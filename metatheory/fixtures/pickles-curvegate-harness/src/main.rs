// PROVE + VERIFY + BIND the LEAN-SYNTHESIZED kimchi CURVE gates. The gate list (typ/wires/coeffs) and
// the COLUMNS-wide witness grid are emitted by `Dregg2.Circuit.Emit.KimchiRenderCompleteAdd` (and
// siblings for var_base_mul / endo_mul / endo_mul_scalar). This harness reads that JSON, builds the
// pure-Rust kimchi objects, and proves + verifies through the SAME `proof-systems` (tag 0.3.0) front
// door mina-rust uses. House Law #1: the circuit is Lean-authored; proof-systems is the Rust prover.
// No OCaml, no Node, no o1js in this path.
//
// Binding is demonstrated with the gate-satisfaction preflight DISABLED (`disable_gates_checks`), so a
// tamper is rejected by the PROOF (a non-vanishing quotient at `ProverProof::create`), not a debug
// assert. For each circuit we check three things (the R4a-real three-way): the good witness VERIFIES;
// a flip of a CONSTRAINED cell is REJECTED (the gate binds); a flip of an UNCONSTRAINED cell is
// ACCEPTED (the reject is the constraint biting, not a blanket reject — non-vacuity).

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

// ---- the Lean-emitted JSON shape (same as pickles-poseidon-harness) ----

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

// Decimal string -> Fp, reduced mod the field order (handles full ~254-bit values).
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
        _ => panic!("unsupported gate ordinal {o} for the curve-gate rung"),
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

// disable_gates_checks = true: skip the prover's debug preflight so a tampered witness is rejected by
// the PROOF (a non-vanishing quotient), returning Err rather than panicking.
fn index_from_gates(gates: Vec<CircuitGate<Fp>>, public: usize) -> Idx {
    let mut index = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
        gates,
        public,
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

fn index_for(c: &CircuitJson) -> Idx {
    index_from_gates(build_gates(c), c.public_input_size)
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

// A binding spec for one circuit: cells (col,row) whose flip must be REJECTED (constrained), and cells
// whose flip must be ACCEPTED (unconstrained — the non-vacuity control).
struct BindSpec {
    file: &'static str,
    constrained: &'static [(usize, usize)],
    free: &'static [(usize, usize)],
}

const SPECS: &[BindSpec] = &[
    BindSpec {
        file: "complete_add.json",
        // (col,row): x3 @ (4,0) breaks s²=x1+x2+x3; the slope s @ (8,0) breaks the slope constraint.
        constrained: &[(4, 0), (8, 0)],
        // an advice column the complete_add gate never reads (cols 11..14) — globally unconstrained.
        free: &[(11, 0)],
    },
    BindSpec {
        file: "endo_mul_scalar.json",
        // n8 @ (1,0) breaks the scalar-reconstruction fold; a8 @ (4,0) breaks the a-fold; crumb x0
        // @ (6,0) breaks both the n8 fold and the crumb-range (unless it stays in {0,1,2,3}).
        constrained: &[(1, 0), (4, 0), (6, 0)],
        // w14 is unused by the EndoMulScalar gate — globally unconstrained.
        free: &[(14, 0)],
    },
    BindSpec {
        file: "var_base_mul.json",
        // n' @ (5,0) breaks the bit-decomposition; slope s0 @ (7,1) breaks bit 0's slope constraint;
        // x5 @ (0,1) breaks the last bit's output constraint.
        constrained: &[(5, 0), (7, 1), (0, 1)],
        // Next w12 is unread by the VarBaseMul gate (Next reads only w0..w11) — unconstrained.
        free: &[(12, 1)],
    },
    BindSpec {
        file: "endo_mul.json",
        // s1 @ (9,0) breaks constraint 5; xr @ (7,0) breaks constraints 6-8; xs @ (4,1) breaks
        // constraint 10. (Proof-systems 0.3.0 EndoMul = 11 constraints; it does not read Curr w2.)
        constrained: &[(9, 0), (7, 0), (4, 1)],
        // Next w7 (the tail Zero row beyond w6) is unread by the EndoMul gate — unconstrained.
        free: &[(7, 1)],
    },
];

fn run_spec(spec: &BindSpec, verbose: bool) {
    let circuit = load_circuit(&fixtures_dir(), spec.file);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let index = index_for(&circuit);
    let public: Vec<Fp> = vec![Fp::from(0u64); 0];
    if verbose {
        println!(
            "-- {} : {} gates, {} rows, {} public --",
            circuit.name,
            circuit.gates.len(),
            circuit.num_rows,
            circuit.public_input_size
        );
    }

    // (1) good witness VERIFIES.
    let t = Instant::now();
    prove_and_verify(&index, &gm, build_witness(&circuit), &public)
        .unwrap_or_else(|e| panic!("[FATAL] good witness for {} REJECTED: {e}", spec.file));
    if verbose {
        println!(
            "[MILESTONE] verify() == true on the Lean-synthesized {} circuit (MEASURED {:?})",
            circuit.name,
            t.elapsed()
        );
    }

    // (2) CONSTRAINED cell flips are REJECTED.
    for &(col, row) in spec.constrained {
        let mut w = build_witness(&circuit);
        w[col][row] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &public).is_err(),
            "[FALSIFICATION] flip of constrained cell ({col},{row}) ACCEPTED — the gate is inert"
        );
        if verbose {
            println!("[bind ] constrained cell ({col},{row}) flip REJECTED");
        }
    }

    // (3) UNCONSTRAINED cell flips are ACCEPTED (non-vacuity).
    for &(col, row) in spec.free {
        let mut w = build_witness(&circuit);
        w[col][row] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &public).is_ok(),
            "[FALSIFICATION] flip of unconstrained cell ({col},{row}) REJECTED — non-vacuity unproven"
        );
        if verbose {
            println!("[ctrl ] unconstrained cell ({col},{row}) flip ACCEPTED");
        }
    }
}

fn main() {
    println!(
        "== curve-gate harness: LEAN-SYNTHESIZED kimchi curve gates -> pure-Rust prove+verify =="
    );
    for spec in SPECS {
        run_spec(spec, true);
        println!();
    }
    println!(
        "== VERDICT: every Lean-synthesized curve-gate circuit produced a kimchi proof its own"
    );
    println!("   verifier ACCEPTED; a constrained-cell tamper was REJECTED; an unconstrained-cell");
    println!("   flip was ACCEPTED. The gate constraints BIND and are NON-VACUOUS. ==");
}

// =====================================================================================
// Committed CI gate. `cargo test --manifest-path .../pickles-curvegate-harness/Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod complete_add_tests {
    use super::*;

    fn setup() -> (CircuitJson, Idx, <Vesta as CommitmentCurve>::Map) {
        let circuit = load_circuit(&fixtures_dir(), "complete_add.json");
        let index = index_for(&circuit);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        (circuit, index, gm)
    }

    // ACCEPT: the Lean-synthesized complete_add circuit's good witness proves + verifies. verify()==true
    // means proof-systems' own CompleteAdd gate accepted the row, i.e. (x3,y3) = G + [2]G = [3]G by the
    // gate's EC-addition law (the Lean side independently pins output == PastaCurve.Gp3).
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        prove_and_verify(&index, &gm, build_witness(&circuit), &[])
            .expect("the Lean-synthesized complete_add witness must verify() == true");
    }

    // BIND polarity 1 — flip x3 (col 4, row 0): breaks s² = x1 + x2 + x3 -> REJECTED.
    #[test]
    fn x3_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[4][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "x3 tamper ACCEPTED — the complete_add gate is inert"
        );
    }

    // BIND polarity 2 — flip the slope s (col 8, row 0): breaks the slope/x3 constraints -> REJECTED.
    #[test]
    fn slope_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[8][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "slope tamper ACCEPTED — the complete_add gate is inert"
        );
    }

    // CONTROL: flip an UNCONSTRAINED advice cell the gate never reads (col 11, row 0) -> ACCEPTED, so
    // the two rejections above are the gate constraints biting, not a blanket rejection.
    #[test]
    fn unconstrained_flip_accepted() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[11][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "flip of an unconstrained cell was REJECTED — the tamper rejections may be vacuous"
        );
    }
}

#[cfg(test)]
mod endo_mul_scalar_tests {
    use super::*;

    fn setup() -> (CircuitJson, Idx, <Vesta as CommitmentCurve>::Map) {
        let circuit = load_circuit(&fixtures_dir(), "endo_mul_scalar.json");
        let index = index_for(&circuit);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        (circuit, index, gm)
    }

    // ACCEPT: the Lean-synthesized endo_mul_scalar circuit's good witness proves + verifies. verify()
    // == true means proof-systems' own EndoMulScalar gate accepted the row — the three folds (n8, a8,
    // b8) and the eight crumb-range checks all hold, i.e. the Lean witness reconstructs the scalar and
    // the c/d crumb tables match the constraint's polynomial forms.
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        prove_and_verify(&index, &gm, build_witness(&circuit), &[])
            .expect("the Lean-synthesized endo_mul_scalar witness must verify() == true");
    }

    // BIND 1 — flip n8 (col 1): breaks the scalar-reconstruction fold n8 = Σ 4·acc + x -> REJECTED.
    #[test]
    fn n8_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[1][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "n8 tamper ACCEPTED — the endo_mul_scalar fold is inert"
        );
    }

    // BIND 2 — flip a8 (col 4): breaks the a-fold a8 = Σ 2·acc + c(x) -> REJECTED.
    #[test]
    fn a8_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[4][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "a8 tamper ACCEPTED — the endo_mul_scalar fold is inert"
        );
    }

    // BIND 3 — flip crumb x0 (col 6): breaks the n8 fold AND the crumb-range check -> REJECTED.
    #[test]
    fn crumb_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[6][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "crumb tamper ACCEPTED — the endo_mul_scalar crumb constraints are inert"
        );
    }

    // CONTROL: flip w14 (unused by the EndoMulScalar gate) -> ACCEPTED (non-vacuity).
    #[test]
    fn unconstrained_flip_accepted() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[14][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "flip of an unconstrained cell was REJECTED — the tamper rejections may be vacuous"
        );
    }
}

#[cfg(test)]
mod var_base_mul_tests {
    use super::*;

    fn setup() -> (CircuitJson, Idx, <Vesta as CommitmentCurve>::Map) {
        let circuit = load_circuit(&fixtures_dir(), "var_base_mul.json");
        let index = index_for(&circuit);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        (circuit, index, gm)
    }

    // ACCEPT: the Lean-synthesized var_base_mul circuit's good witness proves + verifies. verify() ==
    // true means proof-systems' own VarBaseMul gate accepted the two rows — the 5-bit decomposition,
    // per-bit booleanity, slope and output constraints (21 total) all hold.
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        prove_and_verify(&index, &gm, build_witness(&circuit), &[])
            .expect("the Lean-synthesized var_base_mul witness must verify() == true");
    }

    // BIND 1 — flip n' (col 5, row 0): breaks the bit-decomposition constraint -> REJECTED.
    #[test]
    fn nprime_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[5][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "n' tamper ACCEPTED — gate inert"
        );
    }

    // BIND 2 — flip slope s0 (col 7, row 1): breaks bit 0's slope constraint -> REJECTED.
    #[test]
    fn slope_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[7][1] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "slope tamper ACCEPTED — gate inert"
        );
    }

    // BIND 3 — flip x5 (col 0, row 1): breaks the last bit's output constraint -> REJECTED.
    #[test]
    fn output_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[0][1] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "x5 tamper ACCEPTED — gate inert"
        );
    }

    // CONTROL: flip Next w12 (unread by VarBaseMul) -> ACCEPTED (non-vacuity).
    #[test]
    fn unconstrained_flip_accepted() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[12][1] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "flip of an unconstrained cell was REJECTED — the tamper rejections may be vacuous"
        );
    }
}

#[cfg(test)]
mod endo_mul_tests {
    use super::*;

    fn setup() -> (CircuitJson, Idx, <Vesta as CommitmentCurve>::Map) {
        let circuit = load_circuit(&fixtures_dir(), "endo_mul.json");
        let index = index_for(&circuit);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        (circuit, index, gm)
    }

    // ACCEPT: the Lean-synthesized endo_mul circuit's good witness proves + verifies. verify() == true
    // means proof-systems' own EndoMul gate (0.3.0, 11 constraints) accepted the two rows — the
    // endo-selected base, the two slopes/outputs, booleanity, and the n-decomposition all hold.
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        prove_and_verify(&index, &gm, build_witness(&circuit), &[])
            .expect("the Lean-synthesized endo_mul witness must verify() == true");
    }

    // BIND 1 — flip s1 (col 9, row 0): breaks the first slope constraint -> REJECTED.
    #[test]
    fn s1_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[9][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "s1 tamper ACCEPTED — gate inert"
        );
    }

    // BIND 2 — flip xr (col 7, row 0): breaks the intermediate-point constraints -> REJECTED.
    #[test]
    fn xr_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[7][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "xr tamper ACCEPTED — gate inert"
        );
    }

    // BIND 3 — flip xs (col 4, row 1): breaks the output constraint -> REJECTED.
    #[test]
    fn xs_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[4][1] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "xs tamper ACCEPTED — gate inert"
        );
    }

    // CONTROL: flip Next w7 (the tail Zero row, unread by EndoMul) -> ACCEPTED (non-vacuity).
    #[test]
    fn unconstrained_flip_accepted() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[7][1] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "flip of an unconstrained cell was REJECTED — the tamper rejections may be vacuous"
        );
    }
}
