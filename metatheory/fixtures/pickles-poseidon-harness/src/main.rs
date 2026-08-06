// R4a-scaled: PROVE + VERIFY a LEAN-SYNTHESIZED **Poseidon** kimchi circuit, and confirm it BINDS
// (both tamper polarities rejected). The gate list (11 byte-exact `Poseidon` rows + a `Zero` gate)
// and the witness (the 55 intermediate Poseidon round states) are emitted by
// `Dregg2.Circuit.Emit.KimchiRenderPoseidon` (Lean) — the coefficients are `poseidonRowCoeffs`
// (the 165 round constants that byte-match o1js), the witness is computed by dregg's own
// `PastaPoseidon.Ref.permFrom`, and the placement is `KimchiPlacement.place`. This harness only reads
// that JSON, builds the pure-Rust kimchi objects, and runs the prover/verifier through the SAME
// `proof-systems` (tag 0.3.0) front door mina-rust uses. House Law #1: the circuit is Lean-authored;
// proof-systems is the Rust prover. No OCaml, no Node, no o1js in this path.
//
// The milestone: `verify() == true` on the Lean-synthesized Poseidon circuit, whose output lane 0
// equals the o1js `Poseidon.hash([1])` gold value (= dregg's `Ref.hash [1]`) — so the byte-exact
// round-constant coefficients are shown to CONSTRAIN a real proof AND to compute the right hash, not
// merely to match a byte-diff.
//
// Binding is demonstrated with the gate-satisfaction preflight DISABLED (`disable_gates_checks`), so
// a tamper is rejected by the PROOF (a non-vanishing quotient at `ProverProof::create`), not by a
// debug assertion. Two polarities:
//   * witness tamper — flip one intermediate round-state limb -> the Poseidon round constraint bites.
//   * coeff  tamper — flip one of the 165 round constants -> the good witness no longer satisfies it.

use std::path::PathBuf;
use std::time::Instant;

use pickles_circuit_driver::{
    load_in,
    step::{self, F},
    CircuitJson, IndexOpts,
};

// The o1js `Poseidon.hash([1])` gold value (= dregg `PastaPoseidon.Ref.hash [1]`), which is the
// permutation output lane 0 (witness col 0, row 11). Pinned in Lean `KimchiRenderPoseidon` too.
const GOLD_HASH1: &str =
    "7555220006856562833147743033256142154591945963958408607501861037584894828141";

fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

/// ⚑ This rung's index options, unchanged from before the collapse: kimchi's serialized TEST srs,
/// and the prover's gate-satisfaction PREFLIGHT DISABLED so a tampered witness is rejected by the
/// PROOF (a non-vanishing quotient) rather than by a debug assert. The cryptographic constraints are
/// unaffected by that flag.
fn opts(public: usize) -> IndexOpts {
    IndexOpts::test(public)
}

/// A decimal field element through the SHARED reader — arbitrary precision, sign-aware, and it
/// REFUSES a literal that is not canonical for Fp instead of reducing it. ⚠ This harness's own
/// `parse_fp` used `Fp::from_str`, whose ark-ff implementation is `% MODULUS`: it would have taken a
/// wrap-side Fq coefficient silently.
fn step_field(s: &str) -> F {
    pickles_circuit_driver::parse_field::<F>(s)
}

fn index_from_gates(
    gates: Vec<pickles_circuit_driver::kimchi::circuits::gate::CircuitGate<F>>,
    public: usize,
) -> step::Index {
    step::index_from_gates(gates, opts(public))
}

fn index_for(c: &CircuitJson) -> step::Index {
    step::index_for(c, opts(c.public_input_size))
}

fn main() {
    let dir = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(fixtures_dir);

    println!("== R4a-scaled: LEAN-SYNTHESIZED **Poseidon** kimchi circuit -> pure-Rust prove + verify ==");
    println!("   fixtures dir: {}", dir.display());
    println!();

    // --- 1. load the Lean-synthesized Poseidon circuit ---
    let circuit = load_in(&dir, "poseidon.json");
    println!(
        "-- Poseidon circuit '{}' from Lean: {} gates, {} rows, {} public inputs --",
        circuit.name,
        circuit.gates.len(),
        circuit.num_rows,
        circuit.public_input_size
    );
    let poseidon_rows = circuit.gates.iter().filter(|g| g.typ == 2).count();
    let total_coeffs: usize = circuit.gates.iter().map(|g| g.coeffs.len()).sum();
    println!(
        "   {poseidon_rows} Poseidon gate rows carrying {total_coeffs} round-constant coefficients"
    );

    // output = the permutation result lane 0 (witness col 0, row 11) — must equal the o1js gold.
    let output_hash = &circuit.witness[0][circuit.num_rows - 1];
    let gold_ok = step_field(output_hash) == step_field(GOLD_HASH1);
    println!(
        "   circuit output lane0 = {}\n   o1js Poseidon.hash([1]) gold match: {}",
        output_hash,
        if gold_ok { "YES" } else { "NO (!!)" }
    );
    assert!(gold_ok, "output lane0 != o1js Poseidon.hash([1]) gold");
    println!();

    let public_input: Vec<F> = step::public(&circuit);
    let index = index_for(&circuit);
    let group_map = step::group_map();
    println!("   built ProverIndex from the Lean gate list");

    // --- 2. PROVE + VERIFY the Lean witness ---
    let good = step::witness(&circuit);
    let t = Instant::now();
    match step::prove_and_verify(&index, &group_map, good, &public_input) {
        Ok(()) => println!(
            "[MILESTONE] verify() == true on the Lean-synthesized Poseidon circuit (MEASURED {:?})",
            t.elapsed()
        ),
        Err(e) => panic!("[FATAL] good Poseidon witness was REJECTED ({e}) -- the render is wrong"),
    }
    println!();

    // --- 3. BOTH POLARITIES: it must BIND ---
    println!(
        "-- binding checks (a tamper must be REJECTED by the proof, else a constraint is inert) --"
    );

    // (3a) WITNESS tamper: flip one intermediate round-state limb (col 6 = state s(1) lane 0, row 0).
    let mut w_state = step::witness(&circuit);
    w_state[6][0] += F::from(1u64);
    match step::prove_and_verify(&index, &group_map, w_state, &public_input) {
        Err(e) => println!(
            "[bind:witness] round-state tamper s(1)[0]+1 REJECTED at [{}]",
            e.split(':').next().unwrap_or("?")
        ),
        Ok(()) => panic!(
            "[FALSIFICATION] round-state tamper ACCEPTED -- the Poseidon constraint is inert"
        ),
    }

    // (3b) COEFF tamper: flip one of the 165 round constants (gate 0 = Poseidon row 0, coeff 0).
    // Prove the ORIGINAL good witness against the tampered circuit -> it no longer satisfies it.
    let mut tampered_gates = step::gates(&circuit);
    tampered_gates[0].coeffs[0] += F::from(1u64);
    let tampered_index = index_from_gates(tampered_gates, circuit.public_input_size);
    match step::prove_and_verify(
        &tampered_index,
        &group_map,
        step::witness(&circuit),
        &public_input,
    ) {
        Err(e) => println!(
            "[bind:coeff  ] round-constant tamper rc[0][0]+1 REJECTED at [{}]",
            e.split(':').next().unwrap_or("?")
        ),
        Ok(()) => panic!(
            "[FALSIFICATION] round-constant tamper ACCEPTED -- the byte-exact coeff is inert"
        ),
    }

    // (3c) CONTROL: flipping an UNCONSTRAINED cell (row 11 = the Zero gate, col 5 — not read by any
    // constraint and identity-self-wired) must be ACCEPTED. This proves the two rejections above are
    // the Poseidon/round constraints biting, not a blanket "any witness change is rejected".
    let mut w_free = step::witness(&circuit);
    w_free[5][circuit.num_rows - 1] += F::from(1u64);
    match step::prove_and_verify(&index, &group_map, w_free, &public_input) {
        Ok(()) => println!(
            "[control     ] flip of unconstrained cell (Zero row, col 5) ACCEPTED -> the reject above is the CONSTRAINT"
        ),
        Err(e) => panic!("[control] unconstrained-cell flip REJECTED ({e}) -- non-vacuity unproven"),
    }

    println!();
    println!(
        "== VERDICT: a LEAN-SYNTHESIZED Poseidon-permutation circuit produced a kimchi proof its"
    );
    println!(
        "   own verifier ACCEPTED; its output is the o1js Poseidon.hash([1]) gold; and BOTH a"
    );
    println!("   round-state witness tamper and a round-constant coeff tamper were REJECTED. ==");
}

// =====================================================================================
// The committed CI gate: each `#[test]` reads the committed Lean-emitted fixture and asserts
// ONE property. `cargo test --manifest-path metatheory/fixtures/pickles-poseidon-harness/Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod poseidon_r4 {
    use super::*;

    fn setup() -> (CircuitJson, step::Index, step::Map) {
        let circuit = load_in(&fixtures_dir(), "poseidon.json");
        let index = index_for(&circuit);
        let group_map = step::group_map();
        (circuit, index, group_map)
    }

    // ACCEPT: the Lean-synthesized Poseidon circuit's good witness proves + verifies.
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        step::prove_and_verify(&index, &gm, step::witness(&circuit), &[])
            .expect("the Lean-synthesized Poseidon witness must verify() == true");
    }

    // OUTPUT: the permutation output lane 0 is the o1js Poseidon.hash([1]) gold (= dregg Ref.hash [1]).
    #[test]
    fn output_matches_o1js_gold() {
        let circuit = load_in(&fixtures_dir(), "poseidon.json");
        let out = step_field(&circuit.witness[0][circuit.num_rows - 1]);
        assert_eq!(
            out,
            step_field(GOLD_HASH1),
            "output lane0 != o1js Poseidon.hash([1]) gold"
        );
    }

    // BIND polarity 1 — a flipped intermediate round-state limb is REJECTED (the Poseidon
    // round constraint bites). Rejection comes from the proof (gate preflight disabled).
    #[test]
    fn witness_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = step::witness(&circuit);
        w[6][0] += F::from(1u64);
        assert!(
            step::prove_and_verify(&index, &gm, w, &[]).is_err(),
            "round-state tamper (s(1)[0]+1) was ACCEPTED -- the Poseidon constraint is inert"
        );
    }

    // CONTROL: a flip of an UNCONSTRAINED cell (Zero-gate row 11, col 5) is ACCEPTED, so the two
    // tamper rejections are the constraints biting, not a blanket rejection of any witness change.
    #[test]
    fn unconstrained_flip_accepted() {
        let (circuit, index, gm) = setup();
        let mut w = step::witness(&circuit);
        w[5][circuit.num_rows - 1] += F::from(1u64);
        assert!(
            step::prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "flip of an unconstrained cell was REJECTED -- the tamper rejections may be vacuous"
        );
    }

    // BIND polarity 2 — a flipped round constant (one of the 165 byte-exact coeffs) makes the good
    // witness fail to satisfy the circuit -> REJECTED. This is the coeff actually CONSTRAINING.
    #[test]
    fn coeff_tamper_rejected() {
        let circuit = load_in(&fixtures_dir(), "poseidon.json");
        let gm = step::group_map();
        let mut gates = step::gates(&circuit);
        gates[0].coeffs[0] += F::from(1u64);
        let index = index_from_gates(gates, circuit.public_input_size);
        assert!(
            step::prove_and_verify(&index, &gm, step::witness(&circuit), &[]).is_err(),
            "round-constant tamper (rc[0][0]+1) was ACCEPTED -- the byte-exact coeff is inert"
        );
    }
}
