// PROVE the FIRST MULTI-GATE COMPOSITION with a CROSS-GATE COPY WIRE.
//
// The circuit (Lean-authored by `Dregg2.Circuit.Emit.KimchiComposeMSM`) is a 2-step MSM accumulation:
// a `var_base_mul` gate (rows 0-1) produces an output point `[n]·T = (x5,y5)` at its Next row cols 0,1,
// and a `complete_add` gate (row 2) consumes that SAME point as its first input `(x1,y1)` — the
// accumulator update `acc ← acc + [n]·T`, the literal heart of the in-circuit MSM the kimchi verifier
// runs. The var_base_mul output cell and the complete_add input cell are placed into ONE σ (copy-
// permutation) equivalence class, so the wiring forces them equal. That wire is what NO single-gate
// circuit ever tested.
//
// This harness reads the Lean-emitted JSON, builds the pure-Rust kimchi objects, and proves + verifies
// through the SAME `proof-systems` (tag 0.3.0) front door mina-rust uses. House Law #1: the circuit is
// Lean-authored; proof-systems is the Rust prover. No OCaml, no Node, no o1js.
//
// The shared output point is ALSO materialized in the circuit's trailing Zero row (row 3, cols 0,1) and
// placed into the SAME class. The Zero gate reads nothing and no other gate reads row 3, so cell
// (col 0, row 3) is constrained by σ AND BY NOTHING ELSE. That is the clean probe:
//   (1) HONEST:        the composed circuit's good witness verify()==true.
//   (2) WIRING BINDS:  flip (col 0, row 3) on the WIRED circuit -> REJECTED. The only thing that reads
//                      (col 0, row 3) is the copy-permutation, so the rejection IS the wiring.
//   (3) NOT-ADJACENCY: the SAME flip on the UNWIRED circuit (row 3 not in the class) -> ACCEPTED. Same
//                      cell, same witness, no wire -> no rejection. So (2) is the WIRE, not adjacency.
//   (4) NON-VACUITY:   flip an unread advice cell (col 11, row 3) on the WIRED circuit -> ACCEPTED.
// Supporting (contaminated — gate AND wire both fire): flipping the real MSM wire cells (complete_add
// input (col 0, row 2) or var_base_mul output (col 0, row 1)) is REJECTED, but by a gate too.
//
// disable_gates_checks=true: a σ desync is rejected by the PROOF (the permutation argument), returning
// Err, not by a debug assert.

use std::path::PathBuf;
use std::time::Instant;

use mina_curves::pasta::Fp;

// ⚑ THE ONE DRIVER. `build_gates` / `build_witness` / `index_for` / `prove_and_verify` were
// open-coded in TEN of these harnesses — not ten transcriptions of one reader but ten readers that
// DISAGREED. `pickles-circuit-driver/src/lib.rs` carries the measured list: an `i128` parser that
// cannot hold a round constant, an `F::from_str` that SILENTLY REDUCES a coefficient authored over
// the other pasta prime, a gate table stopping at ordinal 3, two SRS constructions, two preflight
// settings, and two serde shapes with no `public_input` field at all. The bodies below are
// one-liners into the shared reader; the names stay, so everything about THIS rung is untouched.
use pickles_circuit_driver::{
    kimchi::circuits::gate::CircuitGate, kimchi::circuits::wires::COLUMNS, load, load_in, step,
    CircuitJson, IndexOpts,
};

fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

/// A decimal literal as a field element. ⚠ NOT `Fp::from_str`: ark-ff implements that as
/// `BigInt::from_str(s) % MODULUS`, so a coefficient authored over the OTHER pasta prime becomes a
/// well-formed element of this one with no error anywhere. The shared reader REFUSES a
/// non-canonical literal instead.
#[allow(dead_code)]
fn parse_f(s: &str) -> Fp {
    pickles_circuit_driver::parse_field::<Fp>(s)
}

#[allow(dead_code)]
fn load_path(path: &std::path::Path) -> CircuitJson {
    load(path)
}

#[allow(dead_code)]
fn load_circuit(dir: &std::path::Path, name: &str) -> CircuitJson {
    load_in(dir, name)
}

#[allow(dead_code)]
fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fp>> {
    step::gates(c)
}

#[allow(dead_code)]
fn build_witness(c: &CircuitJson) -> [Vec<Fp>; COLUMNS] {
    step::witness(c)
}

#[allow(dead_code)]
fn build_public(c: &CircuitJson) -> Vec<Fp> {
    step::public(c)
}

#[allow(dead_code)]
fn public_of(c: &CircuitJson) -> Vec<Fp> {
    step::public(c)
}

/// ⚑ This rung's index options, unchanged from before the collapse: kimchi's serialized TEST srs and
/// `disable_gates_checks` — the prover's debug preflight is SKIPPED so a tampered witness (gate OR
/// permutation) is rejected by the PROOF, returning `Err` rather than panicking.
#[allow(dead_code)]
fn index_from_gates(gates: Vec<CircuitGate<Fp>>, public: usize) -> step::Index {
    step::index_from_gates(gates, IndexOpts::test(public))
}

#[allow(dead_code)]
fn index_for(c: &CircuitJson) -> step::Index {
    step::index_for(c, IndexOpts::test(c.public_input_size))
}

#[allow(dead_code)]
fn prove_and_verify(
    index: &step::Index,
    group_map: &step::Map,
    witness: [Vec<Fp>; COLUMNS],
    public_input: &[Fp],
) -> Result<(), String> {
    step::prove_and_verify(index, group_map, witness, public_input)
}

// A flip of witness cell (col,row) by +1, returning a fresh tampered witness.
fn tamper(c: &CircuitJson, col: usize, row: usize) -> [Vec<Fp>; COLUMNS] {
    let mut w = build_witness(c);
    w[col][row] += Fp::from(1u64);
    w
}

fn main() {
    println!(
        "== compose harness: LEAN-SYNTHESIZED 2-gate MSM step (var_base_mul -> complete_add) =="
    );
    let dir = fixtures_dir();
    let gm = step::group_map();
    let public: Vec<Fp> = vec![];

    let wired = load_circuit(&dir, "compose_msm.json");
    let unwired = load_circuit(&dir, "compose_msm_unwired.json");
    let iw = index_for(&wired);
    let iu = index_for(&unwired);
    println!(
        "-- {} : {} gates typ {:?}, {} rows --",
        wired.name,
        wired.gates.len(),
        wired.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
        wired.num_rows
    );

    // (1) HONEST: the composed circuit verifies.
    let t = Instant::now();
    prove_and_verify(&iw, &gm, build_witness(&wired), &public)
        .unwrap_or_else(|e| panic!("[FATAL] honest composed witness REJECTED: {e}"));
    println!("[1 HONEST   ] verify()==true on the composed var_base_mul->complete_add circuit (MEASURED {:?})", t.elapsed());

    // (2) WIRING BINDS: desync the shared output point in the trailing Zero row (col 0, row 3).
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 0, 3), &public).is_err(),
        "[FALSIFICATION] shared-wire desync (col 0,row 3) ACCEPTED on the WIRED circuit — σ is inert"
    );
    println!("[2 WIRE BIND] shared-wire desync (col 0,row 3) REJECTED by the copy-permutation");
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 1, 3), &public).is_err(),
        "[FALSIFICATION] shared-wire desync (col 1,row 3) ACCEPTED on the WIRED circuit — σ is inert"
    );
    println!("[2 WIRE BIND] shared-wire desync (col 1,row 3, the y twin) REJECTED by σ");

    // (3) NOT-ADJACENCY control: the SAME flip on the UNWIRED circuit is ACCEPTED.
    prove_and_verify(&iu, &gm, build_witness(&unwired), &public)
        .unwrap_or_else(|e| panic!("[FATAL] honest UNWIRED witness REJECTED: {e}"));
    assert!(
        prove_and_verify(&iu, &gm, tamper(&unwired, 0, 3), &public).is_ok(),
        "[FALSIFICATION] (col 0,row 3) flip REJECTED on the UNWIRED circuit — the (2) reject was not the wire"
    );
    println!("[3 CONTROL  ] SAME (col 0,row 3) flip ACCEPTED on the UNWIRED circuit -> (2) is the WIRE, not adjacency");

    // (4) NON-VACUITY: an unread advice cell flip is ACCEPTED.
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 11, 3), &public).is_ok(),
        "[FALSIFICATION] unread cell (col 11,row 3) flip REJECTED — the wired rejections may be vacuous"
    );
    println!("[4 NONVACU  ] unread advice cell (col 11,row 3) flip ACCEPTED (non-vacuity)");

    // Supporting: the REAL MSM wire cells reject too (contaminated — gate AND wire both fire).
    assert!(prove_and_verify(&iw, &gm, tamper(&wired, 0, 2), &public).is_err());
    assert!(prove_and_verify(&iw, &gm, tamper(&wired, 0, 1), &public).is_err());
    println!("[+ REALWIRE ] complete_add input (col 0,row 2) and var_base_mul output (col 0,row 1) desync REJECTED (gate+σ)");

    println!(
        "== VERDICT: the byte-exact single-gate emitters COMPOSE into a multi-gate circuit a pure-"
    );
    println!(
        "   Rust kimchi prover ACCEPTS; the cross-gate copy-permutation GENUINELY BINDS (a shared-"
    );
    println!("   wire desync is rejected by σ, accepted when unwired); non-vacuity holds. ==");
}

// =====================================================================================
// Committed CI gate. `cargo test --manifest-path .../pickles-compose-harness/Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod compose_tests {
    use super::*;

    fn setup() -> (
        CircuitJson,
        CircuitJson,
        step::Index,
        step::Index,
        step::Map,
    ) {
        let dir = fixtures_dir();
        let wired = load_circuit(&dir, "compose_msm.json");
        let unwired = load_circuit(&dir, "compose_msm_unwired.json");
        let iw = index_for(&wired);
        let iu = index_for(&unwired);
        let gm = step::group_map();
        (wired, unwired, iw, iu, gm)
    }

    // (1) HONEST: the composed var_base_mul->complete_add circuit's good witness proves + verifies.
    // verify()==true means proof-systems accepted BOTH gates AND the cross-gate copy-permutation: the
    // var_base_mul output point is genuinely carried into the complete_add input by σ.
    #[test]
    fn honest_composition_verifies() {
        let (wired, _u, iw, _iu, gm) = setup();
        prove_and_verify(&iw, &gm, build_witness(&wired), &[])
            .expect("the composed 2-gate MSM circuit must verify() == true");
    }

    // (2) WIRING BINDS: desync the shared output point in the trailing Zero row (col 0, row 3). That
    // cell is read by NO gate (Zero row; no other gate reads row 3) and sits in σ's cycle with the real
    // MSM wire, so its rejection is the COPY-PERMUTATION, full stop.
    #[test]
    fn shared_wire_desync_rejected_x() {
        let (wired, _u, iw, _iu, gm) = setup();
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, 3), &[]).is_err(),
            "shared-wire x desync ACCEPTED on the WIRED circuit — the copy-permutation is inert"
        );
    }

    #[test]
    fn shared_wire_desync_rejected_y() {
        let (wired, _u, iw, _iu, gm) = setup();
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 1, 3), &[]).is_err(),
            "shared-wire y desync ACCEPTED on the WIRED circuit — the copy-permutation is inert"
        );
    }

    // (3) NOT-ADJACENCY control: the UNWIRED circuit's honest witness verifies, and the SAME
    // (col 0, row 3) flip is ACCEPTED there — proving the (2) rejection is the WIRE, not the gate or a
    // blanket reject. (Same witness cell; the only difference is whether row 3 is in the σ class.)
    #[test]
    fn unwired_honest_verifies() {
        let (_w, unwired, _iw, iu, gm) = setup();
        prove_and_verify(&iu, &gm, build_witness(&unwired), &[])
            .expect("the UNWIRED control circuit's honest witness must verify() == true");
    }

    #[test]
    fn unwired_desync_accepted() {
        let (_w, unwired, _iw, iu, gm) = setup();
        assert!(
            prove_and_verify(&iu, &gm, tamper(&unwired, 0, 3), &[]).is_ok(),
            "(col 0,row 3) flip REJECTED on the UNWIRED circuit — the shared-wire reject was not the wire"
        );
    }

    // (4) NON-VACUITY: an advice cell no gate reads and no cycle contains (col 11, row 3) -> ACCEPTED,
    // so the wired rejections are the copy-permutation biting, not a blanket rejection.
    #[test]
    fn nonvacuity_unread_cell_accepted() {
        let (wired, _u, iw, _iu, gm) = setup();
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 11, 3), &[]).is_ok(),
            "unread advice cell (col 11,row 3) flip REJECTED — the wired rejections may be vacuous"
        );
    }

    // Supporting: the REAL MSM wire cells (complete_add input; var_base_mul output) reject on desync —
    // but by a gate constraint AS WELL AS σ, so they cannot isolate the wiring the way (2)/(3) do.
    #[test]
    fn real_wire_cells_reject() {
        let (wired, _u, iw, _iu, gm) = setup();
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, 2), &[]).is_err(),
            "complete_add input (col 0,row 2) desync ACCEPTED"
        );
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, 1), &[]).is_err(),
            "var_base_mul output (col 0,row 1) desync ACCEPTED"
        );
    }
}
