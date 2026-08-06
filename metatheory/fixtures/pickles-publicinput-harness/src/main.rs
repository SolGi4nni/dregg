// PROVE a LEAN-SYNTHESIZED kimchi circuit whose PUBLIC INPUT is non-empty, and show the public input
// BINDS — in both of the two independent ways it can.
//
// ⚑ THE HOLE. Measured 2026-08-01, all nine committed circuit fixtures across the five sibling
// pickles harnesses carry `public_input_size: 0`. `KimchiPlacement.place` (Lean) takes `pubSize` as
// its FIRST argument and has a whole branch for it — the leading `pubSize` Generic rows with
// `coeffs = [1,0,0,0,0]`, the `External i ↦ {i,0}` cells prepended to `circuitPositions`, and the
// `pubSize + gateIndex` row offset of every circuit gate. At `pubSize = 0` all three are identity, so
// not one line of that branch had ever been inside a circuit a prover accepted. `step_main` HAS a
// public input: mina-rust's `ProofConstants` table measures Step at `PRIMARY_LEN = 67`, Wrap at 40.
//
// WHAT kimchi ACTUALLY DOES WITH IT (read at proof-systems tag 0.3.0, not assumed):
//   * `prover.rs:270`  — `let public = witness[0][0..index.cs.public].to_vec();` The prover's public
//     vector IS witness column 0, rows 0..n. The caller never passes it in.
//   * `verifier.rs:816` — `if public_input.len() != verifier_index.public { return Err(...) }` The
//     VERIFIER is handed the vector separately. That gap is the whole point: prover-side and
//     verifier-side public inputs are two different objects, and the proof is what ties them.
//   * `constraints.rs:420-423` — a row `< cs.public` whose `coeffs[0] != 1` is `IncorrectPublic`.
//   * `generic.rs:297-304` — the generic gate's first half is `c₀w₀+c₁w₁+c₂w₂+c₃w₀w₁+c₄ − pᵣ`, so
//     `coeffs = [1,0,0,0,0]` reads exactly `w₀[r] = pᵣ` and constrains nothing else in the row.
//   * kimchi does NOT synthesise the public rows. `place` emits them, and they must be right.
//
// THE CIRCUIT (Lean-authored by `Dregg2.Circuit.Emit.KimchiRenderPublicInput`): three public words
// `p₀ p₁ p₂` and the relation `p₀·p₁ = p₂`.
//     row 0..2  public  Generic [1,0,0,0,0]      w₀ = pᵢ
//     row 3     Mul     Generic [0,0,-1,1,0,…]   t = w₀·w₁      w₀=p₀ w₁=p₁ w₂=t
//     row 4     Eq      Generic [1,-1,0,0,0,…]   w₀ − w₁ = 0    w₀=t  w₁=p₂
// Every public word reaches the circuit ONLY through σ: p₀ ⟨0,0⟩↔⟨3,0⟩, p₁ ⟨1,0⟩↔⟨3,1⟩,
// p₂ ⟨2,0⟩↔⟨4,1⟩, t ⟨3,2⟩↔⟨4,0⟩.
//
// SIX PROPERTIES, and the two REJECT legs are independent:
//   (1) ACCEPT       instance A (5·7=35) and instance B (3·11=33) both verify()==true.
//   (2) PI BINDS     A's honest proof against B's public input -> REJECTED; each single word flipped
//                    on its own -> REJECTED. The proof COMMITS to the claim.
//   (3) PI IS WIRED  flip the public CELL ⟨0,0⟩ *and* tell the verifier the new value, so the public
//                    row's own constraint still holds -> REJECTED by the copy-permutation alone.
//   (4) CONTROL      the same flip on `pi_nowire` (gate 0 reads a fresh `external 3`, so ⟨0,0⟩
//                    self-wires) -> ACCEPTED. So (3) is the placement WIRE, nothing else.
//   (5) NON-VACUITY  flip ⟨0,3⟩ — a cell IN a public row that the public gate does not read and σ
//                    does not wire -> ACCEPTED. A public row constrains column 0 and nothing else.
//   (6) SCALE        `pi_wide`: pubSize = 67 (step_main's measured PRIMARY_LEN), 134 rows, every
//                    public word folded into one accumulator. Accept + word tamper + control.
//
// `disable_gates_checks = true`: a tamper is rejected by the PROOF (the public-input polynomial or
// the permutation argument's z-polynomial), returning Err — not by a debug assert.
//
// House Law #1: the CIRCUIT is Lean-authored; `proof-systems` is the Rust PROVER that RUNS it.
//
// Two entry points over the same logic:
//   * `main()`  — the demo/regeneration driver. Reads the four JSON files from a directory (argv[1],
//     default the committed `fixtures/` dir) and runs the whole sequence with timings. Point it at
//     `/tmp/pickles-publicinput` after `lake env lean --run EmitPublicInputJson.lean` to drive the
//     LIVE Lean render end to end.
//   * `#[test]` fns — the committed CI gate, one property per test.

use std::array;
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

// A flip of witness cell (col,row) by +1.
fn tamper(c: &CircuitJson, col: usize, row: usize) -> [Vec<Fp>; COLUMNS] {
    let mut w = build_witness(c);
    w[col][row] += Fp::from(1u64);
    w
}

// A flip of public word `i` by +1 — the VERIFIER's copy only.
fn tamper_public(c: &CircuitJson, i: usize) -> Vec<Fp> {
    let mut p = build_public(c);
    p[i] += Fp::from(1u64);
    p
}

fn main() {
    let dir = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(fixtures_dir);

    println!("== pickles PUBLIC-INPUT harness: LEAN-SYNTHESIZED circuit, public_input_size > 0 ==");
    println!("   fixtures dir: {}", dir.display());
    println!();

    let gm = step::group_map();

    let a = load_circuit(&dir, "pi_mul_a.json");
    let b = load_circuit(&dir, "pi_mul_b.json");
    let nw = load_circuit(&dir, "pi_nowire.json");
    println!(
        "-- '{}': {} gates, {} rows, {} PUBLIC INPUTS --",
        a.name,
        a.gates.len(),
        a.num_rows,
        a.public_input_size
    );

    let ia = index_for(&a);
    let inw = index_for(&nw);

    // (1) ACCEPT — two instances of the SAME relation.
    let t = Instant::now();
    prove_and_verify(&ia, &gm, build_witness(&a), &build_public(&a))
        .expect("[FATAL] instance A REJECTED — the public-input render is wrong");
    println!(
        "[accept   ] instance A verify() == true (MEASURED {:?})",
        t.elapsed()
    );
    let t = Instant::now();
    prove_and_verify(&ia, &gm, build_witness(&b), &build_public(&b))
        .expect("[FATAL] instance B REJECTED on the same index");
    println!(
        "[accept   ] instance B verify() == true on the SAME index (MEASURED {:?}) -> the circuit \
         is the RELATION, the public input picks the instance",
        t.elapsed()
    );
    println!();

    // (2) PI BINDS — the claim moves, the witness does not.
    println!("-- the PUBLIC INPUT must BIND (the proof commits to the claim) --");
    assert!(
        prove_and_verify(&ia, &gm, build_witness(&a), &build_public(&b)).is_err(),
        "[FALSIFICATION] A's proof was ACCEPTED against B's public input"
    );
    println!("[bind:pi  ] A's honest proof vs B's public input REJECTED");
    for i in 0..a.public_input_size {
        assert!(
            prove_and_verify(&ia, &gm, build_witness(&a), &tamper_public(&a, i)).is_err(),
            "[FALSIFICATION] public word {i} flipped and still ACCEPTED — word {i} is inert"
        );
        println!("[bind:pi  ] public word {i} flipped -> REJECTED");
    }
    println!();

    // (3)+(4) PI IS WIRED, and the control says it is the wire.
    println!("-- the public CELL must be WIRED INTO the circuit (σ), not merely declared --");
    let mut w = build_witness(&a);
    w[0][0] += Fp::from(1u64);
    let p = tamper_public(&a, 0);
    assert!(
        prove_and_verify(&ia, &gm, w, &p).is_err(),
        "[FALSIFICATION] ⟨0,0⟩ flipped WITH a matching public word was ACCEPTED — the public row is \
         satisfied and σ caught nothing, so the public cell reaches no circuit cell"
    );
    println!("[bind:σ   ] ⟨0,0⟩ + matching public word REJECTED (only σ ⟨0,0⟩↦⟨3,0⟩ can see this)");
    let mut w = build_witness(&nw);
    w[0][0] += Fp::from(1u64);
    let p = tamper_public(&nw, 0);
    prove_and_verify(&inw, &gm, w, &p)
        .expect("[control] pi_nowire REJECTED the same flip — ⟨0,0⟩ is not actually unwired there");
    println!("[control  ] the SAME flip on pi_nowire ACCEPTED -> the rejection above IS the wire");
    println!();

    // (5) NON-VACUITY.
    prove_and_verify(&ia, &gm, tamper(&a, 3, 0), &build_public(&a))
        .expect("[FATAL] ⟨0,3⟩ flip REJECTED — a public row constrains more than column 0");
    println!("[nonvac   ] ⟨0,3⟩ (in a public row, unread + unwired) ACCEPTED");
    println!();

    // (6) SCALE — step_main's measured PRIMARY_LEN.
    let wide = load_circuit(&dir, "pi_wide.json");
    println!(
        "-- '{}': {} rows, {} PUBLIC INPUTS (= step_main's measured PRIMARY_LEN) --",
        wide.name, wide.num_rows, wide.public_input_size
    );
    let iw = index_for(&wide);
    let t = Instant::now();
    prove_and_verify(&iw, &gm, build_witness(&wide), &build_public(&wide))
        .expect("[FATAL] pi_wide REJECTED — the public-input path does not hold at step scale");
    println!(
        "[accept   ] pi_wide verify() == true at pubSize = {} (MEASURED {:?})",
        wide.public_input_size,
        t.elapsed()
    );
    let last = wide.public_input_size - 1;
    assert!(
        prove_and_verify(&iw, &gm, build_witness(&wide), &tamper_public(&wide, last)).is_err(),
        "[FALSIFICATION] the LAST public word ({last}) is inert at pubSize {}",
        wide.public_input_size
    );
    println!("[bind:pi  ] pi_wide public word {last} (the last one) flipped -> REJECTED");
    prove_and_verify(&iw, &gm, tamper(&wide, 3, last), &build_public(&wide))
        .expect("[FATAL] pi_wide ⟨last,3⟩ flip REJECTED — non-vacuity control failed at scale");
    println!("[nonvac   ] pi_wide ⟨{last},3⟩ (unread + unwired) ACCEPTED");

    println!();
    println!(
        "== VERDICT: a LEAN-SYNTHESIZED circuit with a NON-EMPTY PUBLIC INPUT produced a kimchi"
    );
    println!("   proof its own verifier ACCEPTED; the public input BINDS both as a commitment and");
    println!("   through the placement wire, at 3 words and at step_main's 67. ==");
}

// =====================================================================================
// The committed CI gate: one `#[test]` per property.
// `cargo test --release --manifest-path metatheory/fixtures/pickles-publicinput-harness/Cargo.toml`
// =====================================================================================
#[cfg(test)]
mod public_input {
    use super::*;

    fn setup(name: &str) -> (CircuitJson, step::Index, step::Map) {
        let c = load_circuit(&fixtures_dir(), name);
        let index = index_for(&c);
        let gm = step::group_map();
        (c, index, gm)
    }

    // SHAPE: the fixture really has a non-empty public input, and its public vector really is the
    // prefix of witness column 0 the prover will read (`prover.rs:270`). If those disagreed, every
    // leg below would be measuring an incoherent fixture rather than the circuit.
    #[test]
    fn fixture_has_public_input_matching_witness_column_0() {
        for name in [
            "pi_mul_a.json",
            "pi_mul_b.json",
            "pi_nowire.json",
            "pi_wide.json",
        ] {
            let c = load_circuit(&fixtures_dir(), name);
            assert!(c.public_input_size > 0, "{name}: public_input_size is 0");
            let w = build_witness(&c);
            let p = build_public(&c);
            for (i, pi) in p.iter().enumerate() {
                assert_eq!(
                    w[0][i], *pi,
                    "{name}: witness[0][{i}] != public_input[{i}] — the prover's public vector and \
                     the verifier's would disagree for a reason that is not the circuit"
                );
            }
        }
        // And the two instances really are different claims, or (2) below is vacuous.
        let a = load_circuit(&fixtures_dir(), "pi_mul_a.json");
        let b = load_circuit(&fixtures_dir(), "pi_mul_b.json");
        assert_ne!(build_public(&a), build_public(&b));
    }

    // (1) ACCEPT: the Lean-synthesized circuit proves + verifies WITH a public input.
    #[test]
    fn instance_a_verifies() {
        let (c, index, gm) = setup("pi_mul_a.json");
        prove_and_verify(&index, &gm, build_witness(&c), &build_public(&c))
            .expect("instance A must verify() == true");
    }

    // (1b) The SAME index accepts a SECOND instance — the circuit is the relation, not a fixture.
    #[test]
    fn instance_b_verifies_on_the_same_index() {
        let (a, index, gm) = setup("pi_mul_a.json");
        let b = load_circuit(&fixtures_dir(), "pi_mul_b.json");
        assert_eq!(a.gates.len(), b.gates.len());
        prove_and_verify(&index, &gm, build_witness(&b), &build_public(&b))
            .expect("instance B must verify() == true on instance A's index");
    }

    // (2) THE PROOF COMMITS TO THE CLAIM: A's honest proof, verified against B's public input.
    #[test]
    fn cross_instance_public_input_rejected() {
        let (a, index, gm) = setup("pi_mul_a.json");
        let b = load_circuit(&fixtures_dir(), "pi_mul_b.json");
        assert!(
            prove_and_verify(&index, &gm, build_witness(&a), &build_public(&b)).is_err(),
            "A's proof was ACCEPTED against B's public input — the public input is not bound"
        );
    }

    // (2b) EVERY word individually. A single inert word would hide behind the cross-instance leg.
    #[test]
    fn every_public_word_tamper_rejected() {
        let (c, index, gm) = setup("pi_mul_a.json");
        for i in 0..c.public_input_size {
            assert!(
                prove_and_verify(&index, &gm, build_witness(&c), &tamper_public(&c, i)).is_err(),
                "public word {i} flipped and the proof still verified — word {i} is inert"
            );
        }
    }

    // (3) THE PUBLIC CELL IS WIRED INTO THE CIRCUIT. Flip ⟨0,0⟩ AND tell the verifier the new value,
    // so the public row's own constraint `w₀[0] = p₀` still holds and the public commitment matches.
    // The ONLY thing left that can see the change is σ's ⟨0,0⟩↦⟨3,0⟩ class.
    #[test]
    fn public_cell_desync_rejected_by_sigma() {
        let (c, index, gm) = setup("pi_mul_a.json");
        let mut w = build_witness(&c);
        w[0][0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&index, &gm, w, &tamper_public(&c, 0)).is_err(),
            "⟨0,0⟩ flipped WITH a matching public word was ACCEPTED — the public row is satisfied \
             and σ caught nothing, so `place` did not wire the public cell into the circuit"
        );
    }

    // (4) CONTROL: the SAME flip on the circuit whose only difference is that ⟨0,0⟩ self-wires.
    // ACCEPTED -> (3)'s rejection is the placement wire and not adjacency, the gate, or the public
    // commitment.
    #[test]
    fn nowire_control_accepts_the_same_flip() {
        let (c, index, gm) = setup("pi_nowire.json");
        // the control's honest witness verifies at all
        prove_and_verify(&index, &gm, build_witness(&c), &build_public(&c))
            .expect("pi_nowire good witness must verify");
        let mut w = build_witness(&c);
        w[0][0] += Fp::from(1u64);
        prove_and_verify(&index, &gm, w, &tamper_public(&c, 0)).expect(
            "pi_nowire REJECTED the ⟨0,0⟩ flip — ⟨0,0⟩ is NOT actually unwired there, so \
             public_cell_desync_rejected_by_sigma is unproven",
        );
    }

    // (5) NON-VACUITY: a public row constrains column 0 and NOTHING else. ⟨0,3⟩ is in a public row,
    // is not read by the `[1,0,0,0,0]` gate, and is in no σ class -> flipping it must be ACCEPTED.
    // If this reddened, the harness would be rejecting everything and every leg above would be free.
    #[test]
    fn unconstrained_cell_in_a_public_row_accepted() {
        let (c, index, gm) = setup("pi_mul_a.json");
        prove_and_verify(&index, &gm, tamper(&c, 3, 0), &build_public(&c)).expect(
            "flipping ⟨0,3⟩ was REJECTED — a public row is constraining more than column 0, or the \
             harness rejects everything",
        );
    }

    // (6) SCALE: step_main's measured PRIMARY_LEN = 67, 134 rows.
    #[test]
    fn wide_step_scale_verifies() {
        let (c, index, gm) = setup("pi_wide.json");
        assert_eq!(
            c.public_input_size, 67,
            "pi_wide must sit at step_main's measured PRIMARY_LEN (mina-rust ProofConstants)"
        );
        assert_eq!(c.num_rows, 134);
        prove_and_verify(&index, &gm, build_witness(&c), &build_public(&c))
            .expect("pi_wide must verify() == true at pubSize 67");
    }

    // (6b) At scale, the FAR END of the indexing binds — public word 66 is consumed by the gate at
    // row 132, which is exactly where an off-by-one in `pubSize + gateIndex` would land.
    #[test]
    fn wide_last_public_word_binds() {
        let (c, index, gm) = setup("pi_wide.json");
        let last = c.public_input_size - 1;
        assert!(
            prove_and_verify(&index, &gm, build_witness(&c), &tamper_public(&c, last)).is_err(),
            "the LAST public word ({last}) is inert — the tail of the public-input indexing does \
             not reach the circuit"
        );
    }

    // (6c) …and the same non-vacuity control holds at scale, so (6b) is not a blanket reject.
    #[test]
    fn wide_unconstrained_cell_accepted() {
        let (c, index, gm) = setup("pi_wide.json");
        let last = c.public_input_size - 1;
        prove_and_verify(&index, &gm, tamper(&c, 3, last), &build_public(&c))
            .expect("pi_wide rejected an unread + unwired cell — it is rejecting everything");
    }
}
