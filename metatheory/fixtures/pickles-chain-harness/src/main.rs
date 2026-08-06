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
use std::time::Instant;

use mina_curves::pasta::Fq;

// ⚑ THE ONE DRIVER. `build_gates` / `build_witness` / `index_for` / `prove_and_verify` were
// open-coded in TEN of these harnesses — not ten transcriptions of one reader but ten readers that
// DISAGREED. `pickles-circuit-driver/src/lib.rs` carries the measured list: an `i128` parser that
// cannot hold a round constant, an `F::from_str` that SILENTLY REDUCES a coefficient authored over
// the other pasta prime, a gate table stopping at ordinal 3, two SRS constructions, two preflight
// settings, and two serde shapes with no `public_input` field at all. The bodies below are
// one-liners into the shared reader; the names stay, so everything about THIS rung is untouched.
use pickles_circuit_driver::{
    kimchi::circuits::gate::CircuitGate, kimchi::circuits::wires::COLUMNS, load, load_in, wrap,
    CircuitJson, IndexOpts,
};

const RUNGS: [&str; 4] = ["w1_transcript", "w4_bind", "w5_key", "w6_xhat"];

/// `WRAP_PRIMARY_LEN` — what `Impls.Wrap.input ()` allocates.
const MINA_WRAP_PRIMARY_LEN: usize = 40;

fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

/// A decimal literal as a field element. ⚠ NOT `Fq::from_str`: ark-ff implements that as
/// `BigInt::from_str(s) % MODULUS`, so a coefficient authored over the OTHER pasta prime becomes a
/// well-formed element of this one with no error anywhere. The shared reader REFUSES a
/// non-canonical literal instead.
#[allow(dead_code)]
fn parse_f(s: &str) -> Fq {
    pickles_circuit_driver::parse_field::<Fq>(s)
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
fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fq>> {
    wrap::gates(c)
}

#[allow(dead_code)]
fn build_witness(c: &CircuitJson) -> [Vec<Fq>; COLUMNS] {
    wrap::witness(c)
}

#[allow(dead_code)]
fn build_public(c: &CircuitJson) -> Vec<Fq> {
    wrap::public(c)
}

#[allow(dead_code)]
fn public_of(c: &CircuitJson) -> Vec<Fq> {
    wrap::public(c)
}

/// ⚑ This rung's index options, unchanged from before the collapse: kimchi's serialized TEST srs and
/// `disable_gates_checks` — the prover's debug preflight is SKIPPED so a tampered witness (gate OR
/// permutation) is rejected by the PROOF, returning `Err` rather than panicking.
#[allow(dead_code)]
fn index_from_gates(gates: Vec<CircuitGate<Fq>>, public: usize) -> wrap::Index {
    wrap::index_from_gates(gates, IndexOpts::test(public))
}

#[allow(dead_code)]
fn index_for(c: &CircuitJson) -> wrap::Index {
    wrap::index_for(c, IndexOpts::test(c.public_input_size))
}

#[allow(dead_code)]
fn prove_and_verify(
    index: &wrap::Index,
    group_map: &wrap::Map,
    witness: [Vec<Fq>; COLUMNS],
    public_input: &[Fq],
) -> Result<(), String> {
    wrap::prove_and_verify(index, group_map, witness, public_input)
}

/// ⚑ THE CENSUS MUST BE THERE, AND ITS ABSENCE IS A RED. These were `#[serde(default)]` `Vec`s on
/// this harness's own serde shape, so an emission carrying no census at all read back as an EMPTY
/// one and every slot assertion below quietly ranged over nothing. They are `Option` on the shared
/// reader — absent is distinguishable from empty — and these three REFUSE the absent case.
fn probes_of(c: &CircuitJson) -> &[usize] {
    c.probe_rows
        .as_deref()
        .unwrap_or_else(|| panic!("{}: the emission carries NO probe_rows", c.name))
}

fn derived_of(c: &CircuitJson) -> &[usize] {
    c.derived_slots
        .as_deref()
        .unwrap_or_else(|| panic!("{}: the emission carries NO derived_slots", c.name))
}

fn unread_of(c: &CircuitJson) -> &[usize] {
    c.unread_slots
        .as_deref()
        .unwrap_or_else(|| panic!("{}: the emission carries NO unread_slots", c.name))
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

    let gm = wrap::group_map();
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

    let sample = probe_sample(probes_of(&wired), budget);
    for &r in &sample {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &pub_w).is_err(),
            "[FALSIFICATION] {rung}: probe-row {r} col-0 desync ACCEPTED on the WIRED circuit"
        );
    }
    println!(
        "[2 WIRING   ] {}/{} sigma-only probes REJECT a col-0 desync",
        sample.len(),
        probes_of(&wired).len()
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

    let p0 = probes_of(&wired)[0];
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 12, p0), &pub_w).is_ok(),
        "[FALSIFICATION] {rung}: unread advice cell (col 12, row {p0}) flip REJECTED"
    );
    println!("[4 NONVACU  ] unread advice cell (col 12, row {p0}) flip ACCEPTED (non-vacuity)");

    // (5) PUBLIC INPUT, at MINA'S forty slots — two legs that move in OPPOSITE directions. The
    // VECTOR leg (move the verifier's claim) binds every slot, because each public row is a
    // `Generic` gate `1*w0[i] = pub_i`. The SIGMA leg (flip the cell AND the claim) binds only
    // slots a copy class reaches, i.e. the ones this rung DERIVES — so it refuses there and
    // ACCEPTS at the declared-unread ones, which measures the census rather than asserting it.
    if wired.public_input_size > 0 {
        assert_eq!(
            wired.public_input_size, MINA_WRAP_PRIMARY_LEN,
            "{rung}: the emission must be Mina's own statement width"
        );
        assert_eq!(
            derived_of(&wired).len() + unread_of(&wired).len(),
            MINA_WRAP_PRIMARY_LEN,
            "{rung}: derived + unread must be exactly Mina's forty"
        );
        for i in [derived_of(&wired)[0], unread_of(&wired)[0]] {
            let mut bad = pub_w.clone();
            bad[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, build_witness(&wired), &bad).is_err(),
                "[FALSIFICATION] {rung}: honest proof ACCEPTED against a public vector moved at slot {i}"
            );
        }
        let d = [
            derived_of(&wired)[0],
            derived_of(&wired)[derived_of(&wired).len() - 1],
        ];
        for i in d {
            let mut b = pub_w.clone();
            b[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, i), &b).is_err(),
                "[FALSIFICATION] {rung}: DERIVED slot {i} — cell flip WITH a matching public vector ACCEPTED"
            );
        }
        let u = [
            unread_of(&wired)[0],
            unread_of(&wired)[unread_of(&wired).len() - 1],
        ];
        for i in u {
            let mut b = pub_w.clone();
            b[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, i), &b).is_ok(),
                "[FALSIFICATION] {rung}: UNREAD slot {i} — cell flip WITH a matching public vector REFUSED"
            );
        }
        println!(
            "[5 PUBLIC   ] {} Mina slots ({} derived {:?}): VECTOR leg REJECTS; SIGMA leg REJECTS at derived {d:?} and ACCEPTS at unread {u:?}",
            wired.public_input_size,
            derived_of(&wired).len(),
            derived_of(&wired)
        );
    }

    (wired.num_rows, honest.as_millis())
}

/// ⚑ (6) and (7): the chain's own controls, at the closing rung where the derived words are PUBLIC.
fn run_chain_controls(dir: &Path) {
    for rung in ["w4_bind", "w5_key", "w6_xhat"] {
        run_chain_controls_at(dir, rung);
    }
}

/// ⚑ The two controls, at ONE rung. Run at `w5_key` too since 2026-08-05: a control that only ever
/// ran at the rung below the climb would say nothing about the rung the climb reached.
fn run_chain_controls_at(dir: &Path, rung: &str) {
    let honest = load_path(&dir.join(format!("chain_{rung}.json")));
    let bent = load_path(&dir.join(format!("chainbent_{rung}.json")));
    let unread = load_path(&dir.join(format!("chainunread_{rung}.json")));

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
        "[6 CHAIN +  ] {rung}: bending ONE Fq coordinate of the step proof's w_comm MOVES {moved}/{} wrap public words",
        honest.public_strings().len()
    );

    // ...and the moved circuit is still a real circuit: it proves.
    let gm = wrap::group_map();
    let ib = index_for(&bent);
    prove_and_verify(&ib, &gm, build_witness(&bent), &public_of(&bent))
        .unwrap_or_else(|e| panic!("[FATAL] the BENT-step chained circuit did not prove: {e}"));
    println!("[6 CHAIN +  ] {rung}: ...and the moved circuit still proves with verify()==true");

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
    assert_eq!(probes_of(&unread), probes_of(&honest));
    assert!(
        unread.gates == honest.gates,
        "[FALSIFICATION] bending z_1/z_2/ft_eval1/delta/sg changed the emitted gates"
    );
    assert!(
        unread.witness == honest.witness,
        "[FALSIFICATION] bending z_1/z_2/ft_eval1/delta/sg changed the emitted witness"
    );
    println!(
        "[7 CHAIN -  ] {rung}: bending z_1/z_2/ft_eval1/delta/sg (Fp scalars and non-phase-1 points \
         of the SAME proof) leaves the wrap circuit BYTE-IDENTICAL"
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
        let gm = wrap::group_map();
        for rung in RUNGS {
            let c = load(&format!("chain_{rung}"));
            let i = index_for(&c);
            prove_and_verify(&i, &gm, build_witness(&c), &public_of(&c))
                .unwrap_or_else(|e| panic!("{rung}: honest chained witness REJECTED: {e}"));
        }
    }

    #[test]
    fn every_sigma_probe_binds_and_the_control_accepts() {
        let gm = wrap::group_map();
        for rung in RUNGS {
            let w = load(&format!("chain_{rung}"));
            let u = load(&format!("chain_{rung}_unwired"));
            let iw = index_for(&w);
            let iu = index_for(&u);
            let p = public_of(&w);
            assert!(!probes_of(&w).is_empty(), "{rung}: no probes emitted");
            for &r in probes_of(&w) {
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
        let gm = wrap::group_map();
        for rung in RUNGS {
            let c = load(&format!("chain_{rung}"));
            let i = index_for(&c);
            let p0 = probes_of(&c)[0];
            assert!(
                prove_and_verify(&i, &gm, tamper(&c, 12, p0), &public_of(&c)).is_ok(),
                "{rung}: an unread advice cell flip was REJECTED - the rejections may be vacuous"
            );
        }
    }

    #[test]
    fn public_input_binds_and_is_wired_in() {
        let gm = wrap::group_map();
        let c = load("chain_w4_bind");
        let i = index_for(&c);
        let p = public_of(&c);
        assert_eq!(c.public_input_size, MINA_WRAP_PRIMARY_LEN);
        let mut bad = p.clone();
        bad[0] += Fq::from(1u64);
        assert!(prove_and_verify(&i, &gm, build_witness(&c), &bad).is_err());
        // the SIGMA leg: REFUSE where the rung derives, ACCEPT where it declares unread.
        for k in [derived_of(&c)[0], derived_of(&c)[derived_of(&c).len() - 1]] {
            let mut b = p.clone();
            b[k] += Fq::from(1u64);
            assert!(
                prove_and_verify(&i, &gm, tamper(&c, 0, k), &b).is_err(),
                "DERIVED slot ({k},0) flip WITH a matching public vector ACCEPTED"
            );
        }
        for k in [unread_of(&c)[0], unread_of(&c)[unread_of(&c).len() - 1]] {
            let mut b = p.clone();
            b[k] += Fq::from(1u64);
            assert!(
                prove_and_verify(&i, &gm, tamper(&c, 0, k), &b).is_ok(),
                "UNREAD slot ({k},0) flip WITH a matching public vector REFUSED"
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
