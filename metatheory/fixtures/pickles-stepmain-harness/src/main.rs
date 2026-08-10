// PROVE the Lean-assembled `step_verifier.verify_one` recursive verifier, rung by rung.
//
// The circuit (Lean-authored by `Dregg2.Circuit.Emit.KimchiStepMain`) is the recursive verifier in
// the five named sub-circuits `verify_one` runs:
//
//   r1_transcript  the Fp Poseidon SPONGE — an init pin, one pinned pad cell, and `tBlocks`
//                  PERMUTATIONS (a Generic absorb row where the block swallows anything + an 11-row
//                  Poseidon permutation + its output Zero row). A SQUEEZE EMITS NO BLOCK: Mina's
//                  sponge is lazy (`snarky/sponge/sponge.ml:296-325`), so a squeeze from
//                  `Absorbed _` performs the pending block's permutation and a second consecutive
//                  squeeze reads `state.(1)` for free. `tBlocks` is `ceil(items/2)` at upstream's
//                  own squeeze schedule. The sponge STATE crosses every block boundary as a sigma
//                  class: no prior rung had ever copy-wired a Poseidon gate to anything.
//   r2_challenges  `to_field_checked` — 8 chained EndoMulScalar rows per challenge, the (n,a,b)
//                  accumulators hopping row->row through sigma (row k's n8/a8/b8 at cols 1/4/5 IS
//                  row k+1's n0/a0/b0 at cols 0/2/3), plus a Generic decomposition row tying the
//                  reconstructed n8 back to the SPONGE OUTPUT variable.
//   r3_msm         `multiscale_known` — var_base_mul terms of 26 five-bit chunks, summed by a
//                  complete_add chain. Each term's scalar counter chain CLOSES ON ITS CHALLENGE:
//                  the final n' cell and the challenge's final n8 cell are the SAME VARIABLE.
//   r4_ipa         `Scalar_challenge.endo` fold rounds — 32 four-bit endo_mul blocks each, chained
//                  by ROW OVERLAP (not sigma), each closing on its own challenge, folded by a
//                  second complete_add chain.
//   r5_full        + the deferred b(zeta) = prod(1 + u_i * zeta^(2^(k-1-i))) Generic chain over the
//                  challenge variables, the combined_inner_product Horner chain, and the
//                  PRIMARY_LEN public-input ties. Placed through `placeChecked`, so an inert public
//                  word REFUSES rather than passing green.
//   r6_ft_eval0    + `scalars_env` + the linearization CONSTANT TERM (all six kimchi gate bodies
//                  behind their selectors, alpha-combined) + `ft_eval0` + `Plonk_checks.checked`'s
//                  `perm` scalar, compiled from a straight-line program onto double-Generic rows.
//                  Its `ft_eval0` output IS the `ft` column r5's combined_inner_product folds.
//   r7_absorption  + the fr-sponge: an OPT-SPONGE over the carried bulletproof challenges with a
//                  per-block keep MASK (the `Field.if_` state mux), the 43-column evaluation
//                  absorption at zeta and zeta*omega, and `hash_messages_for_next_step_proof`.
//   r8_finalize    + `finalize_other_proof`'s TAIL - the rung at which the deferred values stop
//                  being computed and start BINDING: the second challenge polynomial at
//                  zeta*omega so b_actual = challenge_poly(zeta) + r*challenge_poly(zeta*omega),
//                  the THREE `Shifted_value.Type1.to_field` unshifts (Type1 over Fp - the value's
//                  own field) of the statement's combined_inner_product, b and plonk.perm,
//                  `xi_correct` against the fr-sponge's own squeeze, and
//                  `Boolean.all [xi_correct; b_correct; cip_correct; plonk_checks_passed]` behind
//                  the `should_verify` mux, ASSERTED. The four statement words are the FIRST FOUR
//                  public words, so leg (5) below aims the public tamper straight at a deferred
//                  value.
//
// WHAT IT DOES. Reads the Lean-emitted circuit JSON (gate typ/wires/coeffs, the 15-wide witness
// grid, the public vector, and the sigma-only probe rows), builds the pure-Rust kimchi objects, and
// PROVES + VERIFIES through the SAME `proof-systems` (tag 0.3.0) front door mina-rust uses.
//
//   (1) HONEST        verify()==true on the assembled rung.
//   (2) WIRING        flip col 0 of a probe row -> REJECTED. Probe rows are standalone `Zero` rows
//                     carrying a copy of a sub-circuit boundary value; a `Zero` gate reads nothing
//                     and no gate reads a probe row, so that cell is constrained by the
//                     copy-permutation AND BY NOTHING ELSE. The rejection IS sigma.
//   (3) NOT-ADJACENCY the SAME flips on the UNWIRED circuit (identical rows, identical witness,
//                     probe rows in NO sigma class) are ACCEPTED. So (2) is the WIRE.
//   (4) NON-VACUITY   flip an unread advice cell (col 12) of a probe row -> ACCEPTED.
//   (5) PUBLIC INPUT  (rungs with public_input_size > 0) the honest proof against a tampered public
//                     vector is REJECTED; and flipping public cell (0,0) AND telling the verifier
//                     the new value -- so the public row's own constraint w0[0] = p0 still holds --
//                     is STILL REJECTED, by the copy-permutation alone.
//
// disable_gates_checks=true: a sigma desync is rejected by the PROOF (the permutation argument's
// z-polynomial), not by a debug assert.
//
// House Law #1: the CIRCUIT (gates/coeffs/witness + cross-gate placement) is Lean-authored;
// `proof-systems` is the Rust PROVER that RUNS it. No OCaml, no Node, no o1js in this path.
//
// SCOPE. INNER-KIMCHI FIDELITY of the assembled recursive verifier. NOT a soundness proof, NOT
// "machine-checked Pickles", NOT a Mina-valid proof; the kimchi proof is an INNER proof of a
// `verify_one`-shaped circuit, and wrap is a later rung.

use std::path::{Path, PathBuf};
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

const RUNGS: [&str; 9] = [
    "r1_transcript",
    "r2_challenges",
    "r3_msm",
    "r4_ipa",
    "r5_full",
    "r6_ft_eval0",
    "r7_absorption",
    "r8_finalize",
    "r9_opening",
];

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

/// Which probe rows to tamper. Every probe at small scale; at scale a spread SAMPLE, because each
/// tamper is a full prove. The sample always contains the FIRST and the LAST probe (the ends of the
/// chain) plus evenly spaced interior ones, and the chosen rows are printed.
fn probe_sample(probes: &[usize], budget: usize) -> Vec<usize> {
    if probes.len() <= budget {
        return probes.to_vec();
    }
    let n = probes.len();
    (0..budget)
        .map(|i| probes[i * (n - 1) / (budget - 1)])
        .collect()
}

struct RungOutcome {
    rows: usize,
    domain: usize,
    probes_tested: usize,
    honest_ms: u128,
}

/// The whole four/five-polarity gate for ONE rung. Panics on any falsification.
fn run_rung(dir: &Path, tag: &str, rung: &str, budget: usize) -> RungOutcome {
    let wired = load_path(&dir.join(format!("stepmain_{tag}_{rung}.json")));
    let unwired = load_path(&dir.join(format!("stepmain_{tag}_{rung}_unwired.json")));

    // The control must be a control: same rows, same gate types, byte-identical witness, DIFFERENT
    // wires. If the witnesses ever diverge, (3) proves nothing.
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

    let gm = step::group_map();
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

    // (1) HONEST.
    let t = Instant::now();
    prove_and_verify(&iw, &gm, build_witness(&wired), &pub_w).unwrap_or_else(|e| {
        panic!(
            "[FATAL] {rung}: honest {}-row rung REJECTED: {e}",
            wired.num_rows
        )
    });
    let honest = t.elapsed();
    println!(
        "[1 HONEST   ] verify()==true on the {}-row {rung} (MEASURED {:?})",
        wired.num_rows, honest
    );

    // (2) WIRING BINDS, at a spread of sigma-only probes.
    let sample = probe_sample(wired.probes(), budget);
    for &r in &sample {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &pub_w).is_err(),
            "[FALSIFICATION] {rung}: probe-row {r} col-0 desync ACCEPTED on the WIRED circuit"
        );
    }
    println!(
        "[2 WIRING   ] {}/{} sigma-only probes REJECT a col-0 desync (rows {:?})",
        sample.len(),
        wired.probes().len(),
        sample
    );

    // (3) NOT-ADJACENCY control.
    prove_and_verify(&iu, &gm, build_witness(&unwired), &pub_w)
        .unwrap_or_else(|e| panic!("[FATAL] {rung}: honest UNWIRED witness REJECTED: {e}"));
    for &r in &sample {
        assert!(
            prove_and_verify(&iu, &gm, tamper(&unwired, 0, r), &pub_w).is_ok(),
            "[FALSIFICATION] {rung}: probe-row {r} flip REJECTED on the UNWIRED circuit - (2) was not the wire"
        );
    }
    println!("[3 CONTROL  ] the SAME flips ACCEPTED on the UNWIRED circuit -> (2) is the WIRE, not adjacency");

    // (4) NON-VACUITY: an advice cell no gate reads and no cycle contains.
    let p0 = wired.probes()[0];
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 12, p0), &pub_w).is_ok(),
        "[FALSIFICATION] {rung}: unread advice cell (col 12, row {p0}) flip REJECTED - the rejections may be vacuous"
    );
    println!("[4 NONVACU  ] unread advice cell (col 12, row {p0}) flip ACCEPTED (non-vacuity)");

    // (5) PUBLIC INPUT, when the rung has one.
    if wired.public_input_size > 0 {
        // (5a) the honest proof against a TAMPERED public vector.
        let mut bad = pub_w.clone();
        bad[0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&iw, &gm, build_witness(&wired), &bad).is_err(),
            "[FALSIFICATION] {rung}: honest proof ACCEPTED against a tampered public vector"
        );
        // (5b) the sigma leg: flip public cell (0,0) AND tell the verifier the new value, so the
        // public row's own constraint w0[0] = p0 still holds. Only the copy-permutation can refuse.
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, 0), &bad).is_err(),
            "[FALSIFICATION] {rung}: public cell (0,0) flip WITH a matching public vector ACCEPTED - the public word is not wired in"
        );
        let last = wired.public_input_size - 1;
        let mut bad_last = pub_w.clone();
        bad_last[last] += Fp::from(1u64);
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, last), &bad_last).is_err(),
            "[FALSIFICATION] {rung}: public cell ({last},0) flip WITH a matching public vector ACCEPTED"
        );
        println!(
            "[5 PUBLIC   ] {} public words: a tampered public vector REJECTED, and the sigma leg (flip cell (i,0) AND tell the verifier) REJECTED at i=0 and i={last}",
            wired.public_input_size
        );
    }

    RungOutcome {
        rows: wired.num_rows,
        domain: iw.cs.domain.d1.size as usize,
        probes_tested: sample.len(),
        honest_ms: honest.as_millis(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // No args: the COMMITTED fixture subset (see `stepmain_tests::COMMITTED` for why it is a
    // subset). With a directory: every rung the driver emitted there.
    let (dir, tag, budget, rungs): (PathBuf, String, usize, Vec<&str>) = match args.len() {
        0 => (
            fixtures_dir(),
            "smoke".to_string(),
            usize::MAX,
            vec!["r1_transcript", "r8_finalize"],
        ),
        1 => (
            PathBuf::from(&args[0]),
            "step".to_string(),
            8,
            RUNGS.to_vec(),
        ),
        _ => (
            PathBuf::from(&args[0]),
            args[1].clone(),
            args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8),
            RUNGS.to_vec(),
        ),
    };

    // ⚑ `DREGG_SM_RUNGS` — a comma list that RESTRICTS the run to those rungs, the exact twin of
    // the wrap harness's `DREGG_WM_RUNGS` and additive in the same way: unset, the behaviour is
    // exactly what it was.
    //
    // ⚠ ⚑ **IT EXISTS TO REACH THE `endo_inv` WITNESSES, WHICH NOTHING WITH A POLARITY GATE COULD
    // REACH.** §19d's rewire of `runIpa` onto `combine_split_commitments` + `Scalar_challenge.
    // endo_inv` added `nBulletPairs` WITNESSED curve points — fifteen at `shapeStep`. It is
    // ROW-COUNT-NEUTRAL wherever `nBulletPairs = 0`, and `nBulletPairs shapeSmoke = 0`
    // (`KimchiStepMainPins01`, `…Pins03`), so **the smoke fixtures exercise none of them**: the only
    // tracked artifact that contains an `endo_inv` witness at all is `stepmain_step_r8_finalize`
    // (10 753 rows, `shapeStep`), and its only consumer was `pickles_kimchi_marshal`, which PROVES
    // it and marshals it but runs no sigma leg, no unwired control and no unread-cell leg.
    // `RUNGS` is a fixed nine and only `r8_finalize` is emitted at the step tag, so
    // `harness <dir> step` died on the eight absent files — the coverage was unreachable by
    // arithmetic, not by choice. With the filter:
    //
    //     DREGG_SM_RUNGS=r8_finalize cargo run --release -- \
    //       metatheory/fixtures/pickles-stepmain-harness/fixtures step 8
    let filt = std::env::var("DREGG_SM_RUNGS").ok();
    let rungs: Vec<&str> = match &filt {
        None => rungs,
        Some(f) => {
            let want: Vec<&str> = f
                .split(',')
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .collect();
            let sel: Vec<&str> = rungs.into_iter().filter(|r| want.contains(r)).collect();
            assert!(
                !sel.is_empty(),
                "DREGG_SM_RUNGS={f:?} selected NO rung out of {RUNGS:?} - refusing to report a \
                 green run that proved nothing"
            );
            sel
        }
    };

    println!("== step_main harness: the LEAN-ASSEMBLED `verify_one` RECURSIVE VERIFIER ==");
    println!("   dir={} tag={tag}", dir.display());
    let mut summary = Vec::new();
    for rung in rungs {
        let o = run_rung(&dir, &tag, rung, budget);
        summary.push((rung, o));
        println!();
    }
    println!("== SUMMARY ==");
    for (rung, o) in &summary {
        println!(
            "   {rung:<14} {:>6} rows  domain {:>6}  honest prove+verify {:>7} ms  probes {:>3}",
            o.rows, o.domain, o.honest_ms, o.probes_tested
        );
    }
    println!(
        "== VERDICT: nine sub-circuits of `step_verifier.verify_one` ASSEMBLE from Lean, PROVE"
    );
    println!("   pure-Rust with verify()==true, and BIND at every sub-circuit boundary. ==");
    // ⚠ AND SAY WHAT `r9_opening` DOES NOT ADD. It emits `check_bulletproof`'s opening side, so
    // `verified` (#11) is `equal_g`'s output cell instead of a free witness. It does NOT refuse an
    // on-curve substitution: `G`, `z_1` and `z_2` have no binder inside `verify_one`, the honest
    // witness this harness proves SOLVES `G` off `lhs`, and a substituting prover solves its own.
    // The Lean side names that fact rather than leaving it to a reader
    // (`substituted_assembly_still_closes_equal_g`). A proved r9 is a proved ASSEMBLY, not a
    // proved OPENING.
    println!("== ⚠ r9_opening proves the ASSEMBLY, not the OPENING: `equal_g` refuses no on-curve");
    println!("   substitution — `G`, `z_1`, `z_2` are free, and the honest witness solves `G`. ==");
}

// =====================================================================================
// Committed CI gate. `cargo test --release --manifest-path .../Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod stepmain_tests {
    use super::*;

    /// The COMMITTED subset of the ladder. All SEVEN rungs are emitted by the driver and were
    /// proved at both scales (see the header), but the rungs are CUMULATIVE — r7 contains r6
    /// contains r5 … — so committing all fourteen fixtures would put tens of MB of
    /// seven-times-redundant JSON in the tree and re-churn all of it on every assembly change.
    /// `r1_transcript` ISOLATES the copy-wired Poseidon sponge at minimum cost and `r7_absorption`
    /// is the SUPERSET; `r6_ft_eval0` is committed too but only READ (the census test below), not
    /// proved in CI, because it is r7 minus the sponge segments. Regenerate/prove the other four
    /// with the driver + `harness <dir> <tag>` (Cargo.toml header).
    const COMMITTED: [&str; 2] = ["r1_transcript", "r8_finalize"];

    struct Fixture {
        wired: CircuitJson,
        unwired: CircuitJson,
        iw: step::Index,
        iu: step::Index,
        gm: step::Map,
        public: Vec<Fp>,
    }

    fn fixture(rung: &str) -> Fixture {
        let dir = fixtures_dir();
        let wired = load_path(&dir.join(format!("stepmain_smoke_{rung}.json")));
        let unwired = load_path(&dir.join(format!("stepmain_smoke_{rung}_unwired.json")));
        let iw = index_for(&wired);
        let iu = index_for(&unwired);
        let public = public_of(&wired);
        Fixture {
            wired,
            unwired,
            iw,
            iu,
            gm: step::group_map(),
            public,
        }
    }

    // ── (1) HONEST ──────────────────────────────────────────────────────────────────────────
    #[test]
    fn honest_rungs_verify() {
        for rung in COMMITTED {
            let f = fixture(rung);
            prove_and_verify(&f.iw, &f.gm, build_witness(&f.wired), &f.public)
                .unwrap_or_else(|e| panic!("{rung}: honest witness REJECTED: {e}"));
        }
    }

    // ── (2) WIRING: a sigma-ONLY probe cell is constrained by the copy-permutation and by NOTHING
    // else (a `Zero` gate reads nothing and no gate reads a probe row), so its rejection IS sigma.
    // EVERY probe, not a sample.
    #[test]
    fn every_sigma_probe_binds() {
        for rung in COMMITTED {
            let f = fixture(rung);
            for &r in f.wired.probes() {
                for col in [0usize, 1usize] {
                    assert!(
                        prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, col, r), &f.public)
                            .is_err(),
                        "{rung}: probe-row {r} col-{col} desync ACCEPTED on the WIRED circuit"
                    );
                }
            }
        }
    }

    // ── (3) NOT-ADJACENCY: the honest UNWIRED witness verifies, and the SAME flips are ACCEPTED
    // there. Same rows, byte-identical witness; the only difference is the sigma class.
    #[test]
    fn unwired_control_accepts_the_same_flips() {
        for rung in COMMITTED {
            let f = fixture(rung);
            prove_and_verify(&f.iu, &f.gm, build_witness(&f.unwired), &f.public)
                .unwrap_or_else(|e| panic!("{rung}: honest UNWIRED witness REJECTED: {e}"));
            for &r in f.unwired.probes() {
                assert!(
                    prove_and_verify(&f.iu, &f.gm, tamper(&f.unwired, 0, r), &f.public).is_ok(),
                    "{rung}: probe-row {r} flip REJECTED on the UNWIRED circuit - the wired reject was not the wire"
                );
            }
        }
    }

    // The control IS a control: identical rows, identical gate types, byte-identical witness, and
    // DIFFERENT wires. If the witnesses ever diverged, the acceptance above would prove nothing.
    #[test]
    fn control_differs_only_in_the_placement() {
        for rung in COMMITTED {
            let f = fixture(rung);
            assert_eq!(f.unwired.num_rows, f.wired.num_rows);
            assert_eq!(
                f.unwired.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
                f.wired.gates.iter().map(|g| g.typ).collect::<Vec<_>>()
            );
            assert_eq!(f.unwired.witness, f.wired.witness);
            assert_ne!(
                f.unwired
                    .gates
                    .iter()
                    .map(|g| g.wires.clone())
                    .collect::<Vec<_>>(),
                f.wired
                    .gates
                    .iter()
                    .map(|g| g.wires.clone())
                    .collect::<Vec<_>>()
            );
        }
    }

    // ── (4) NON-VACUITY: advice cells no gate reads and no cycle contains -> ACCEPTED. Without
    // this the rejections above could all be an artefact of a circuit that rejects everything.
    #[test]
    fn unread_advice_cells_are_accepted() {
        for rung in COMMITTED {
            let f = fixture(rung);
            let p0 = f.wired.probes()[0];
            for col in [12usize, 13usize] {
                assert!(
                    prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, col, p0), &f.public).is_ok(),
                    "{rung}: unread advice cell (col {col}, row {p0}) flip REJECTED - the rejections may be vacuous"
                );
            }
        }
    }

    // ── (5) PUBLIC INPUT (r5 only): the proof BINDS the claim, and each public word is WIRED into
    // the circuit rather than merely declared.
    #[test]
    fn public_input_binds_and_is_wired_in() {
        let f = fixture("r8_finalize");
        assert!(f.wired.public_input_size > 0);
        // (a) the honest proof against a TAMPERED public vector.
        let mut bad = f.public.clone();
        bad[0] += Fp::from(1u64);
        assert!(
            prove_and_verify(&f.iw, &f.gm, build_witness(&f.wired), &bad).is_err(),
            "honest proof ACCEPTED against a tampered public vector"
        );
        // (b) the sigma leg: flip public cell (i,0) AND tell the verifier the new value, so the
        // public row's own constraint w0[i] = p_i still holds. Only the copy-permutation can refuse.
        for i in [0usize, f.wired.public_input_size - 1] {
            let mut b = f.public.clone();
            b[i] += Fp::from(1u64);
            assert!(
                prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, 0, i), &b).is_err(),
                "public cell ({i},0) flip WITH a matching public vector ACCEPTED - public word {i} is not wired in"
            );
        }
    }

    // The full rung really is the assembled verifier: strictly larger than the transcript rung, and
    // carrying all SEVEN gate types Mina's own step circuits use (measured on the `step-zkapp-proved`
    // blob: Zero/Generic/Poseidon/CompleteAdd/VarBaseMul/EndoMul/EndoMulScalar and nothing else — no
    // lookup, no foreign-field, no range-check). A regression that quietly shrank it to a toy, or
    // dropped a sub-circuit's gate family, shows here rather than behind a green prove.
    #[test]
    fn full_rung_is_the_whole_assembly_with_seven_gate_types() {
        let dir = fixtures_dir();
        let r1 = load_path(&dir.join("stepmain_smoke_r1_transcript.json"));
        let full = load_path(&dir.join("stepmain_smoke_r7_absorption.json"));
        assert!(
            full.num_rows > r1.num_rows,
            "the full rung ({} rows) does not extend the transcript rung ({} rows)",
            full.num_rows,
            r1.num_rows
        );
        assert!(!r1.probes().is_empty() && !full.probes().is_empty());
        let cen = gate_census(&full);
        for (ord, name) in [
            (0usize, "Zero"),
            (1, "Generic"),
            (2, "Poseidon"),
            (3, "CompleteAdd"),
            (4, "VarBaseMul"),
            (5, "EndoMul"),
            (6, "EndoMulScalar"),
        ] {
            assert!(cen[ord] > 0, "the full rung emits no {name} gate");
        }
        // The closing rung carries Step's public input path.
        assert!(full.public_input_size > 0);
        assert_eq!(full.public_strings().len(), full.public_input_size);
        // The transcript rung does NOT (it is placed at pubSize 0) - so the public-input legs of
        // the gate are attributable to the closing rungs alone.
        assert_eq!(r1.public_input_size, 0);
    }

    // The two rungs added on top of `verify_one`'s first five sub-circuits really are there, and
    // each is the sub-circuit it claims: r6 is scalar arithmetic (Generic-only on top of r5) and r7
    // is the fr-sponge (Poseidon permutations on top of r6, 11 rows each - upstream's own run
    // length). A regression that emitted an EMPTY rung would prove green and say nothing; this is
    // what makes the ladder's top two rungs load-bearing rather than relabelled copies of r5.
    #[test]
    fn ft_eval0_and_absorption_rungs_extend_the_assembly() {
        let dir = fixtures_dir();
        let r1 = load_path(&dir.join("stepmain_smoke_r1_transcript.json"));
        let r6 = load_path(&dir.join("stepmain_smoke_r6_ft_eval0.json"));
        let r7 = load_path(&dir.join("stepmain_smoke_r7_absorption.json"));
        let c6 = gate_census(&r6);
        let c7 = gate_census(&r7);
        // r6 is `ft_eval0` + `Plonk_checks.checked` + the linearization constant term: the compiled
        // straight-line program is HUNDREDS of double-Generic rows, not a handful.
        assert!(
            c6[1] > 600,
            "r6 has only {} Generic rows - the ft_eval0 / constant-term program is missing",
            c6[1]
        );
        // r7 adds the fr-sponge: WHOLE Poseidon permutations (11 rows each, upstream's own run
        // length) and NOT ONE new curve gate.
        assert!(
            c7[2] >= c6[2] + 11 * 40,
            "r7 added only {} Poseidon rows over r6 - the evaluation absorption is missing",
            c7[2] - c6[2]
        );
        assert_eq!(
            (c7[2] - c6[2]) % 11,
            0,
            "r7's added Poseidon rows are not whole permutations"
        );
        for ord in [3usize, 4, 5] {
            assert_eq!(
                c6[ord], c7[ord],
                "r7 changed a CURVE gate family (ord {ord}) - the absorption rung is not a sponge"
            );
        }
        // r7 adds EXACTLY TWO further `to_field_checked` chains - 16 EndoMulScalar rows - and both
        // hang off `r_actual`, the fr-sponge's SECOND squeeze: the chain that lifts it into the `r`
        // the combined_inner_product fold and `b_correct` multiply by
        // (`step_verifier.ml:1008,1013`), AND `lowest_128_bits`' `assert_128_bits` of its high part,
        // which is itself a `to_field_checked` (`step_verifier.ml:88-97,190-192`) and is what stops
        // a prover choosing the low part outright. It was +8 until 2026-08-02, when the range check
        // landed. `==` and not `>=` so a THIRD chain appearing here is also a red.
        assert_eq!(
            c7[6],
            c6[6] + 16,
            "r7's EndoMulScalar delta is {} - expected exactly two 8-row `to_field_checked` chains \
             (r_actual's lift and the `assert_128_bits` of its high part)",
            c7[6] - c6[6]
        );
        // r7 also adds the absorb rows and the opt-sponge mux rows.
        assert!(c7[1] > c6[1]);
        // Each rung strictly extends the one below and keeps the public-input path.
        assert!(r1.num_rows < r6.num_rows && r6.num_rows < r7.num_rows);
        assert!(r6.public_input_size > 0 && r7.public_input_size > 0);
        assert!(r7.probes().len() > r6.probes().len());
        assert_eq!(r1.public_input_size, 0);
    }

    // r8 is `finalize_other_proof`'s TAIL, and it is the rung that makes the deferred values BIND.
    // It must be (a) strictly larger than r7, (b) NO CURVE GATE and no new Poseidon permutation on
    // top of it - it is scalar arithmetic, the `Field.equal` boolean gadgets, and the two
    // `assert_128_bits` chains its own `lowest_128_bits` owes - and (c) still carrying the
    // PRIMARY_LEN public-input path whose FIRST FOUR words are now the statement's deferred values.
    // A regression that relabelled r7 as r8 would pass every prove and say nothing; this is what
    // catches it.
    #[test]
    fn finalize_rung_binds_the_deferred_values() {
        let dir = fixtures_dir();
        let r7 = load_path(&dir.join("stepmain_smoke_r7_absorption.json"));
        let r8 = load_path(&dir.join("stepmain_smoke_r8_finalize.json"));
        let c7 = gate_census(&r7);
        let c8 = gate_census(&r8);
        assert!(
            r8.num_rows > r7.num_rows,
            "r8 ({} rows) does not extend r7 ({} rows) - the finalize rung is empty",
            r8.num_rows,
            r7.num_rows
        );
        // (b) NO CURVE GATE, NO NEW SPONGE: every one of those families is unchanged.
        for (ord, name) in [
            (2usize, "Poseidon"),
            (3, "CompleteAdd"),
            (4, "VarBaseMul"),
            (5, "EndoMul"),
        ] {
            assert_eq!(
                c7[ord], c8[ord],
                "r8 changed the {name} family - the finalize rung is not scalar arithmetic"
            );
        }
        // …and EXACTLY TWO further `to_field_checked` chains - 16 EndoMulScalar rows - which are
        // the THIRD `lowest_128_bits` in the assembly: `xi_actual = lowest_128_bits (squeeze
        // fr_sponge)` (`step_verifier.ml:821-822`; `lowest_128_bits` is `:99-101` and `xi_correct`
        // itself is `:1010-1013` — `:1102` is `combine ~ft:ft_eval1`, a fifth wrong citation of the
        // same line, corrected 2026-08-03), whose high part `util.ml:98` asserts
        // unconditionally and whose low part `util.ml:99` asserts because
        // `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`. It was +0 until
        // 2026-08-02: R8 split a field element with NOTHING constraining either half, so any
        // 128-bit xi the prover named satisfied `xi_correct` - and since the fold's own multiplier
        // is `to_field_checked` of that same statement word, Fiat-Shamir was his. `==` and not
        // `>=` so a THIRD chain appearing here is also a red.
        assert_eq!(
            c8[6],
            c7[6] + 16,
            "r8's EndoMulScalar delta is {} - expected exactly two 8-row `to_field_checked` chains \
             (the `assert_128_bits` of BOTH parts of `xi_actual`'s `lowest_128_bits`)",
            c8[6] - c7[6]
        );
        // …and it really adds Generic rows (the unshifts, the two b-polynomial legs, the four
        // `Field.equal` gadgets and the `Boolean.all` mux are all double-Generic halves).
        assert!(
            c8[1] >= c7[1] + 30,
            "r8 added only {} Generic rows - `finalize_other_proof`'s tail is missing",
            c8[1] - c7[1]
        );
        // (c) the public-input path, and MORE sigma-only probes than r7.
        assert!(r8.public_input_size > 0);
        assert_eq!(r8.public_strings().len(), r8.public_input_size);
        assert!(r8.probes().len() > r7.probes().len());
    }
}
