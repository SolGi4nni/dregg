// pickles-wrapmain-harness — PROVE the Lean-assembled `wrap_main` rungs.
//
// ⚑ THIS IS THE WRAP SIDE, AND IT IS A DIFFERENT CURVE AND A DIFFERENT FIELD FROM THE STEP ONE.
// `wrap_main_inputs.ml:4,6` sets `Me = Tock`, `Impl = Impls.Wrap`, so the wrap circuit's native
// field is `Tock.Field = Fq` and a wrap kimchi proof is committed on **Pallas**, whose scalar field
// is Fq. The step harness proves over Vesta/Fp. Everything below is Pallas/Fq: the prover index,
// both sponges, and every coefficient and witness cell parsed out of the Lean emission.
//
// The circuit is Lean-authored by `Dregg2.Circuit.Emit.KimchiWrapMain` — gate list, coefficients,
// cross-gate placement (`KimchiPlacement.placeChecked`) and the composed witness grid
// (`WitnessBuilder.compose`). House Law #1: `proof-systems` (tag 0.3.0) is the Rust PROVER that
// RUNS it and authors no constraint. No OCaml, no Node, no o1js in this path.
//
// NINE RUNGS, each a superset of the one below, each proved with BOTH polarities:
//   w1_transcript  the Fq Poseidon sponge of `wrap_verifier.ml:516-646` + `check_bulletproof`'s
//                  continuation, driven by the REAL rate-2 state machine (`poseidon.rs:107-146`):
//                  beta and gamma share ONE permutation, and the digest squeeze is the FORK at
//                  `:645-646` that does not advance the transcript
//   w2_challenges  `to_field_checked` over Fq (`scalar_challenge.ml:12-136`) — chained
//                  EndoMulScalar rows with the n0=0/a0=2/b0=2 seeds PINNED, the lowest_128_bits
//                  decomposition, and a SECOND chain over the HIGH part (`util.ml:98` asserts it
//                  unconditionally), closed by `Field.(scale a endo + b)` at Pallas's endo scalar
//   w3_branch      `One_hot_vector.of_index` + `Pseudo.choose` + `Util.ones_vector` +
//                  `Branch_data.Checked.pack` (`wrap_main.ml:164-199`) — the wrap-specific
//                  selection sub-circuit, which has no step-side analogue at all
//   w4_bind        the closing ties: the wrap statement words this assembly DERIVES become public
//                  words through `placeCheckedWith`, so a word no gate reads REFUSES.
//                  ⚑ THE VECTOR IS FORTY WIDE AND IN MINA'S SLOT ORDER — `WRAP_PRIMARY_LEN`, what
//                  `Impls.Wrap.input ()` allocates and what `make_zkapp_verifier_index` hands
//                  `kimchi::verifier::verify`. Which of the forty this rung derives travels with
//                  the circuit as `derived_slots`; the rest as `unread_slots`. The sixteen unread
//                  are Mina's own: ten `Spec.T.Constant`/dead-lookup slots upstream allocates and
//                  never reads, and six pass-throughs (0-4, 9) `wrap_main` READS but never CHECKS
//                  - their checker is the NEXT proof's `finalize_other_proof`
//   w5_key         W-KEY: `choose_key` (`wrap_verifier.ml:189-204`) as a one-hot fold over the
//                  per-branch step keys - which are `Inner_curve.constant`, so it is Generic
//                  arithmetic and not a curve MSM - plus the INDEX SPONGE (`:521-530`), whose
//                  squeeze IS the transcript's first absorbed word. This is the rung at which
//                  `index_digest` stops being a fixture and starts being DERIVED
//   w6_xhat        W-XHAT: the PUBLIC-INPUT MSM (`wrap_verifier.ml:539-616`) and the first curve
//                  gates on this side. 67 entries at 15x255 / 40x128 / 12x1, `scale_fast2'`
//                  ladders with their `add_fast base base` seeds and `n_acc = 0` PINNED, both
//                  halves of the `s_div_2` top-bit range check moved out of ADVICE into
//                  permutation columns, every base and correction pinned against the devnet SRS,
//                  and the fold's output written into the very cells `:617` ABSORBS. ⚑ This rung
//                  MOVES THE TRANSCRIPT: `x_hat` stops being the `RC_XHAT` fixture, so every
//                  rung's witness below it changes even though its GATES do not
//   w7_split       W-SPLIT: `split_field` (`wrap_main.ml:69-81`, called at `:409`) — one
//                  `Boolean.typ` check and one `Field.Assert.equal ((of_int 2 * y) + is_odd) x`
//                  per statement `Field` word, whose outputs ARE w6's 255-bit and 1-bit entry
//                  scalars, so the tie is a sigma class and not a new cell. ⚠ READ §16 BEFORE
//                  QUOTING THIS RUNG: with `x` a free witness (W-PREV is not emitted) the
//                  constraint pins NOTHING; its content lands when W-PREV ties `x`. The gadget is
//                  upstream's and is emitted faithfully — including the parity being
//                  boolean-constrained TWICE, which is upstream's duplication and not ours
//   w8_ftcomm      W-FTCOMM: `Common.ft_comm` (`common.ml:238-256`) — `tComms + 1` ladders at
//                  `Ops.scale_fast ~num_bits:255`, 51 chunks each, so 8 x 51 = 408 rows at the
//                  wrap shape, which is exactly `wrap-transaction`'s VarBaseMul 2417 minus
//                  W-XHAT's 1805 and W-BULLET's 204. ⚑ They are `scale_fast`, NOT `scale_fast2`
//                  (`wrap_verifier.ml:658-659` shadows it), so there is no split, no mux, no
//                  correction and — the part that matters — NO top-bit-zero loop: the 255 bit
//                  cells are tied to the scalar only by `n_acc = scalar` over Fq, and `B` and
//                  `B + q` both satisfy that. §17 names it and proves it; it is upstream's, and
//                  bounding it here would be a divergence from `wrap_main`, not a fix to it.
//                  The first ladder's base is W-KEY's sealed `sigma_comm.(6)`
//   w9_prev        W-PREV: the WITNESSED PREVIOUS STEP STATEMENT (`wrap_main.ml:201-256` and
//                  `:340-356`). ⚑ READ §18 BEFORE QUOTING THIS RUNG. Its OWN rows are small on
//                  purpose, because upstream `exists ~request:Req.Proof_state` costs only what its
//                  `typ` checks: TWO `Boolean.typ`s on the two `should_finalize` words, and NOTHING
//                  else - `Limb_vector.Challenge.typ` is `Typ.field` with a transport and no range
//                  check at all, and the `~assert_16_bits` `wrap_main.ml:208` passes is consumed
//                  ONLY by `Branch_data`, which the STEP per-proof spec does not contain. Plus
//                  `Inner_curve.typ`'s `assert_on_curve` on each of the two `prev_step_accs` -
//                  three R1CS rows each, over the very cells `wrap_verifier.ml:538` ABSORBS as
//                  `sg_old` - and one `Field.Assert.equal` that makes
//                  `messages_for_next_step_proof` a PUBLIC word. What the rung really buys is in
//                  the WIRING: the 67 MSM scalars stop being 67 independent draws and become the
//                  packed image of 57 statement words, so `w7_split`'s `x` is the word itself and
//                  no longer a cell derived downward from its own outputs. ⚠ `x_hat` does NOT
//                  leave the unconsumed census: 66 of the 67 scalars are still free witnesses,
//                  here and upstream, and what would tie them is W-FINALIZE / W-WRAPHACK
//
// THE GATE, per rung:
//   (1) HONEST      — the assembled circuit's good witness verify()==true;
//   (2) WIRING      — desyncing a sigma-ONLY probe cell is REJECTED (probe rows are standalone
//                     `Zero` rows: a `Zero` gate reads nothing and no gate reads a probe row, so
//                     that cell is constrained by the copy-permutation AND BY NOTHING ELSE);
//   (3) NOT-ADJACENCY — the SAME flips on the UNWIRED control (identical rows, byte-identical
//                     witness, probe rows in NO sigma class) are ACCEPTED;
//   (4) NON-VACUITY — an unread advice-cell flip is ACCEPTED;
//   (5) PUBLIC INPUT (w4 and up) — TWO legs that move in OPPOSITE directions across Mina's forty
//                     slots. The VECTOR leg (move the verifier's claim alone) is REJECTED at every
//                     slot, derived or not: a public row is a `Generic` gate `1*w0[i] = pub_i` and
//                     the negated public polynomial is added to the quotient. The SIGMA leg (flip
//                     the CELL and tell the verifier the new value) is REJECTED at every DERIVED
//                     slot and ACCEPTED at every declared-unread one — which MEASURES the 24-vs-40
//                     census instead of asserting it. An unread slot that refused, or a derived
//                     slot that accepted, is a red.
//
// disable_gates_checks=true: a sigma desync is rejected by the PROOF (the permutation argument's
// z-polynomial), not by a debug assert.
//
// SCOPE. INNER-KIMCHI FIDELITY of ELEVEN assembled sub-circuits of `wrap_main`. NOT a soundness
// proof, NOT "machine-checked Pickles", NOT a Mina-valid proof; the kimchi proof is an INNER
// Pallas/Fq proof of a `wrap_main`-SHAPED circuit, and `KimchiWrapMain` §13 names by sub-circuit
// everything that is not here (W-OPENINGS, W-COMBINE, W-BULLET and W-FINALIZE).
//
//   w11_wraphack   W-WRAPHACK: the THREE `hash_messages_for_next_wrap_proof` Fq sponges
//                  (`wrap_hack.ml:110-137` at `wrap_main.ml:341-348` and `:421-431`). ⚑ It is the
//                  rung that closes the public vector: wrap statement word 11 is the closing
//                  sponge's `squeeze_field`, and with it all TWENTY-FOUR statement words
//                  `wrap_main` pins are derived. ⚠ 24, not 40 - words 0-4 and 9 are deferred
//                  values it passes through unchecked, 30-37 are `Spec.T.Constant` and 38-39 the
//                  dead lookup `Opt`. Its two prev-proof sponges also give `old_bp_chals` its only
//                  consumer and turn packed statement words 55/56 from fixtures into squeezes.
//   w12_close      W-CLOSE: `Boolean.Assert.is_true bulletproof_success` (`wrap_main.ml:419-420`).
//                  ONE constraint, and its input is W-BULLET's - so what it buys is that a witness
//                  whose opening FAILED is refused, not that the opening is checked here.
//
// ⚠ ⚑ **THE COMMITTED FIXTURES PREDATE THE MINA SLOT LAYOUT AND MUST BE RE-EMITTED.** They carry
// `public_input_size: 6` and no `derived_slots`; this harness now REQUIRES Mina's forty. The first
// assertion of polarity (5) says so in its own words ("the emission must be Mina's own statement
// width"), and that red is the correct one — do NOT add a compatibility branch for the old shape,
// re-emit. A full smoke ladder is ~45 min at `w12_close` and above, which is why this note exists
// rather than a half-updated fixture directory: mixing two emissions in one directory is worse
// than a red, because every cross-rung ladder assertion silently compares different circuits.
//
// REGENERATE the fixtures (only when the Lean assembly changes):
//   cd metatheory && lake build Dregg2.Circuit.Emit.KimchiWrapMain \
//     && DREGG_WM=smoke lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean \
//     && cp /tmp/pickles-wrapmain/wrapmain_smoke_*.json \
//           fixtures/pickles-wrapmain-harness/fixtures/
//
// RUN the committed gate (RELEASE — a debug prove is minutes):
//   cargo test --release --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml
// RUN the wrap-scale rung set (all six rungs, timed):
//   DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean
//   cargo run --release --manifest-path .../Cargo.toml -- /tmp/pickles-wrapmain wrap

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

// ⚑ Pallas-committed, Fq-scalar. `kimchi/src/curve.rs:62-72,87-97`: a proof on curve G runs its
// phase-1 sponge with `G::other_curve_sponge_params()` over `G::BaseField` and its phase-2 with
// `G::sponge_params()` over `G::ScalarField`. For Pallas that is fp_kimchi then fq_kimchi — the
// mirror of the step harness, which is the whole point.
type BaseSponge = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>;

/// The fifteen rungs. `rungsUpto` is a TREE, not a chain — each rung is a superset of its BASE, and
/// three branches hang off `w9_prev`, because `wrap_main.ml` runs `finalize_other_proof` (`:329`)
/// before `hash_messages_for_next_wrap_proof` (`:340`) and neither reads the other's rows:
///
///     w9_prev ─┬─ w10_finalize ── w11_finsponge
///              └─ w10_combine  ── w11_bullet ── w12_close
///                                              (+ w11_wraphack's own rows)
///     w9_prev ─── w11_wraphack
///
/// ⚠ ⚑ **THIS DIAGRAM WAS WRONG AND NOTHING CAUGHT IT.** It drew `w12_close` hanging off
/// `w11_wraphack` on a branch of its own, which was true until 2026-08-05. Since then
/// `close_rung_extends_bullet` — kernel-clean and general over every `WrapData` — states
/// `rungRows _ .close = rungRows _ .bullet ++ rungOwn _ .wraphack ++ rungOwn _ .close`, because
/// `Boolean.Assert.is_true bulletproof_success` needs the rows that COMPUTE `bulletproof_success`.
/// The committed fixtures still carry the old shape (`w12_close` 2260 rows against `w11_bullet`'s
/// 3654 — a subset of what it must contain), and **no test compared the two**, so a topology change
/// in the Lean, a fixture set that never followed it, and a diagram describing neither were all
/// simultaneously green. `close_rung_contains_bullet` below is that missing comparison.
///
/// ⚠ So no single file here is the whole circuit, and this array's ORDER is the emission order, not
/// a containment order. `wrapmain-shape-diff.mjs` assembles the union by prefix-stripping.
const RUNGS: [&str; 15] = [
    "w1_transcript",
    "w2_challenges",
    "w3_branch",
    "w4_bind",
    "w5_key",
    "w6_xhat",
    "w7_split",
    "w8_ftcomm",
    "w9_prev",
    "w10_finalize",
    // ⚑ W-FINSPONGE: `finalize_other_proof`'s sponge half — the nested challenge digest, the
    // 91-element finalize sponge, and the three legs of `Boolean.all` that need its two squeezes.
    "w11_finsponge",
    "w11_wraphack",
    "w12_close",
    // ⚑ W-COMBINE and W-BULLET hang off `w9_prev` too, and they are the pair that closes
    // `wrap-transaction`'s `EndoMul 2528 = 32 × (46 + 33)` — the family this assembly emitted
    // ZERO of before them.
    "w10_combine",
    "w11_bullet",
];

// ---- the Lean-emitted JSON shape (identical schema to the step side's) ----

#[derive(Deserialize, Clone)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize, Clone)]
struct CircuitJson {
    #[allow(dead_code)]
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    /// Absolute rows of the sigma-ONLY probes. Emitted WITH the circuit so the tampers aim at what
    /// the Lean schedule produced, not at a hand-copied constant a drift would invalidate.
    probe_rows: Vec<usize>,
    /// ⚑ Which of MINA'S forty statement slots this emission DERIVES, and which it declares
    /// unread. Emitted WITH the circuit for the same reason `probe_rows` is: a Rust gate that had
    /// to guess the split would be testing its own guess. `default` so a `pubSize = 0` rung, which
    /// carries neither, still parses.
    #[serde(default)]
    derived_slots: Vec<usize>,
    #[serde(default)]
    unread_slots: Vec<usize>,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>,
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

/// ⚑ `Fq`, not `Fp`. A step-side coefficient reduced mod p would parse here and mean something
/// else, so this is the one-line difference that decides which circuit is being proved.
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
    assert_eq!(
        c.public_input.len(),
        c.public_input_size,
        "the emitted public vector must have public_input_size entries"
    );
    c.public_input.iter().map(|s| parse_fq(s)).collect()
}

// disable_gates_checks = true: skip the prover's debug preflight so a tampered witness (gate OR
// permutation) is rejected by the PROOF, returning Err rather than panicking.
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

/// A flip of witness cell (col,row) by +1, returning a fresh tampered witness.
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

#[allow(dead_code)]
/// Maximal run lengths of one gate type — the fidelity signal the region-conformance diff reads.
fn run_lengths(c: &CircuitJson, typ: u64) -> Vec<usize> {
    let mut out = Vec::new();
    let mut cur = 0usize;
    for g in &c.gates {
        if g.typ == typ {
            cur += 1;
        } else if cur > 0 {
            out.push(cur);
            cur = 0;
        }
    }
    if cur > 0 {
        out.push(cur);
    }
    out
}

/// Which probe rows to tamper. Every probe at small scale; at scale a spread SAMPLE, because each
/// tamper is a full prove. The sample always contains the FIRST and the LAST probe plus evenly
/// spaced interior ones, and the chosen rows are printed.
/// Mina's own wrap statement width — `Impls.Wrap.input ()` allocates forty and
/// `make_zkapp_verifier_index` hands `kimchi::verifier::verify` forty. The Lean emission carries it
/// in `public_input_size`; this constant is the INDEPENDENT source the emission is checked against,
/// so a silently narrowed emission is a red rather than a self-consistent smaller circuit.
const MINA_WRAP_PRIMARY_LEN: usize = 40;

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

/// The whole five-polarity gate for ONE rung. Panics on any falsification.
fn run_rung(dir: &Path, tag: &str, rung: &str, budget: usize) -> RungOutcome {
    let wired = load_path(&dir.join(format!("wrapmain_{tag}_{rung}.json")));
    let unwired = load_path(&dir.join(format!("wrapmain_{tag}_{rung}_unwired.json")));

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
    let sample = probe_sample(&wired.probe_rows, budget);
    for &r in &sample {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &pub_w).is_err(),
            "[FALSIFICATION] {rung}: probe-row {r} col-0 desync ACCEPTED on the WIRED circuit"
        );
    }
    println!(
        "[2 WIRING   ] {}/{} sigma-only probes REJECT a col-0 desync (rows {:?})",
        sample.len(),
        wired.probe_rows.len(),
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
    let p0 = wired.probe_rows[0];
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 12, p0), &pub_w).is_ok(),
        "[FALSIFICATION] {rung}: unread advice cell (col 12, row {p0}) flip REJECTED - the rejections may be vacuous"
    );
    println!("[4 NONVACU  ] unread advice cell (col 12, row {p0}) flip ACCEPTED (non-vacuity)");

    // (5) PUBLIC INPUT, when the rung has one — and at MINA'S LAYOUT it has two legs that move in
    // OPPOSITE directions, which is the whole point of running it slot by slot.
    //
    //   · THE VECTOR LEG binds at EVERY one of the forty. A public row is a `Generic` gate
    //     `1·w0[i] = pub_i`, and the negated public polynomial is added to the quotient, so moving
    //     the verifier's claim alone breaks row `i` whether or not any other gate reads it.
    //   · THE SIGMA LEG discriminates. Flip the CELL and tell the verifier the new value and the
    //     row is satisfied again; what refuses is the copy-permutation, and only a slot this rung
    //     DERIVES is in a class with a cell the circuit reads. So a derived slot REFUSES and an
    //     unread slot ACCEPTS — and that acceptance is the 24-vs-40 split MEASURED at the prover
    //     rather than asserted in a comment. An unread slot that refused here would mean the split
    //     is not what the emission says it is.
    if wired.public_input_size > 0 {
        assert_eq!(
            wired.public_input_size, MINA_WRAP_PRIMARY_LEN,
            "{rung}: the emission must be Mina's own statement width"
        );
        assert!(
            !wired.derived_slots.is_empty(),
            "{rung}: a rung with a public vector must declare which slots it derives"
        );
        assert_eq!(
            wired.derived_slots.len() + wired.unread_slots.len(),
            MINA_WRAP_PRIMARY_LEN,
            "{rung}: derived + unread must be exactly Mina's forty"
        );

        // the vector leg, at both ends of each set
        let mut vector_probed = 0usize;
        for &i in [
            wired.derived_slots[0],
            wired.derived_slots[wired.derived_slots.len() - 1],
            wired.unread_slots[0],
            wired.unread_slots[wired.unread_slots.len() - 1],
        ]
        .iter()
        {
            let mut bad = pub_w.clone();
            bad[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, build_witness(&wired), &bad).is_err(),
                "[FALSIFICATION] {rung}: honest proof ACCEPTED against a public vector moved at slot {i}"
            );
            vector_probed += 1;
        }

        // ⚑ SAMPLED, not exhaustive, and the sampling is spread across each set rather than taken
        // from its head: one `prove_and_verify` is a full kimchi proof, and 40 of them per rung
        // across 15 rungs at wrap scale is minutes of nothing new. `probe_sample` is the same
        // spread the wiring polarity uses.
        let derived_s = probe_sample(&wired.derived_slots, budget.min(4).max(2));
        let unread_s = probe_sample(&wired.unread_slots, budget.min(4).max(2));

        // the sigma leg, at every sampled derived slot: REFUSE
        for &i in &derived_s {
            let mut bad = pub_w.clone();
            bad[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, i), &bad).is_err(),
                "[FALSIFICATION] {rung}: DERIVED slot {i} — cell flip WITH a matching public vector ACCEPTED, so the slot is not wired to anything the circuit reads"
            );
        }
        // …and at the unread ones: ACCEPT. The control that makes the line above a measurement.
        let mut unread_accepted = 0usize;
        for &i in &unread_s {
            let mut bad = pub_w.clone();
            bad[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, i), &bad).is_ok(),
                "[FALSIFICATION] {rung}: UNREAD slot {i} — cell flip WITH a matching public vector REFUSED, so the declared unread set is wrong"
            );
            unread_accepted += 1;
        }
        println!(
            "[5 PUBLIC   ] {} Mina slots ({} derived {:?}, {} declared unread): VECTOR leg REJECTS at {vector_probed}/4 sampled; SIGMA leg REJECTS at derived {:?} and ACCEPTS at unread {:?} ({unread_accepted} of them)",
            wired.public_input_size,
            wired.derived_slots.len(),
            wired.derived_slots,
            wired.unread_slots.len(),
            derived_s,
            unread_s
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
    let (dir, tag, budget, rungs): (PathBuf, String, usize, Vec<&str>) = match args.len() {
        0 => (
            fixtures_dir(),
            "smoke".to_string(),
            usize::MAX,
            vec![
                "w1_transcript",
                "w7_split",
                "w8_ftcomm",
                "w9_prev",
                "w11_wraphack",
                "w12_close",
                "w10_combine",
                "w11_bullet",
            ],
        ),
        1 => (
            PathBuf::from(&args[0]),
            "wrap".to_string(),
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

    // ⚑ `DREGG_WM_RUNGS` — a comma list that RESTRICTS the run to those rungs. Additive and
    // opt-in: unset, the behaviour is exactly what it was. It exists because a lane that owns two
    // rungs of fourteen should not have to emit and prove the other twelve to see its own five
    // polarities, and because the emitter is minutes per rung.
    let filt = std::env::var("DREGG_WM_RUNGS").ok();
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
                "DREGG_WM_RUNGS={f:?} selected NO rung out of {RUNGS:?} - refusing to report a \
                 green run that proved nothing"
            );
            sel
        }
    };

    println!("== wrap_main harness: the LEAN-ASSEMBLED WRAP-SIDE sub-circuits, over Pallas/Fq ==");
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
        "== VERDICT: eleven sub-circuits of `wrap_main` ASSEMBLE from Lean, PROVE pure-Rust on"
    );
    println!("   PALLAS with verify()==true, and BIND at every sub-circuit boundary. The rest of");
    println!("   `wrap_main` is named by sub-circuit in KimchiWrapMain §13. ==");
}

// =====================================================================================
// Committed CI gate. `cargo test --release --manifest-path .../Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod wrapmain_tests {
    use super::*;

    /// The fixture subset actually PROVED in CI: the bottom rung, the closing rung, and the top
    /// one. w2/w3 are read for their census without proving, because each prove is seconds and the
    /// ladder pins (`KimchiWrapMain` §12b, §14b) already establish that they are supersets.
    const COMMITTED: [&str; 13] = [
        "w1_transcript",
        "w4_bind",
        "w5_key",
        "w6_xhat",
        "w7_split",
        "w8_ftcomm",
        "w9_prev",
        "w10_finalize",
        "w11_finsponge",
        "w11_wraphack",
        "w12_close",
        "w10_combine",
        "w11_bullet",
    ];

    struct Fixture {
        wired: CircuitJson,
        unwired: CircuitJson,
        iw: Idx,
        iu: Idx,
        gm: <Pallas as CommitmentCurve>::Map,
        public: Vec<Fq>,
    }

    fn load(rung: &str) -> CircuitJson {
        load_path(&fixtures_dir().join(format!("wrapmain_smoke_{rung}.json")))
    }

    fn fixture(rung: &str) -> Fixture {
        let wired = load(rung);
        let unwired = load(&format!("{rung}_unwired"));
        let iw = index_for(&wired);
        let iu = index_for(&unwired);
        let public = public_of(&wired);
        Fixture {
            wired,
            unwired,
            iw,
            iu,
            gm: <Pallas as CommitmentCurve>::Map::setup(),
            public,
        }
    }

    #[test]
    fn honest_rungs_verify() {
        for rung in COMMITTED {
            let f = fixture(rung);
            prove_and_verify(&f.iw, &f.gm, build_witness(&f.wired), &f.public)
                .unwrap_or_else(|e| panic!("{rung}: honest witness REJECTED: {e}"));
        }
    }

    #[test]
    fn every_sigma_probe_binds() {
        for rung in COMMITTED {
            let f = fixture(rung);
            assert!(!f.wired.probe_rows.is_empty(), "{rung}: no probes emitted");
            for &r in &f.wired.probe_rows {
                assert!(
                    prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, 0, r), &f.public).is_err(),
                    "{rung}: probe row {r} col-0 desync ACCEPTED on the WIRED circuit"
                );
            }
        }
    }

    #[test]
    fn unwired_control_accepts_the_same_flips() {
        for rung in COMMITTED {
            let f = fixture(rung);
            prove_and_verify(&f.iu, &f.gm, build_witness(&f.unwired), &f.public)
                .unwrap_or_else(|e| panic!("{rung}: honest UNWIRED witness REJECTED: {e}"));
            for &r in &f.wired.probe_rows {
                assert!(
                    prove_and_verify(&f.iu, &f.gm, tamper(&f.unwired, 0, r), &f.public).is_ok(),
                    "{rung}: probe row {r} flip REJECTED on the UNWIRED control - the wiring test was not about the wire"
                );
            }
        }
    }

    #[test]
    fn control_differs_only_in_the_placement() {
        for rung in COMMITTED {
            let f = fixture(rung);
            assert_eq!(f.unwired.num_rows, f.wired.num_rows);
            assert_eq!(
                f.unwired.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
                f.wired.gates.iter().map(|g| g.typ).collect::<Vec<_>>()
            );
            assert_eq!(
                f.unwired
                    .gates
                    .iter()
                    .map(|g| g.coeffs.clone())
                    .collect::<Vec<_>>(),
                f.wired
                    .gates
                    .iter()
                    .map(|g| g.coeffs.clone())
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                f.unwired.witness, f.wired.witness,
                "{rung}: the control's witness must be byte-identical"
            );
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

    #[test]
    fn unread_advice_cells_are_accepted() {
        for rung in COMMITTED {
            let f = fixture(rung);
            let p0 = f.wired.probe_rows[0];
            assert!(
                prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, 12, p0), &f.public).is_ok(),
                "{rung}: an unread advice cell flip was REJECTED - the rejections may be vacuous"
            );
        }
    }

    /// ⚑ **THE PUBLIC VECTOR IS MINA'S FORTY, AND THE TWO LEGS MOVE IN OPPOSITE DIRECTIONS.**
    /// See the `(5)` block in `run_rung` for why: the VECTOR leg binds every slot (each public row
    /// is a `Generic` gate `1·w0[i] = pub_i`), while the SIGMA leg binds only slots this rung
    /// DERIVES. The unread half ACCEPTING is not a weakness being tolerated — it is the
    /// measurement that the emission's 24-vs-40 census is the truth about the circuit.
    #[test]
    fn public_input_binds_and_is_wired_in() {
        for rung in ["w4_bind", "w5_key", "w9_prev", "w11_wraphack", "w12_close"] {
            let f = fixture(rung);
            assert_eq!(
                f.wired.public_input_size, MINA_WRAP_PRIMARY_LEN,
                "{rung} must carry MINA'S statement width"
            );
            assert_eq!(
                f.wired.derived_slots.len() + f.wired.unread_slots.len(),
                MINA_WRAP_PRIMARY_LEN,
                "{rung}: derived + unread must be exactly Mina's forty"
            );
            // the VECTOR leg — every sampled slot, derived or not
            for i in [
                f.wired.derived_slots[0],
                f.wired.unread_slots[0],
                MINA_WRAP_PRIMARY_LEN - 1,
            ] {
                let mut bad = f.public.clone();
                bad[i] += Fq::from(1u64);
                assert!(
                    prove_and_verify(&f.iw, &f.gm, build_witness(&f.wired), &bad).is_err(),
                    "{rung}: the honest proof was ACCEPTED against a public vector moved at slot {i}"
                );
            }
            // the SIGMA leg — REFUSE at derived, ACCEPT at unread
            for &i in &[
                f.wired.derived_slots[0],
                f.wired.derived_slots[f.wired.derived_slots.len() - 1],
            ] {
                let mut b = f.public.clone();
                b[i] += Fq::from(1u64);
                assert!(
                    prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, 0, i), &b).is_err(),
                    "{rung}: DERIVED slot {i} — cell flip WITH a matching public vector ACCEPTED, so the word is not wired in"
                );
            }
            for &i in &[
                f.wired.unread_slots[0],
                f.wired.unread_slots[f.wired.unread_slots.len() - 1],
            ] {
                let mut b = f.public.clone();
                b[i] += Fq::from(1u64);
                assert!(
                    prove_and_verify(&f.iw, &f.gm, tamper(&f.wired, 0, i), &b).is_ok(),
                    "{rung}: UNREAD slot {i} — cell flip WITH a matching public vector REFUSED, so the declared unread set is wrong"
                );
            }
        }
    }

    /// ⚑ w9 is W-PREV: the WITNESSED PREVIOUS STEP STATEMENT (`wrap_main.ml:201-256`, `:340-356`).
    /// Three measurable things, and the third is the one that matters:
    ///   (a) the public vector GROWS BY EXACTLY ONE - `messages_for_next_step_proof`, the
    ///       `Field.Assert.equal` of `:350-351`. It is the ONLY rung above `w4_bind` that grows it,
    ///       because it is the only one that derives a wrap statement word `w4_bind` did not;
    ///   (b) the rung adds NO curve gate and NO Poseidon permutation - `exists ~request` costs its
    ///       `typ`'s checks and nothing else, and that `typ` emits two `Boolean.typ`s over 57 words
    ///       (`Limb_vector.Challenge.typ` has NO range check; the `~assert_16_bits` is consumed only
    ///       by `Branch_data`, absent from the STEP per-proof spec). A Poseidon run appearing here
    ///       would mean W-WRAPHACK had been folded in without being named;
    ///   (c) it adds exactly one sigma-only probe.
    /// ⚠ What the rung BUYS is not visible in this census at all - it is that the x_hat MSM's
    /// scalar cells ARE the packed statement words (`KimchiWrapMain.prev_msm_scalars_are_the_
    /// statement_words`, proved in the KERNEL). The gate count is deliberately small; do not read
    /// it as the size of the change.
    #[test]
    fn prev_rung_adds_one_public_word_and_no_curve_gate() {
        let w8 = load("w8_ftcomm");
        let w9 = load("w9_prev");
        let c8 = gate_census(&w8);
        let c9 = gate_census(&w9);
        assert!(w9.num_rows > w8.num_rows, "the ladder is monotone");
        // ⚑ THE WIDTH IS MINA'S AT BOTH — what grows is the DERIVED set, by exactly one slot, and
        // the slot is 12: `messages_for_next_step_proof`, the `Field.Assert.equal` of `:350-351`.
        assert_eq!(w9.public_input_size, w8.public_input_size);
        assert_eq!(w9.public_input_size, MINA_WRAP_PRIMARY_LEN);
        assert_eq!(
            w9.derived_slots.len(),
            w8.derived_slots.len() + 1,
            "w9 must derive exactly one more Mina slot than every rung below it"
        );
        assert!(
            w9.derived_slots.contains(&12) && !w8.derived_slots.contains(&12),
            "the slot w9 adds must be Mina's 12"
        );
        assert_eq!(w9.public_input.len(), w9.public_input_size);
        for k in [2usize, 3, 4, 5, 6] {
            assert_eq!(
                c9[k], c8[k],
                "w9 adds only Generic/Zero rows (family {k} moved) - a Poseidon or curve run here \
                 would mean W-WRAPHACK or W-COMBINE was folded in unnamed"
            );
        }
        assert_eq!(
            w9.probe_rows.len(),
            w8.probe_rows.len() + 1,
            "W-PREV drops exactly one sigma-only probe"
        );
        assert_eq!(
            w9.gates.len(),
            w9.num_rows,
            "placement produced a gate per row (incl. the public rows)"
        );
    }

    /// ⚑ w5 is W-KEY: `choose_key` (`wrap_verifier.ml:189-204`) over `Inner_curve.constant` step
    /// keys — which is `Generic` arithmetic, NOT a curve MSM — plus the INDEX SPONGE
    /// (`wrap_verifier.ml:521-530`), a fresh Fq Poseidon absorbing the 28 chosen commitments as 56
    /// coordinates and squeezing once. At rate 2 that is exactly 28 permutations, and the squeeze
    /// adds exactly one more sigma-only probe. The DERIVATION's own reality gate — that the squeeze
    /// reproduces the digest Rust kimchi computed for the same index — is
    /// `KimchiWrapMain.key_digest_is_the_index_digest`, proved in the KERNEL, not here.
    #[test]
    fn key_rung_adds_the_index_sponge_and_no_curve_gate() {
        let w4 = load("w4_bind");
        let w5 = load("w5_key");
        let c4 = gate_census(&w4);
        let c5 = gate_census(&w5);
        assert!(w5.num_rows > w4.num_rows, "the ladder is monotone");
        assert_eq!(
            c5[2],
            c4[2] + 28 * 11,
            "w5 must add exactly 28 whole Fq permutations - the 56-coordinate index sponge"
        );
        for (i, n) in run_lengths(&w5, 2).iter().enumerate() {
            assert_eq!(*n, 11, "Poseidon run {i} is {n} rows, not one permutation");
        }
        for k in [3usize, 4, 5, 6] {
            assert_eq!(
                c5[k], c4[k],
                "choose_key is Generic arithmetic over CONSTANT keys - family {k} must not move"
            );
        }
        assert_eq!(
            w5.derived_slots, w4.derived_slots,
            "index_digest is not a wrap statement word; the derived slot set must not grow"
        );
        assert_eq!(
            w5.probe_rows.len(),
            w4.probe_rows.len() + 1,
            "the index sponge's single squeeze must add exactly one sigma-only probe"
        );
    }

    /// ⚑ **`w12_close` MUST CONTAIN `w11_bullet`, and until now nothing here said so.**
    ///
    /// The Lean states it kernel-clean and general over every `WrapData`
    /// (`KimchiWrapMain.close_rung_extends_bullet`, 2026-08-05):
    /// `rungRows _ .close = rungRows _ .bullet ++ rungOwn _ .wraphack ++ rungOwn _ .close`.
    /// `w12_close` asserts `bulletproof_success`, which is `equal_g`'s output, so the rung that
    /// asserts it has to carry the rows that compute it.
    ///
    /// ⚠ This is a RATIO check, not a row-count pin: the exact delta is `w11_wraphack`'s own rows
    /// plus two, and pinning that number here would duplicate a fact the Lean already proves
    /// generally. What this catches is the SHAPE — a `w12_close` smaller than `w11_bullet` cannot
    /// be a superset of it, whatever the arithmetic. That is exactly the state the committed
    /// fixtures were in while every other gate stayed green.
    #[test]
    fn close_rung_contains_bullet() {
        let bullet = load("w11_bullet");
        let close = load("w12_close");
        assert!(
            close.num_rows > bullet.num_rows,
            "w12_close ({} rows) must be a strict superset of w11_bullet ({} rows) — \
             close_rung_extends_bullet says .close = .bullet ++ wraphack-own ++ close-own. \
             A smaller w12_close means the fixtures predate that topology and must be re-emitted.",
            close.num_rows,
            bullet.num_rows
        );
        // …and per gate family, since a row count alone can be reached by a different circuit.
        let cb = gate_census(&bullet);
        let cc = gate_census(&close);
        for k in 0..7 {
            assert!(
                cc[k] >= cb[k],
                "w12_close must contain every w11_bullet gate of family {k}: {} < {}",
                cc[k],
                cb[k]
            );
        }
    }

    /// ⚑ w11_finsponge IS `finalize_other_proof`'s SPONGE half, and this is the census that says so
    /// — the rung this whole epoch's largest remaining Poseidon gap was named against.
    ///
    /// Per instance: the nested challenge-digest sponge over the 30 flattened old bulletproof
    /// challenges (**15** permutations — the rate-2 machine permutes before absorbs 3, 5, …, 29,
    /// which is 14, and once more for the squeeze, which arrives at `Absorbed 2`), and the
    /// 91-element finalize sponge (**46** — 45 during the absorbs and one for the FIRST squeeze;
    /// the second reads lane 1 of that SAME permutation, `wrap_verifier.ml:892-894`, which is why
    /// this is 46 and not 47). **61 per instance, 122 at `prevs = 2`.** Mina's `wrap-transaction`
    /// carries 261 `(Poseidon x 11, Zero)` blocks; the assembly carried 137 before this rung.
    ///
    /// ⚠ The `EndoMulScalar` run length is asserted at **8** and that is this file being STRICTER
    /// than Mina, not short of it. `compute_challenges` (`:1012-1013`) lifts all fifteen bulletproof
    /// challenges in ONE unbroken `EndoMulScalar x 120` run upstream; `tfcRowsQ` brackets every
    /// chain with its own seed pins and lift row because upstream's `a0`/`b0` are one constant
    /// `Cvar` and its `a8`/`b8` closing is a `Cvar` linear combination that emits NO row. Fifteen
    /// chains therefore come out as fifteen x8 blocks. Widening the emitted rows to reach x120
    /// would be emitting rows to match a histogram.
    #[test]
    fn finsponge_rung_adds_the_two_finalize_sponges() {
        let w10 = load("w10_finalize");
        let w11 = load("w11_finsponge");
        let c10 = gate_census(&w10);
        let c11 = gate_census(&w11);
        assert!(w11.num_rows > w10.num_rows, "the ladder is monotone");
        assert_eq!(
            c11[2],
            c10[2] + 122 * 11,
            "w11_finsponge must add exactly 122 whole Fq permutations - 61 per instance at prevs=2"
        );
        for (i, n) in run_lengths(&w11, 2).iter().enumerate() {
            assert_eq!(*n, 11, "Poseidon run {i} is {n} rows, not one permutation");
        }
        // The sponge half emits no curve gadget at all: the ladders it needs (`compute_challenges`)
        // are `EndoMulScalar` chains, and the three legs are Generic arithmetic.
        for k in [3usize, 4, 5] {
            assert_eq!(
                c11[k], c10[k],
                "the sponge half emits no curve gate - family {k} must not move"
            );
        }
        // 19 `to_field_checked` chains per instance: fifteen `compute_challenges` lifts plus
        // xi/xi_hi/r/r_hi, at 8 `EndoMulScalar` rows each.
        assert_eq!(
            c11[6],
            c10[6] + 2 * 19 * 8,
            "w11_finsponge must add exactly 19 eight-row lift chains per instance"
        );
        for (i, n) in run_lengths(&w11, 6).iter().enumerate() {
            assert_eq!(*n, 8, "EndoMulScalar run {i} is {n} rows, not one chain");
        }
        assert_eq!(
            w11.derived_slots, w10.derived_slots,
            "W-FINSPONGE derives no NEW wrap statement word - it derives the PREVIOUS statement's"
        );
        // ⚑ 42 sigma-only probes per instance, and every one is accounted for: 2 per
        // `to_field_checked` chain (`tfcRowsQ` probes `n_8`/`a_8` and `lift`/`b_8`) x 19 chains,
        // one after each of the three squeezes (`transcriptRowsQ` drops one per squeeze — the
        // challenge sponge squeezes once, the finalize sponge twice), and one on the rung's own
        // `cip_actual`/`b_actual` pair. ⚠ MEASURED, not derived: the first draft of this line
        // asserted `+ 2` from the sponge probes alone and was wrong by 82.
        assert_eq!(
            w11.probe_rows.len(),
            w10.probe_rows.len() + 2 * (2 * 19 + 3 + 1),
            "42 sigma-only probes per instance: 19 lift chains x2, 3 squeezes, 1 leg pair"
        );
        assert_eq!(
            w11.gates.len(),
            w11.num_rows,
            "placement produced a gate per row (incl. the public rows)"
        );
    }

    /// ⚑ w1 IS the Fq Poseidon sponge, and the run-length family says so: every `Poseidon` run is
    /// exactly 11 rows (one permutation), and the assembly emits NO curve gate at this rung — the
    /// four families `wrap-transaction` spends 2528 + 2417 + 492 rows on are W-XHAT / W-COMBINE /
    /// W-BULLET and are not here.
    #[test]
    fn transcript_rung_is_the_fq_poseidon_sponge() {
        let c = load("w1_transcript");
        let cen = gate_census(&c);
        assert!(
            cen[2] > 0 && cen[2] % 11 == 0,
            "Poseidon rows must be whole 11-row permutations, got {}",
            cen[2]
        );
        for (i, n) in run_lengths(&c, 2).iter().enumerate() {
            assert_eq!(*n, 11, "Poseidon run {i} is {n} rows, not one permutation");
        }
        assert_eq!(cen[4], 0, "no VarBaseMul at w1");
        assert_eq!(cen[5], 0, "no EndoMul at w1");
        assert_eq!(cen[3], 0, "no CompleteAdd at w1");
        assert_eq!(cen[6], 0, "no EndoMulScalar at w1 - that is w2");
        assert!(cen[1] > 0, "the absorb rows are Generic");
        assert_eq!(
            c.public_input_size, 0,
            "w1 is placed below the closing rung"
        );
    }

    /// ⚑ w2 adds BOTH `lowest_128_bits` chains per challenge and nothing else in the
    /// `EndoMulScalar` family: the count is EXACTLY `2 * chals * 8`, `==` and not `>=`, so a third
    /// chain or a missing high chain is a red.
    #[test]
    fn challenge_rung_adds_both_lowest_128_bits_chains() {
        let w1 = load("w1_transcript");
        let w2 = load("w2_challenges");
        let c1 = gate_census(&w1);
        let c2 = gate_census(&w2);
        assert!(
            w2.num_rows > w1.num_rows,
            "w2 must be a strict superset of w1"
        );
        assert_eq!(c2[2], c1[2], "w2 adds no Poseidon rows");
        assert!(c2[6] > 0, "w2 must emit EndoMulScalar chains");
        assert_eq!(c2[6] % 8, 0, "every to_field_checked chain is 8 rows");
        for (i, n) in run_lengths(&w2, 6).iter().enumerate() {
            assert_eq!(
                *n, 8,
                "EndoMulScalar run {i} is {n} rows, not one 128-bit chain"
            );
        }
        // The smoke shape squeezes 8 `chal`s; both halves of each get a chain.
        assert_eq!(
            c2[6],
            2 * 8 * 8,
            "expected 2 chains per challenge of 8 rows each"
        );
        assert_eq!(c2[4] + c2[5] + c2[3], 0, "w2 emits no curve gate either");
    }

    /// ⚑ w3 is the wrap-specific selection sub-circuit and w4 closes the public tie. w3 adds only
    /// `Generic`/`Zero`; w4 adds only the closing halves and turns the public input ON.
    #[test]
    fn branch_and_bind_rungs_close_the_selection() {
        let w2 = load("w2_challenges");
        let w3 = load("w3_branch");
        let w4 = load("w4_bind");
        let c2 = gate_census(&w2);
        let c3 = gate_census(&w3);
        let c4 = gate_census(&w4);
        assert!(
            w3.num_rows > w2.num_rows && w4.num_rows > w3.num_rows,
            "the ladder is monotone"
        );
        for k in [2usize, 3, 4, 5, 6] {
            assert_eq!(
                c3[k], c2[k],
                "w3 adds only Generic/Zero rows (family {k} moved)"
            );
            assert_eq!(c4[k], c3[k], "w4 adds only Generic rows (family {k} moved)");
        }
        assert_eq!(w2.public_input_size, 0);
        assert_eq!(w3.public_input_size, 0);
        assert_eq!(
            w4.public_input_size, MINA_WRAP_PRIMARY_LEN,
            "w4 is the closing rung and turns MINA'S forty-slot statement on"
        );
        assert_eq!(w4.public_input.len(), w4.public_input_size);
        // ⚑ and the six the SMOKE shape derives sit where Pickles reads them: β γ α ζ at 5-8, the
        // fork digest at 10, the first bulletproof prechallenge at 13.
        assert_eq!(w4.derived_slots, vec![5usize, 6, 7, 8, 10, 13]);
        // ⚑ `placeChecked` refuses an inert public word, so a nonempty public vector that placed
        // at all is evidence every declared word is READ by some gate.
        assert_eq!(
            w4.gates.len(),
            w4.num_rows,
            "placement produced a gate per row (incl. the public rows)"
        );
    }

    /// ⚑ THE FIELD. Every coefficient and witness cell parses as an `Fq` element, and the whole
    /// emission is Pallas-committed. A step-side (mod p) emission would still parse — both primes
    /// are 255 bits — so the real check is that the honest witness VERIFIES on Pallas, which
    /// `honest_rungs_verify` does; this pins the complementary half: the wrap circuit's Poseidon
    /// coefficients are NOT the step circuit's.
    #[test]
    fn the_emission_is_over_fq_and_not_fp() {
        let c = load("w1_transcript");
        // fp_kimchi's first Poseidon round constant, from the step side's own gate emitter. If the
        // wrap emission carried it, the sponge would be the wrong instantiation.
        const FP_KIMCHI_RC0: &str =
            "21155079365419562533580730049431973842736068869601348388420898564282378592202";
        let pos: Vec<&GateJson> = c.gates.iter().filter(|g| g.typ == 2).collect();
        assert!(!pos.is_empty());
        assert_eq!(
            pos[0].coeffs.len(),
            15,
            "a Poseidon row carries 15 round constants"
        );
        assert!(
            !pos[0].coeffs.iter().any(|s| s == FP_KIMCHI_RC0),
            "the wrap emission carries an fp_kimchi round constant - wrong Poseidon instantiation"
        );
        for g in &c.gates {
            for s in &g.coeffs {
                let _ = parse_fq(s);
            }
        }
        for col in &c.witness {
            for s in col {
                let _ = parse_fq(s);
            }
        }
    }
}
