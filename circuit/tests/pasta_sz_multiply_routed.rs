//! # The cheap multiply, ROUTED — both polarities on the deployed prover, and the cost re-derived.
//!
//! `Dregg2.Circuit.Emit.PastaSzMul` proved a Schwartz–Zippel foreign-field multiply — 63 algebraic
//! gates collapsed to 2, on the FAITHFUL carrier (`ChalConstraint.holdsIn` over any `CommRing K`,
//! which is what `ExtensionBuilder::assert_zero_ext` checks) — and it sat with **no Rust consumer,
//! no witness generation and no emitted artifact**. This file is the other end of that route.
//!
//! Four artifacts arrive here, all Lean-authored (`EffectLower.lowerAir` of an `EffectAir`; no
//! hand-written `VmConstraint2` anywhere in the cone — House Law #1):
//!
//! | artifact | source | replaces |
//! |---|---|---|
//! | `dregg-pasta-pallas-complete-add-sz::v1` | `PastaCurveSound.pallasCompleteAddSzDesc` | `…-sound::v1` |
//! | `dregg-pasta-vesta-complete-add-sz::v1`  | `PastaCurveSound.vestaCompleteAddSzDesc`  | `…-sound::v1` |
//! | `dregg-pasta-alu-sz::v1`                 | `MinaWrapVerifierAir.fpAluSzDesc`         | `dregg-pasta-alu-sound::v1` |
//! | `dregg-pasta-alu-fq-sz::v1`              | `MinaWrapVerifierAir.fqAluSzDesc`         | `dregg-pasta-alu-fq-sound::v1` |
//!
//! ⚑ **THESE ARE THE FIRST `chal_gate`-CARRYING ARTIFACTS IN `by-name/`.** They declare
//! `"challenges":2`, they read `permutation_randomness()[0]` and `[1]`, and `Ir2UniAir::new`
//! REFUSES them outright — only `prove_vm_descriptor2`'s multi-table assembly, which has lookup
//! contexts and therefore challenges, can carry them. §5 asserts that refusal rather than
//! describing it.
//!
//! ⚑ **THE PAIRS ARE A CONTROLLED BEFORE/AFTER ON ONE WITNESS.** The sz rows have the SAME
//! declared width, the SAME range lookups and the SAME column layout as the rows they replace, so
//! the *same* Lean-emitted honest trace fixture proves against both artifacts. §6 measures both
//! sides on this binary, on this box, on that one trace.
//!
//! ## ⚠ WHAT THE REFUSALS IN THIS FILE MEAN, AND IT IS NOT WHAT THE SCHOOLBOOK'S MEAN
//!
//! The schoolbook row refuses a forged multiply because the forgery's **witness does not exist**:
//! every gate body is bounded below `p_felt`, so a nonzero ℤ body cannot vanish mod `p_felt`. That
//! is unconditional.
//!
//! The sz row refuses a forged multiply because the forgery's residual polynomial is nonzero
//! (`PastaSzMul.fpHonest_quotient_bump_residual_nonzero`) and the drawn challenge is not one of its
//! `≤ 62` roots. **That is a probabilistic statement**, priced in `PastaSzMul` §6d as `2^−117.7`
//! per check and `2^−197.0` for the two-point form across the whole wrap workload. A refusal
//! observed here is one sample from that distribution, not a proof — and the one-gate form is
//! `2^−98.5`, BELOW this repo's ~124-bit bar (`sz_single_challenge_is_below_the_bar`), which is
//! why every sz artifact here carries TWO challenge gates per multiply and never one. §4 asserts
//! that shape on the bytes.
//!
//! ⚠ **AND THE DRAW ITSELF IS NOT PROVED ANYWHERE.** That the challenges are uniform,
//! post-commitment and drawn from `BinomialExtensionField<BabyBear,4>` is READ off pinned Plonky3
//! `82cfad7` (`p3-batch-stark/src/{prover,transcript}.rs`) and cited in `DescriptorIR2` §2.6. No
//! Lean file proves a Rust transcript's ordering and none claims to.
//!
//! ⚠ **RUN IN RELEASE.** Algebraic refusals are `debug_assert` panics in debug and clean `Err`s in
//! release; a refusal test that passes only in debug is testing the assertion.
//!
//! ```text
//! cargo test -p dregg-circuit --release --test pasta_sz_multiply_routed -- --nocapture
//! ```

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2UniAir, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};

// ── the artifacts ───────────────────────────────────────────────────────────────────────────────
const PALLAS_SOUND: &str =
    include_str!("../descriptors/by-name/pasta-pallas-complete-add-sound.json");
const PALLAS_SZ: &str = include_str!("../descriptors/by-name/pasta-pallas-complete-add-sz.json");
const VESTA_SOUND: &str =
    include_str!("../descriptors/by-name/pasta-vesta-complete-add-sound.json");
const VESTA_SZ: &str = include_str!("../descriptors/by-name/pasta-vesta-complete-add-sz.json");
const ALU_SOUND: &str = include_str!("../descriptors/by-name/pasta-alu-sound.json");
const ALU_SZ: &str = include_str!("../descriptors/by-name/pasta-alu-sz.json");
const ALU_FQ_SZ: &str = include_str!("../descriptors/by-name/pasta-alu-fq-sz.json");

// ── the traces, unchanged: the sz rows are the same layout, so one witness serves both ──────────
const PALLAS_TRACE: &str = include_str!("fixtures/pasta-pallas-complete-add-sound-trace.txt");
const VESTA_TRACE: &str = include_str!("fixtures/pasta-vesta-complete-add-sound-trace.txt");
const ALU_TRACE: &str = include_str!("fixtures/pasta-alu-sound-trace.txt");

/// The Lean layout constants, restated so a drift reds here rather than addressing another column.
const RCB_WIDTH: usize = 3048;
const ALU_WIDTH: usize = 226;
const SK: usize = 32;
/// The 33 SSA intermediates start after the six input blocks.
const V_BASE: usize = 6 * SK;
/// The 12 multiply witnesses: 32 quotient limbs then 62 sixteen-bit carries, 94 columns apart.
const MW_BASE: usize = V_BASE + 33 * SK;
/// The ALU multiply's quotient block (`MinaWrapVerifierAir.ALU_Q_BASE`).
const ALU_Q_BASE: usize = 96;
const SEL_MUL: usize = 222;
const SEL_ADD: usize = 223;
const SEL_SUB: usize = 224;

/// `IR2_FRI_LOG_BLOWUP` — the deployed FRI configuration's blowup exponent.
const LOG_BLOWUP: u32 = 6;

fn desc(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the artifact")
}

fn trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(!rows.is_empty());
    assert!(
        rows.iter().all(|r| r.len() == width),
        "every row is {width} wide"
    );
    rows
}

/// The committed main width, from the descriptor's own tables through the deployed
/// `decomp_cols_pub` — the number every trace-size and LDE figure must be denominated in.
fn committed_width(d: &EffectVmDescriptor2) -> usize {
    let mut aux = 0usize;
    for c in &d.constraints {
        if let VmConstraint2::Lookup(l) = c
            && let Some(bits) =
                d.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
        {
            aux += decomp_cols_pub(bits);
        }
    }
    d.trace_width + aux
}

/// The LDE domain the prover commits to: the padded height times the blowup, times the committed
/// width. This is the memory figure, and the whole point of §6 is that it does not move.
fn lde_cells(d: &EffectVmDescriptor2, rows: usize) -> u64 {
    let padded = rows.next_power_of_two() as u64;
    padded * (1u64 << LOG_BLOWUP) * committed_width(d) as u64
}

fn chal_gates(d: &EffectVmDescriptor2) -> Vec<&VmConstraint2> {
    d.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::ChalGate(_)))
        .collect()
}

fn prove_verify(d: &EffectVmDescriptor2, t: &[Vec<BabyBear>]) -> Result<(f64, f64), String> {
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(d, t, &[], &MemBoundaryWitness::default(), &[])?;
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    verify_vm_descriptor2(d, &proof, &[])?;
    Ok((prove_ms, t1.elapsed().as_secs_f64() * 1000.0))
}

/// ⚑ A forgery that stays INSIDE the declared 8-bit range, and is asserted to have MOVED.
///
/// A forgery that trips a cheaper check than the one under test is not a test of that check: a
/// limb pushed to `256` is caught by the range LOOKUP and the algebra is never exercised. Wrapping
/// inside the limb width keeps every declared lookup satisfied, so the only thing left that can
/// refuse is the multiply's own gate — which is the point of the whole file.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §1 — the shape, off the parsed artifacts.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE COLLAPSE, ON THE BYTES.** `4 476 → 3 744` on the curve row (`12 × 61`), `386 → 325` on
/// the ALU row (`63 − 2`), and the DECLARED WIDTH IS IDENTICAL in both pairs.
#[test]
fn the_sz_artifacts_collapse_the_gates_and_move_no_columns() {
    let (ps, pz) = (desc(PALLAS_SOUND), desc(PALLAS_SZ));
    let (vs, vz) = (desc(VESTA_SOUND), desc(VESTA_SZ));
    let (asnd, asz, aqsz) = (desc(ALU_SOUND), desc(ALU_SZ), desc(ALU_FQ_SZ));

    for (name, before, after, n_before, n_after, width) in [
        (
            "pallas complete-add",
            &ps,
            &pz,
            4476usize,
            3744usize,
            RCB_WIDTH,
        ),
        ("vesta  complete-add", &vs, &vz, 4476, 3744, RCB_WIDTH),
        ("fp     ALU row", &asnd, &asz, 386, 325, ALU_WIDTH),
    ] {
        assert_eq!(
            before.constraints.len(),
            n_before,
            "{name}: schoolbook constraint count"
        );
        assert_eq!(
            after.constraints.len(),
            n_after,
            "{name}: sz constraint count"
        );
        assert_eq!(before.trace_width, width);
        assert_eq!(
            after.trace_width, before.trace_width,
            "{name}: ⚑ the DECLARED WIDTH MUST NOT MOVE — the sz collapse is algebraic, and a \
             width change here would mean the two artifacts are not a controlled pair"
        );
        assert_eq!(
            committed_width(after),
            committed_width(before),
            "{name}: ⚑ and neither does the COMMITTED width — 71.7% of it is range decomposition \
             and Schwartz–Zippel does not touch a single range lookup"
        );
    }
    // The fq ALU twin, because the accumulator leg is Step/Tick on Vesta.
    assert_eq!(aqsz.constraints.len(), 325);
    assert_eq!(aqsz.trace_width, ALU_WIDTH);
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §2 — the HONEST polarity, on the deployed prover, in release.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE SZ CURVE ROW PROVES AND VERIFIES ON BOTH CURVES**, on the SAME honest witness the
/// schoolbook row proves on. `PastaCurveSound.szMulCore_width_unchanged` is why one fixture serves
/// two artifacts: the sz multiply reads the same offset-encoded carry cells `rcbSoundRow` writes.
#[test]
fn the_sz_curve_row_proves_and_verifies_on_both_curves() {
    for (curve, json, text) in [
        ("Pallas", PALLAS_SZ, PALLAS_TRACE),
        ("Vesta", VESTA_SZ, VESTA_TRACE),
    ] {
        let d = desc(json);
        let t = trace(text, RCB_WIDTH);
        let (p, v) = prove_verify(&d, &t)
            .expect("the honest Lean witness must prove under the SZ curve row");
        println!(
            "SZ RCB complete add ({curve}): {} constraints, {} declared / {} committed columns, \
             {} rows — prove {p:.1} ms, verify {v:.1} ms",
            d.constraints.len(),
            d.trace_width,
            committed_width(&d),
            t.len()
        );
    }
}

/// ⚑ **THE SZ ALU ROW PROVES ALL THREE OPERATIONS.** The fixture really is a multiply, an add and
/// a sub — a green on eight copies of one row would not exercise the selector, and the sz gate is
/// selector-gated exactly as the 63 it replaces were.
#[test]
fn the_sz_alu_row_proves_all_three_operations() {
    let d = desc(ALU_SZ);
    let t = trace(ALU_TRACE, ALU_WIDTH);
    let sel = |r: usize, c: usize| t[r][c].as_u32();
    assert_eq!(sel(0, SEL_MUL), 1, "row 0 is a multiply");
    assert_eq!(sel(1, SEL_ADD), 1, "row 1 is an add");
    assert_eq!(sel(2, SEL_SUB), 1, "row 2 is a sub");

    let (p, v) = prove_verify(&d, &t).expect("the honest ALU trace must prove under the SZ row");
    println!(
        "SZ ALU row: {} constraints, {} declared / {} committed columns, {} rows — \
         prove {p:.1} ms, verify {v:.1} ms",
        d.constraints.len(),
        d.trace_width,
        committed_width(&d),
        t.len()
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §3 — the FORGED polarity. Both artifacts, the same tamper, the same refusal.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE MULTIPLY FORGERY IS REFUSED BY THE SZ ROW TOO.** A quotient limb of multiply 0 is moved
/// by `+1 mod 256` — a real, non-zero move that stays INSIDE the declared 8-bit lookup, so the
/// range legs are all still satisfied and the only thing that can refuse is the multiply's algebra.
///
/// The schoolbook row refuses this because gate 0's ℤ body moves by `−p₀ ≠ 0` with `|p₀| < 2^8 < P`
/// — unconditional. The sz row refuses it because the forgery's residual polynomial is nonzero
/// (`PastaSzMul.fpHonest_quotient_bump_residual_nonzero` proves exactly this bump's residual has a
/// nonzero constant coefficient) and neither drawn challenge is one of its `≤ 62` roots — which is
/// `1 − 2^−197.0`, NOT a certainty. Both are asserted; only one of them is a theorem.
#[test]
fn the_multiply_forgery_is_refused_by_both_curve_rows() {
    let honest = trace(PALLAS_TRACE, RCB_WIDTH);

    let before = honest[0][MW_BASE];
    let after = bump_limb8(before);
    assert_ne!(before, after, "⚑ the falsifier must actually MOVE the cell");
    assert!(
        after.as_u32() < 256,
        "⚑ and land inside the declared 8-bit width, so the range lookup cannot be what refuses"
    );

    let mut forged = honest.clone();
    for row in forged.iter_mut() {
        row[MW_BASE] = bump_limb8(row[MW_BASE]);
    }

    for (label, json) in [("schoolbook", PALLAS_SOUND), ("sz", PALLAS_SZ)] {
        let d = desc(json);
        // sanity: the honest trace proves under this very descriptor, so the refusal below is the
        // tamper and not a broken fixture.
        prove_vm_descriptor2(&d, &honest, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("{label}: the honest trace must prove first: {e}"));
        // ⚑ UNCHECKED, deliberately: `prove_vm_descriptor2`'s producer-side pre-flight replay is a
        // Rust `assert` an adversary never runs. This entry puts the forged witness in front of the
        // CONSTRAINT SYSTEM, so the refusal below is the AIR's verdict and not the producer's.
        let err =
            prove_vm_descriptor2_unchecked(&d, &forged, &[], &MemBoundaryWitness::default(), &[])
                .err()
                .unwrap_or_else(|| {
                    panic!("{label}: a bumped quotient limb must be REFUSED by the AIR")
                });
        println!("§3 {label} curve row REFUSED the quotient forgery: {err}");
    }
}

/// The same tamper against the ALU pair, on the multiply row's quotient block.
#[test]
fn the_multiply_forgery_is_refused_by_both_alu_rows() {
    let honest = trace(ALU_TRACE, ALU_WIDTH);
    let before = honest[0][ALU_Q_BASE];
    let after = bump_limb8(before);
    assert_ne!(before, after, "⚑ the falsifier must actually MOVE the cell");
    assert!(after.as_u32() < 256, "⚑ inside the declared 8-bit width");

    let mut forged = honest.clone();
    forged[0][ALU_Q_BASE] = after;

    for (label, json) in [("schoolbook", ALU_SOUND), ("sz", ALU_SZ)] {
        let d = desc(json);
        prove_vm_descriptor2(&d, &honest, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("{label}: the honest trace must prove first: {e}"));
        let err =
            prove_vm_descriptor2_unchecked(&d, &forged, &[], &MemBoundaryWitness::default(), &[])
                .err()
                .unwrap_or_else(|| {
                    panic!("{label}: a bumped quotient limb must be REFUSED by the AIR")
                });
        println!("§3 {label} ALU row REFUSED the quotient forgery: {err}");
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §4 — the TWO-POINT form, on the bytes. The single-challenge form must never ship.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE ONE-GATE FORM IS BELOW THE BAR AND IS NOT WHAT SHIPPED.**
/// `PastaSzMul.sz_single_challenge_is_below_the_bar` is a `decide`d theorem that a single draw
/// unions across the 588 732-multiply wrap workload to `2^−98.5`, under this repo's ~124-bit bar.
/// So every artifact here must declare TWO challenges and carry an EVEN number of challenge gates,
/// paired one per draw — and both `permutation_randomness()` indices `0` and `1` must actually be
/// read. A descriptor that declared 1, or carried an odd count, or read only index 0, would be the
/// below-bar form and this test is what stops it reaching `by-name/`.
#[test]
fn every_sz_artifact_uses_the_two_point_form_and_never_the_single() {
    for (name, json, expected_gates) in [
        ("pallas complete-add", PALLAS_SZ, 24usize),
        ("vesta complete-add", VESTA_SZ, 24),
        ("fp ALU", ALU_SZ, 2),
        ("fq ALU", ALU_FQ_SZ, 2),
    ] {
        let d = desc(json);
        assert_eq!(
            d.challenges, 2,
            "{name}: the descriptor must DECLARE two challenges — one is below the bar"
        );
        let gates = chal_gates(&d);
        assert_eq!(gates.len(), expected_gates, "{name}: challenge-gate count");
        assert_eq!(
            gates.len() % 2,
            0,
            "{name}: the gates come in {{α, β}} pairs, one multiply per pair"
        );
        // Both declared indices are actually read: `check_descriptor2` already refuses a declared
        // count that disagrees with `max(chal_count)`, but that only pins the MAXIMUM. A body that
        // read index 1 twice and index 0 never would pass that check and be a single-point form.
        let mut reads_zero = 0usize;
        let mut reads_one = 0usize;
        for g in &gates {
            if let VmConstraint2::ChalGate(spec) = g {
                match spec.body.chal_count() {
                    1 => reads_zero += 1,
                    2 => reads_one += 1,
                    n => panic!("{name}: a chal_gate body reads {n} challenges; expected 1 or 2"),
                }
            }
        }
        assert_eq!(
            reads_zero, reads_one,
            "{name}: ⚑ the draws must be BALANCED — {reads_zero} gates at index 0 against \
             {reads_one} at index 1. An unbalanced count is a single-point form wearing a \
             two-gate declaration."
        );
        println!(
            "§4 {name}: {} chal_gates, challenges = {}",
            gates.len(),
            d.challenges
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §5 — the FAIL-CLOSED route refusal.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A CHALLENGE DESCRIPTOR CANNOT TAKE THE UNI-STARK ROUTE, and the refusal is at construction.**
/// A uni-stark instance has no lookup contexts and therefore no `permutation_randomness()`, so
/// `Ir2UniAir::new` refuses a `ChalGate` descriptor outright rather than proving it against an
/// empty challenge slice. That refusal is the reason the closure inside `Ir2UniAir::eval` — which
/// emits `assert_zero(ONE)` — is unreachable. Asserted here so that a future weakening of it reds
/// somewhere rather than silently evaluating an identity at the origin, which a prover satisfies
/// for free.
#[test]
fn a_challenge_descriptor_refuses_the_uni_stark_route() {
    for (name, json) in [("pallas complete-add", PALLAS_SZ), ("fp ALU", ALU_SZ)] {
        let d = desc(json);
        let err = Ir2UniAir::new(d)
            .err()
            .unwrap_or_else(|| panic!("{name}: uni-stark must REFUSE a chal_gate descriptor"));
        assert!(
            err.contains("chal_gate"),
            "{name}: the refusal must name the constraint kind, got: {err}"
        );
        println!("§5 {name} uni-stark REFUSED: {err}");
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// §6 — the COST, RE-DERIVED. Same binary, same box, same trace, both artifacts.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE MEASUREMENT, AND IT IS NOT THE "17%" ANYONE INHERITED.**
///
/// Four currencies, before and after, on the objects themselves:
///
/// * **constraints** — the recursion-visible count. This is where the win is.
/// * **declared columns** — unchanged, by construction.
/// * **committed columns** — unchanged. `MainLayout::build` appends a nibble-decomposition aux
///   block per declared range lookup, and Schwartz–Zippel removes no range lookup, so 71.7% of the
///   committed row is untouched.
/// * **LDE cells** — `padded_rows · 2^6 · committed_width`. Unchanged, because neither factor
///   moves. **This is the number that decides prover memory, and the sz collapse does not move it
///   by one cell.** Anyone selling sz as a trace-size fix is quoting the wrong currency.
///
/// Wall clock is printed, not asserted: it is one box on one day, and the assertions above are the
/// facts.
#[test]
fn the_cost_is_re_derived_on_the_real_objects() {
    println!("\n═══ THE CHEAP MULTIPLY: BEFORE / AFTER, SAME BINARY, SAME BOX, SAME TRACE ═══");
    println!(
        "{:<26} {:>7} {:>7} {:>9} {:>9} {:>13} {:>10} {:>10}",
        "artifact", "cons", "declW", "commitW", "rows", "LDE cells", "prove ms", "verify ms"
    );

    let cases: [(&str, &str, &str, usize); 6] = [
        ("pallas complete-add", PALLAS_SOUND, PALLAS_TRACE, RCB_WIDTH),
        ("pallas complete-add SZ", PALLAS_SZ, PALLAS_TRACE, RCB_WIDTH),
        ("vesta complete-add", VESTA_SOUND, VESTA_TRACE, RCB_WIDTH),
        ("vesta complete-add SZ", VESTA_SZ, VESTA_TRACE, RCB_WIDTH),
        ("fp ALU row", ALU_SOUND, ALU_TRACE, ALU_WIDTH),
        ("fp ALU row SZ", ALU_SZ, ALU_TRACE, ALU_WIDTH),
    ];

    let mut measured: Vec<(usize, usize, u64)> = Vec::new();
    for (name, json, text, width) in cases {
        let d = desc(json);
        let t = trace(text, width);
        let (p, v) = prove_verify(&d, &t).expect("both sides of the pair must prove");
        let cw = committed_width(&d);
        let lde = lde_cells(&d, t.len());
        measured.push((d.constraints.len(), cw, lde));
        println!(
            "{:<26} {:>7} {:>7} {:>9} {:>9} {:>13} {:>10.1} {:>10.1}",
            name,
            d.constraints.len(),
            d.trace_width,
            cw,
            t.len(),
            lde,
            p,
            v
        );
    }

    // The three pairs, as assertions rather than a printed table anyone can misread.
    for (i, label) in [(0usize, "pallas"), (2, "vesta"), (4, "fp ALU")] {
        let (c_before, w_before, l_before) = measured[i];
        let (c_after, w_after, l_after) = measured[i + 1];
        assert!(
            c_after < c_before,
            "{label}: the sz row must have FEWER constraints"
        );
        assert_eq!(
            w_after, w_before,
            "{label}: ⚑ committed width MUST NOT move — that is the honest boundary of the win"
        );
        assert_eq!(
            l_after, l_before,
            "{label}: ⚑ and neither may the LDE domain"
        );
        println!(
            "{label}: constraints {c_before} → {c_after} (−{}), committed width {w_before} → \
             {w_after} (0), LDE cells {l_before} → {l_after} (0)",
            c_before - c_after
        );
    }
    println!(
        "\n⚑ The currency that moved is ALGEBRAIC GATES and MULTIPLICATION NODES, not memory.\n\
         ⚑ In the emitted bodies: 2 206 → 442 multiplication nodes per multiply \
         (PastaSzMul.sz_arithmetic_ratio), 12 × that on the curve row, and at \
         MinaWrapVerifierAir.WRAP_MULS = 588 732 that is 1.04e9 multiplication nodes removed \
         from the wrap verifier's per-row constraint evaluation — and ZERO committed cells."
    );
}
