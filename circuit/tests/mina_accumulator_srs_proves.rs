//! # `dregg-mina-accumulator-srs::v1` — **the declared addends are `−s_r · G_r`, and a table that
//! merely DISCHARGES is refused.**
//!
//! ## What this file is the tooth for
//!
//! `mina_accumulator_routing_proves.rs` closed the rung below: row `i`'s addend cells ARE the
//! descriptor's declared addend `i`, so a prover holding a fixed descriptor cannot choose them. It
//! said, in its own words, what that did not buy — *"scaling is still unrouted; nothing says the
//! declared addends are `−s_r·G_r`"* — because `MinaAccumulatorAir.accRoutedDesc` takes the addend
//! list as a FREE PARAMETER and will emit any 97-wide table it is handed.
//!
//! `MinaAccumulatorAir` §10 removes the parameter. `srsScaledAddends Gs u⃗ n` is a TOTAL FUNCTION of
//! a generator list and the bulletproof challenges whose `r`-th entry is `−s_r · G_r`, with
//! `s_r = b_poly_coefficients(u⃗)_r` and the scalar multiplication run by the same complete formula
//! the AIR row computes. `accSrsDesc` is that descriptor. Its ALGEBRA is `-routed`'s verbatim —
//! same 4 831 constraints, same 3 049 columns, same selector census — so every forcing theorem of
//! §5–§8 applies unchanged, and the only thing that differs is what the manifest is a function of.
//!
//! ## ⚑ THE PAIR, AND THE OLD-ADMITS POLE IS THE PREVIOUS RUNG'S OWN HONEST ARTIFACT
//!
//! `mina-accumulator-routed-trace.txt` is a chain of eight genuine `rcbSoundRow`s whose threads
//! hold, whose accumulator VANISHES, and whose addends are seven copies of the Vesta generator and
//! a closing negation. It is internally consistent, it discharges, and it is **not anybody's scalar
//! multiples** — which is exactly the forgery `accumulator_discharge_forced_on_declared_addends`
//! admits. It PROVES under `-routed` (whose manifest declares it) and is REFUSED under `-srs`, by
//! the balance of `mina_accumulator_addends` and by nothing else.
//!
//! No forgery fixture was written for this file. The falsifier is the previous rung's deliverable.
//!
//! ## ⚑ AND THE MANIFEST IS CERTIFIED AGAINST THE PINNED BLOB, NOT AGAINST ITSELF
//!
//! `the_declared_manifest_is_the_pinned_srs_scaled_by_the_challenges` recomputes every declared
//! addend NATIVELY — `dregg_bridge::mina_accumulator_discharge::vesta_srs_g` (which re-checks the
//! sha256 `f28a8a91…` and every one of the 65 536 generators on `y² = x³ + 5` over `q` before
//! returning a byte), then `pasta_msm::b_poly_coefficients_at` at the Vesta SCALAR prime and
//! `pasta_msm::scalar_mul_at` at the Vesta BASE prime — and compares projectively.
//!
//! ⚠ **PROJECTIVELY, and that is the correct notion, not a weakening.** The Lean derivation is
//! LSB-first double-and-add; `scalar_mul_at` is MSB-first. Two correct implementations reach
//! different projective REPRESENTATIVES of the same point, and the AIR's chain is projective, so
//! `proj_eq_at` is what "the declared addend is `−s_r·G_r`" means. `on_curve_at` and `Z ≠ 0` are
//! asserted alongside so the comparison cannot be satisfied by an off-curve triple or by the
//! degenerate `Z = 0` case where cross-multiplication says nothing.
//!
//! ⚠ **This is a CONSUMER certification, not a differential twin.** Lean AUTHORS the manifest;
//! this is the check a node performs to decide the descriptor belongs to the block. That it costs
//! `n` native scalar multiplications is the whole residual, and `MinaAccumulatorAir` §10's docblock
//! is where it is written down at full resolution.
//!
//! ## What still is not closed, said here as well as there
//!
//! The derivation runs in the EMITTER. Nothing in this AIR forces the manifest to be the image of
//! `u⃗`; the verifier rebuilds the manifest from descriptor bytes and never re-runs the function. So
//! the scaling relation lives in the circuit (the deferred MSM), in the emitter (here), or nowhere
//! (the rung below) — and there is no fourth place. What moved is the object a certifier checks:
//! from `n` arbitrary Vesta points to `|u⃗|` field elements and a byte-pinned blob.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_accumulator_srs_proves -- --nocapture`
//! ⚠ RELEASE. In debug a lookup refusal is a p3 `#[cfg(debug_assertions)]` panic rather than a
//! clean `Err`, and the release verdict carries the bus name this file asserts on.

use dregg_bridge::mina_accumulator_discharge::vesta_srs_g;
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::pasta_msm::{
    PastaCurve, b_poly_coefficients_at, on_curve_at, proj_eq_at, scalar_mul_at, sub_mod,
};
use dregg_circuit::pasta_windowed_witness::{Pt, U256};
use dregg_circuit::refusal::{
    assert_bus_imbalance_not_constraint, assert_violated_constraint_not_bus,
    must_refuse_or_unsat_panic,
};

// -------------------------------------------------------------------------------------------
// The artifacts. All four are Lean-emitted; nothing here is authored.
// -------------------------------------------------------------------------------------------

const SRS_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-srs.json");
const ROUTED_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-routed.json");

/// The honest SRS chain: `acc_0 = C = Σ s_r·G_r`, eight addends `−s_r·G_r`, terminal `O`.
const SRS_TRACE: &str = include_str!("fixtures/mina-accumulator-srs-trace.txt");
/// ⚑ The OLD-ADMITS pole — the routing rung's own honest artifact.
const ROUTED_TRACE: &str = include_str!("fixtures/mina-accumulator-routed-trace.txt");
/// The certification inputs: three challenge decimals, then the routed generator indices.
const SRS_PARAMS: &str = include_str!("fixtures/mina-accumulator-srs-params.txt");

// -------------------------------------------------------------------------------------------
// Layout — every constant a mirror of a Lean name, none of them re-derived here.
// -------------------------------------------------------------------------------------------

const WIDTH: usize = 3048; // PastaCurveSound.RCB_WIDTH
const ROUTED_WIDTH: usize = WIDTH + 1; // MinaAccumulatorAir.ROUTED_WIDTH
const ROWS: usize = 8;
const SK: usize = 32; // PastaFieldSound.SK
const ACC: [usize; 3] = [0, SK, 2 * SK];
const ADD_X: usize = 3 * SK; // 96
const OUT: [usize; 3] = [1024, 1120, 1216];
const PI_COUNT: usize = 6 * SK; // 192
const ADDEND_TUP: usize = 1 + 3 * SK; // 97
const ADDEND_TID: usize = 133; // .custom 128 ⇒ wireId 133
const ADDEND_BUS: &str = "ir2_exact_public_a97";
const ROUTED_CONSTRAINTS: usize = 4476 + 96 + 192 + 64 + 3; // 4831

const SRS_NAME: &str = "dregg-mina-accumulator-srs::v1";
const ROUTED_NAME: &str = "dregg-mina-accumulator-routed::v1";

// -------------------------------------------------------------------------------------------
// Readers.
// -------------------------------------------------------------------------------------------

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the AIR")
}

/// Raw decimal cells, so the hygiene assertions below read the FIXTURE rather than a felt.
fn cells(text: &str) -> Vec<Vec<u64>> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| c.parse::<u64>().expect("decimal cell"))
                .collect()
        })
        .collect()
}

fn trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let cells: Vec<BabyBear> = l
                .split_whitespace()
                .map(|c| {
                    BabyBear::new(
                        u32::try_from(c.parse::<u64>().expect("decimal cell"))
                            .expect("cell inside BabyBear"),
                    )
                })
                .collect();
            assert_eq!(cells.len(), width, "every row is exactly {width} wide");
            cells
        })
        .collect();
    assert_eq!(rows.len(), ROWS, "the base trace is {ROWS} rows");
    rows
}

/// PIs are READ OFF the trace, never authored: row 0's three `ACC` blocks then row 7's three `OUT`
/// blocks. Same derivation the routing rung uses, so a PI difference between the two traces can
/// never be what separates them.
fn public_inputs(t: &[Vec<BabyBear>]) -> Vec<BabyBear> {
    let mut pis = Vec::with_capacity(PI_COUNT);
    for base in ACC {
        for i in 0..SK {
            pis.push(t[0][base + i]);
        }
    }
    for base in OUT {
        for i in 0..SK {
            pis.push(t[ROWS - 1][base + i]);
        }
    }
    assert_eq!(pis.len(), PI_COUNT);
    pis
}

fn declared_manifest(d: &EffectVmDescriptor2) -> Vec<Vec<u32>> {
    let table = d
        .tables
        .iter()
        .find(|t| t.id == ADDEND_TID)
        .expect("the descriptor declares the addend manifest");
    assert_eq!(table.arity, ADDEND_TUP);
    match &table.sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("the addend table is not exact-public: {other:?}"),
    }
}

/// The three challenges, as emitted.
fn challenges() -> Vec<U256> {
    SRS_PARAMS
        .lines()
        .filter(|l| !l.trim().is_empty())
        .take(3)
        .map(|l| U256::from_dec(l.trim()))
        .collect()
}

/// The generator indices this manifest routes, as emitted.
fn generator_indices() -> Vec<usize> {
    SRS_PARAMS
        .lines()
        .filter(|l| !l.trim().is_empty())
        .nth(3)
        .expect("the params fixture carries the index line")
        .split_whitespace()
        .map(|s| s.parse::<usize>().expect("decimal index"))
        .collect()
}

/// A manifest row's 96 limbs read back as a projective point. The limbs are base-`2^8` digits in
/// `X ‖ Y ‖ Z` order — `MinaAccumulatorAir.coordLimb`'s own layout, and the same order the trace's
/// `ADD_X/ADD_Y/ADD_Z` blocks sit in.
fn point_of_row(row: &[u32]) -> Pt {
    assert_eq!(row.len(), ADDEND_TUP);
    let coord = |block: usize| -> U256 {
        let mut words = [0u64; 4];
        for j in 0..SK {
            let limb = row[1 + block * SK + j];
            assert!(limb < 256, "a manifest limb is not an 8-bit digit: {limb}");
            words[j / 8] |= u64::from(limb) << (8 * (j % 8));
        }
        U256(words)
    };
    Pt {
        x: coord(0),
        y: coord(1),
        z: coord(2),
    }
}

fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

// -------------------------------------------------------------------------------------------
// §1 — SHAPE. What this file reads is what the artifact declares.
// -------------------------------------------------------------------------------------------

#[test]
fn the_srs_artifact_declares_what_this_file_reads() {
    let d = descriptor(SRS_JSON);
    assert_eq!(d.name, SRS_NAME);
    assert_eq!(d.trace_width, ROUTED_WIDTH);
    assert_eq!(d.public_input_count, PI_COUNT);
    assert_eq!(d.constraints.len(), ROUTED_CONSTRAINTS);

    let manifest = declared_manifest(&d);
    assert_eq!(manifest.len(), ROWS, "one declared addend per trace row");
    for (i, row) in manifest.iter().enumerate() {
        assert_eq!(row.len(), ADDEND_TUP);
        assert_eq!(
            row[0],
            u32::try_from(i + 1).unwrap(),
            "the key is the row index plus one"
        );
    }
    println!("-srs: {ROUTED_WIDTH} cols, {ROUTED_CONSTRAINTS} constraints, {ROWS} manifest rows");
}

/// ⚑ **THE ALGEBRA IS THE SAME OBJECT AND THE MANIFEST IS NOT.** If these two ever agreed on the
/// manifest the pair below would prove nothing; if they ever disagreed on the constraints, `-srs`
/// would be a different circuit and §5–§8's forcing theorems would not transfer to it.
#[test]
fn the_two_descriptors_share_an_algebra_and_differ_in_their_manifest() {
    let srs = descriptor(SRS_JSON);
    let routed = descriptor(ROUTED_JSON);

    assert_ne!(srs.name, routed.name);
    assert_eq!(routed.name, ROUTED_NAME);
    assert_eq!(srs.constraints, routed.constraints, "same algebra");
    assert_eq!(srs.trace_width, routed.trace_width);
    assert_eq!(srs.public_input_count, routed.public_input_count);
    assert_eq!(
        srs.tables.iter().map(|t| t.id).collect::<Vec<_>>(),
        routed.tables.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    assert_ne!(
        declared_manifest(&srs),
        declared_manifest(&routed),
        "the two manifests must not agree — the whole pair rests on it"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — ⚑⚑ THE CERTIFICATION. The declared table IS the pinned SRS scaled by the challenges.
// -------------------------------------------------------------------------------------------

/// ⚠ A degenerate challenge would make the derivation's falsifier blind: at `u_k = 1` a
/// `b_poly_coefficients` that dropped that challenge entirely is invisible, and at `u_k = 0` half
/// the coefficients collapse to zero and half the addends to `O`. The first draft of `demoChals`
/// derived its values from `PastaCurve.Gv` and the first one came out as **exactly `1`**. This is
/// the guard that catches it.
#[test]
fn the_demo_challenges_are_not_degenerate() {
    let chals = challenges();
    let scalar = PastaCurve::Vesta.scalar();
    assert_eq!(chals.len(), 3, "2^3 = 8 coefficients tile the eight rows");
    for (k, c) in chals.iter().enumerate() {
        assert!(
            *c < scalar,
            "challenge {k} is not reduced at the Vesta scalar prime"
        );
        assert!(
            *c > U256::from_u64(1),
            "challenge {k} is degenerate: {}",
            c.to_dec()
        );
    }
    assert_ne!(chals[0], chals[1]);
    assert_ne!(chals[1], chals[2]);
    assert_ne!(chals[0], chals[2]);
}

/// ⚑⚑ **THE DELIVERABLE, MEASURED.** Every declared addend is `−s_r · G_r` with `G_r` the
/// sha-pinned SRS generator at index `r` and `s_r = b_poly_coefficients(u⃗)_r`, recomputed by the
/// DEPLOYED native arithmetic and compared projectively, on-curve, with `Z ≠ 0`.
#[test]
fn the_declared_manifest_is_the_pinned_srs_scaled_by_the_challenges() {
    let base = PastaCurve::Vesta.base();
    let scalar = PastaCurve::Vesta.scalar();

    // The pinned blob. `vesta_srs_g(0)` re-checks the sha256 AND every one of the 65 536
    // generators on `y² = x³ + 5` over `q` before returning.
    let g = vesta_srs_g(0).expect("the pinned Vesta SRS must load and be on-curve");
    assert_eq!(g.len(), 65_536);

    let chals = challenges();
    let idx = generator_indices();
    assert_eq!(
        idx,
        (0..ROWS).collect::<Vec<_>>(),
        "the demo routes G_0..G_7"
    );

    let s = b_poly_coefficients_at(&scalar, &chals);
    assert_eq!(s.len(), 1 << chals.len());

    let manifest = declared_manifest(&descriptor(SRS_JSON));
    assert_eq!(manifest.len(), ROWS);

    for (r, row) in manifest.iter().enumerate() {
        let declared = point_of_row(row);

        // The native answer: −s_r · G_r.
        let scaled = scalar_mul_at(&base, &s[r], &g[idx[r]]);
        let expect = Pt {
            x: scaled.x,
            y: sub_mod(&base, &U256::ZERO, &scaled.y),
            z: scaled.z,
        };

        assert!(
            s[r] != U256::ZERO,
            "row {r}: the scalar is zero, so the addend carries no information"
        );
        assert!(
            declared.z != U256::ZERO,
            "row {r}: the declared addend is at infinity, where projective equality says nothing"
        );
        assert!(
            on_curve_at(&base, &declared),
            "row {r}: the declared addend is not on Vesta"
        );
        assert!(
            proj_eq_at(&base, &declared, &expect),
            "row {r}: the declared addend is NOT −s_r·G_r\n  declared x={}\n  expected x={}",
            declared.x.to_dec(),
            expect.x.to_dec()
        );
    }
    println!("all {ROWS} declared addends certified as −s_r·G_r against the sha-pinned SRS");
}

/// …and the certification is REFUTABLE: the rung below's manifest fails it. Without this the test
/// above could be passing because `proj_eq_at` accepts everything.
#[test]
fn the_routed_rungs_manifest_fails_the_same_certification() {
    let base = PastaCurve::Vesta.base();
    let scalar = PastaCurve::Vesta.scalar();
    let g = vesta_srs_g(256).expect("the pinned Vesta SRS must load");
    let s = b_poly_coefficients_at(&scalar, &challenges());

    let manifest = declared_manifest(&descriptor(ROUTED_JSON));
    let mut agreeing = 0usize;
    for (r, row) in manifest.iter().enumerate() {
        let declared = point_of_row(row);
        let scaled = scalar_mul_at(&base, &s[r], &g[r]);
        let expect = Pt {
            x: scaled.x,
            y: sub_mod(&base, &U256::ZERO, &scaled.y),
            z: scaled.z,
        };
        if proj_eq_at(&base, &declared, &expect) {
            agreeing += 1;
        }
    }
    assert_eq!(
        agreeing, 0,
        "the routed rung's declared table passed the scalar-multiple certification — \
         the certification is not discriminating"
    );
}

// -------------------------------------------------------------------------------------------
// §3 — THE POLARITIES.
// -------------------------------------------------------------------------------------------

/// The honest SRS chain proves. Both rails: the adversarial one (so the tooth below is measured
/// against a prover that CAN emit a bad trace) and the checked one (so the producer's pre-flight is
/// exercised on the honest side rather than only on the forged one).
#[test]
fn the_srs_chain_proves() {
    let d = descriptor(SRS_JSON);
    let t = trace(SRS_TRACE, ROUTED_WIDTH);
    let pis = public_inputs(&t);

    prove_and_verify_adversarial(&d, &t, &pis).expect("the honest SRS chain proves and verifies");

    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest SRS chain passes the producer pre-flight");
    verify_vm_descriptor2(&d, &proof, &pis).expect("…and verifies");
}

/// The old-admits pole, restated here so the pair is one file's claim: the routing rung's honest
/// chain still proves under its OWN descriptor. If this ever went red the tooth below would be
/// measuring a broken fixture rather than a manifest disagreement.
#[test]
fn the_routed_chain_still_proves_under_its_own_descriptor() {
    let d = descriptor(ROUTED_JSON);
    let t = trace(ROUTED_TRACE, ROUTED_WIDTH);
    let pis = public_inputs(&t);
    prove_and_verify_adversarial(&d, &t, &pis).expect("the routed chain proves under -routed");
}

/// ⚑⚑ **THE TOOTH.** A table that is internally consistent, whose every row is a genuine sound RCB
/// row, whose threads hold, whose index column is threaded, and whose accumulator VANISHES — and
/// which is not this block's scalar multiples — is REFUSED by the AIR.
///
/// ⚠ It is refused by the LogUp balance, and the assertion is inverted on purpose:
/// `assert_bus_imbalance_not_constraint`. A constraint verdict here would mean the forgery was not
/// the all-gates-satisfied case and the exhibit would be measuring the wrong thing.
///
/// ⚠ And it is the AIR's refusal, not a producer assert: the trace goes in through
/// `prove_vm_descriptor2_unchecked`, which bypasses `build_traces`' multiset replay entirely.
#[test]
fn a_table_that_discharges_and_is_not_the_scalar_multiples_is_refused() {
    let d = descriptor(SRS_JSON);
    let t = trace(ROUTED_TRACE, ROUTED_WIDTH);
    let pis = public_inputs(&t);

    let what = "a discharging chain whose addends are not −s_r·G_r, under -srs";
    let refusal = must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&d, &t, &pis));
    let reason = refusal.reason();
    assert_bus_imbalance_not_constraint(what, &reason);
    assert!(
        reason.contains(ADDEND_BUS),
        "the refusal must name the addend manifest's own bus ({ADDEND_BUS}); got: {reason}"
    );
    println!("refused by: {reason}");
}

/// The producer's pre-flight ALSO refuses it, and that is explicitly not the tooth — it is a Rust
/// `assert` in `build_traces`, one rail above the circuit. Named so nobody later reads the tooth
/// above as this.
#[test]
fn the_producer_preflight_also_refuses_and_that_is_not_the_tooth() {
    let d = descriptor(SRS_JSON);
    let t = trace(ROUTED_TRACE, ROUTED_WIDTH);
    let pis = public_inputs(&t);

    let err = match prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[]) {
        Ok(_) => panic!("the producer pre-flight ACCEPTED the substituted table"),
        Err(e) => e,
    };
    assert!(
        err.contains("lookup multiset does not equal its"),
        "the pre-flight refusal is the multiset replay; got: {err}"
    );
}

// -------------------------------------------------------------------------------------------
// §4 — FALSIFIER HYGIENE. What moved, that it is nonzero, and that it is inside its width.
// -------------------------------------------------------------------------------------------

/// ⚑ The two traces differ in their ADDEND blocks, the moved values are NONZERO, and every moved
/// cell is inside the declared 8-bit limb width — so no range lookup can be what refuses, and
/// nothing here is a falsifier that moved a zero into a zero.
#[test]
fn the_falsifier_moves_nonzero_values_inside_their_width() {
    let honest = cells(SRS_TRACE);
    let forged = cells(ROUTED_TRACE);

    let mut moved = 0usize;
    let mut moved_nonzero = 0usize;
    for r in 0..ROWS {
        for j in 0..3 * SK {
            let a = honest[r][ADD_X + j];
            let b = forged[r][ADD_X + j];
            assert!(a < 256, "honest addend limb outside the 8-bit width: {a}");
            assert!(b < 256, "forged addend limb outside the 8-bit width: {b}");
            if a != b {
                moved += 1;
                if a != 0 && b != 0 {
                    moved_nonzero += 1;
                }
            }
        }
    }
    assert!(moved > 0, "the two traces agree on every addend limb");
    assert!(
        moved_nonzero > 0,
        "every moved addend limb had a zero on one side — the falsifier moved a zero into a zero"
    );
    println!("{moved} addend limbs moved, {moved_nonzero} of them nonzero on BOTH sides");
}

/// ⚑ …and the index column is identical in the two traces, so the routing KEY is not what
/// separates them: the tuples collide on their key and differ in their payload, which is the case
/// `addend_manifest_key_unique` turns a multiset membership into a pointwise statement for.
#[test]
fn the_row_index_column_is_the_same_in_both_traces() {
    let honest = cells(SRS_TRACE);
    let forged = cells(ROUTED_TRACE);
    for r in 0..ROWS {
        assert_eq!(
            honest[r][WIDTH], forged[r][WIDTH],
            "the row-index column differs at row {r}"
        );
        assert_eq!(honest[r][WIDTH], u64::try_from(r).unwrap());
    }
}

/// ⚑ The bus is not refusing everything. (1) The honest chain balances it. (2) An arithmetically
/// dishonest edit — one addend limb bumped by one, inside its width — is caught by a GATE, not by
/// the bus, so the two refusal kinds are distinguishable and neither is swallowing the other.
#[test]
fn the_bus_is_not_refusing_everything_and_is_not_the_only_refusal() {
    let d = descriptor(SRS_JSON);
    let t = trace(SRS_TRACE, ROUTED_WIDTH);
    let pis = public_inputs(&t);
    prove_and_verify_adversarial(&d, &t, &pis).expect("(1) the honest chain balances the bus");

    let before = cells(SRS_TRACE)[3][ADD_X];
    assert!(
        before + 1 < 256,
        "the bump stays inside the 8-bit limb width"
    );
    let mut bumped = t.clone();
    bumped[3][ADD_X] = BabyBear::new(u32::try_from(before + 1).unwrap());

    let what = "one addend limb bumped by one";
    let refusal =
        must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&d, &bumped, &pis));
    assert_violated_constraint_not_bus(what, &refusal.reason());
}
