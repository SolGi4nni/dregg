//! # `dregg-mina-wrap-closing-*::v1` — **the IPA closing check, in a circuit, and the free-`sg`
//! forgery refused by the AIR.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** All three descriptors are `EffectLower.lowerAir` of
//! `Dregg2.Circuit.Emit.MinaWrapClosingAir.{closingFinalAir, closingRoutedAirOn}`, and every trace
//! below is `PastaCurveSound.rcbSoundRow` rendered by `metatheory/EmitMinaWrapClosing.lean`.
//! Nothing in this file authors a constraint, a `Builder` gadget or an `air_accepts` predicate: it
//! parses emitted bytes, fills cells, and calls the deployed prover and the deployed verifier.
//!
//! ## ⚑⚑ WHAT THIS FILE IS THE TOOTH FOR
//!
//! `MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` and
//! `PastaIpaDeferral.opening_is_vacuous_when_sg_is_free` are two `#assert_axioms`-gated theorems
//! that the IPA closing check `c·Q + delta = z₁·(sg + b₀·U) + z₂·H` **accepts at every value of
//! everything else while `sg` is a free witness** — the prover simply solves for `sg`.
//! `pinned_sg_makes_the_opening_refute` is the pole that keeps that from being a tautology.
//!
//! `MinaWrapClosingAir` brings in the leg upstream actually uses. `poly-commitment/src/ipa.rs`
//! folds the `sg` binding into the SAME terminal MSM with an independent randomiser: the `sg` base
//! carries `neg_rand_base_i * z1 - sg_rand_base_i` (`:410-411`) and the SRS bases carry
//! `+ sg_rand_base_i · s_i` (`:413-425`). **At `sg_rand_base = −z₁·rand_base` that coefficient is
//! exactly zero and `sg` leaves the equation.** `the_combined_check_is_constant_in_sg` is that as a
//! theorem and `the_eliminated_check_is_the_conjunction` is why it is not a weakening: the
//! eliminated residual vanishes iff there EXISTS an `sg` satisfying both statements together.
//!
//! ## THE PAIR, AND THE FALSIFIER IS THE FORGERY THE VACUITY THEOREM NAMES
//!
//! The emitter constructs the prover that theorem describes. `SG_FORGED` is a real Pallas point
//! that is not `⟨s, G⟩`; `DELTA_FORGED` is the `delta` that makes his chain close.
//!
//! * `free-sg` — his chain in the UN-ELIMINATED shape, four addends with `−z₁·sg*` among them. It
//!   VANISHES, every row is a genuine `rcbSoundRow`, every thread holds, the terminal `X`/`Z`
//!   blocks are canonically zero. ⚑ **It PROVES under `-final`.** That is the vacuity as a STARK
//!   proof rather than as a theorem about a model, and it is why `-final` alone is not the answer.
//! * `free-sg-routed` — the SAME prover's own data through the ELIMINATED manifest, where there is
//!   no `sg` slot. His chain lands on `z₁·(sg* − ⟨s,G⟩) ≠ O`. **REFUSED, by a `.last` discharge
//!   gate on a terminal limb** — `assert_violated_constraint_not_bus`, so the refusal is the
//!   intended algebraic constraint and not a LogUp imbalance and not a range lookup.
//! * `bound` / `bound-routed` — the honest pair at the same shape and the same row count, `delta`
//!   derived from the TRUE `⟨s, G⟩`. Both prove. Without them the refusal above would be evidence
//!   that the descriptor accepts nothing.
//!
//! ⚠ **THE REFUSAL MUST BE THE AIR'S.** `prove_vm_descriptor2` runs a producer pre-flight that
//! replays the exact-public multiset in Rust and fires BEFORE any constraint is evaluated, so a
//! routed forgery would refuse there with a message about a manifest and the AIR would never be
//! asked. Every refusal tooth here goes through `prove_vm_descriptor2_unchecked` +
//! `verify_vm_descriptor2`, which is the only path on which the constraint system is what speaks.
//!
//! ⚠ **THE DEMONSTRATION IS AT FIVE SRS GENERATORS, NOT `2^15`.** Three group terms plus five
//! scaled generators is eight rows, a legal power-of-two base height. The full-width chain is a
//! FOLD of segments and nothing here is evidence about `2^15`.
//!
//! ## ⚑⚑ AND WHERE THE FREE WITNESS MOVED TO — named here, not left to be found
//!
//! `delta` is a DECLARED manifest slot and a prover-supplied group element, and nothing in this AIR
//! binds it to a transcript. So a prover who may choose `delta` freely satisfies the eliminated
//! check at every value of everything else — the emitter's own `deltaFor` is that choice. **That is
//! a free witness of the same SHAPE as the one this file retires.**
//!
//! It is not the same HOLE. `sg`'s binding is ALGEBRAIC — `sg = ⟨s, srs.g⟩`, a relation inside the
//! closing equation that nothing in dregg discharged — and it is closed here by elimination.
//! `delta`'s binding is FIAT–SHAMIR: `SRS::verify` absorbs it into the sponge before squeezing `c`,
//! so it lives in the transcript, which is `MinaWrapOpeningGate` §3 and `MinaAccumulatorAir`'s
//! residual 2 — open before this file and open after it. **This AIR refutes a free `sg` and does
//! NOT refute a free `delta`.**
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_wrap_closing_air_proves -- --nocapture`
//! ⚠ RELEASE is load-bearing: in debug an algebraic refusal is a p3 `#[cfg(debug_assertions)]`
//! panic rather than a clean `Err`, and the release verdict carries the constraint name asserted on.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::descriptor_ir2::{ProofBindSpec, VmConstraint2};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::effect_vm::key_limbs9;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};

// -------------------------------------------------------------------------------------------
// The artifacts. All Lean-emitted; nothing here is authored.
// -------------------------------------------------------------------------------------------

const FINAL_JSON: &str = include_str!("fixtures/mina-wrap-closing-final.json");
const SRS_JSON: &str = include_str!("fixtures/mina-wrap-closing-srs.json");
const SRS_FORGED_JSON: &str = include_str!("fixtures/mina-wrap-closing-srs-forged.json");

const BOUND_TRACE: &str = include_str!("fixtures/mina-wrap-closing-bound-trace.txt");
const BOUND_ROUTED_TRACE: &str = include_str!("fixtures/mina-wrap-closing-bound-routed-trace.txt");
const FREE_SG_TRACE: &str = include_str!("fixtures/mina-wrap-closing-free-sg-trace.txt");
const FREE_SG_ROUTED_TRACE: &str =
    include_str!("fixtures/mina-wrap-closing-free-sg-routed-trace.txt");
const PARAMS: &str = include_str!("fixtures/mina-wrap-closing-params.txt");

// -------------------------------------------------------------------------------------------
// Layout — every constant a mirror of a Lean name, none re-derived here.
// -------------------------------------------------------------------------------------------

const WIDTH: usize = 3048; // PastaCurveSound.RCB_WIDTH
const ROUTED_WIDTH: usize = WIDTH + 1; // MinaAccumulatorAir.ROUTED_WIDTH
const SK: usize = 32; // PastaFieldSound.SK
const ACC: [usize; 3] = [0, SK, 2 * SK];
const OUT: [usize; 3] = [1024, 1120, 1216]; // PastaLadderThread.out_bases_eq
const PI_COUNT: usize = 6 * SK; // MinaAccumulatorAir.ACC_PI_COUNT
const ADDEND_TUP: usize = 1 + 3 * SK; // 97
const ADDEND_TID: usize = 133; // .custom 128 ⇒ wireId 133
const FINAL_CONSTRAINTS: usize = 4476 + 96 + 192 + 64; // 4828
const ROUTED_CONSTRAINTS: usize = FINAL_CONSTRAINTS + 3; // 4831

/// Three group terms plus five scaled generators.
const ROUTED_ROWS: usize = 8;
/// The un-eliminated chain: `delta*`, `−z₁·sg*`, `−(z₁b₀)·U`, `−z₂·H`.
const FREE_SG_ROWS: usize = 4;

const FINAL_NAME: &str = "dregg-mina-wrap-closing-final::v1";
const SRS_NAME: &str = "dregg-mina-wrap-closing-srs::v1";

// -------------------------------------------------------------------------------------------
// Readers.
// -------------------------------------------------------------------------------------------

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the AIR")
}

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

fn trace(text: &str, width: usize, rows: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let row: Vec<BabyBear> = l
                .split_whitespace()
                .map(|c| {
                    BabyBear::new(
                        u32::try_from(c.parse::<u64>().expect("decimal cell"))
                            .expect("cell inside BabyBear"),
                    )
                })
                .collect();
            assert_eq!(row.len(), width, "every row is exactly {width} wide");
            row
        })
        .collect();
    assert_eq!(t.len(), rows, "this trace is {rows} rows");
    t
}

/// PIs are READ OFF the trace, never authored: row 0's three `ACC` blocks (`c·Q`) then the last
/// row's three `OUT` blocks. Same derivation for every trace, so a PI difference can never be what
/// separates two of them.
fn public_inputs(t: &[Vec<BabyBear>]) -> Vec<BabyBear> {
    let last = t.len() - 1;
    let mut pis = Vec::with_capacity(PI_COUNT);
    for base in ACC {
        for i in 0..SK {
            pis.push(t[0][base + i]);
        }
    }
    for base in OUT {
        for i in 0..SK {
            pis.push(t[last][base + i]);
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

/// A SMALL scalar from the emitter's parameter dump, keyed by its first token.
///
/// ⚠ Only for the small ones (`ngen`, `c`, `z1`, `z2`, `b0`). Coordinates are 255-bit decimals and
/// have no `u64` reading — [`param_point`] keeps those as text, so a coordinate can never be
/// silently truncated into an assertion that then passes.
fn param_small(name: &str) -> Vec<u64> {
    PARAMS
        .lines()
        .find(|l| l.split_whitespace().next() == Some(name))
        .unwrap_or_else(|| panic!("the params fixture carries `{name}`"))
        .split_whitespace()
        .skip(1)
        .map(|s| {
            s.parse::<u64>()
                .unwrap_or_else(|_| panic!("`{name}` is not a small scalar: {s}"))
        })
        .collect()
}

/// The raw decimal coordinates of a named point in the parameter dump.
fn param_point(name: &str) -> Vec<String> {
    PARAMS
        .lines()
        .find(|l| l.split_whitespace().next() == Some(name))
        .unwrap_or_else(|| panic!("the params fixture carries `{name}`"))
        .split_whitespace()
        .skip(1)
        .map(std::string::ToString::to_string)
        .collect()
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
// §1 — SHAPE.
// -------------------------------------------------------------------------------------------

#[test]
fn the_closing_artifacts_declare_what_this_file_reads() {
    let f = descriptor(FINAL_JSON);
    assert_eq!(f.name, FINAL_NAME);
    assert_eq!(f.trace_width, WIDTH);
    assert_eq!(f.public_input_count, PI_COUNT);
    assert_eq!(f.constraints.len(), FINAL_CONSTRAINTS);

    for json in [SRS_JSON, SRS_FORGED_JSON] {
        let d = descriptor(json);
        assert_eq!(d.name, SRS_NAME);
        assert_eq!(d.trace_width, ROUTED_WIDTH);
        assert_eq!(d.public_input_count, PI_COUNT);
        assert_eq!(d.constraints.len(), ROUTED_CONSTRAINTS);
        let m = declared_manifest(&d);
        assert_eq!(m.len(), ROUTED_ROWS, "one declared addend per trace row");
        for (i, row) in m.iter().enumerate() {
            assert_eq!(row.len(), ADDEND_TUP);
            assert_eq!(
                row[0],
                u32::try_from(i + 1).unwrap(),
                "key is row index + 1"
            );
        }
    }
    println!(
        "-final: {WIDTH} cols / {FINAL_CONSTRAINTS} constraints; \
         -srs: {ROUTED_WIDTH} cols / {ROUTED_CONSTRAINTS} constraints / {ROUTED_ROWS} manifest rows"
    );
}

/// ⚑ **THE ALGEBRA IS THE SAME OBJECT AND THE MANIFEST IS NOT.** The honest and the forged `-srs`
/// descriptors are the SAME circuit; what differs is the `delta` slot, which is the prover's own
/// proof datum. If they ever agreed on the manifest the pair below would prove nothing.
#[test]
fn the_two_srs_descriptors_share_an_algebra_and_differ_in_one_slot() {
    let honest = descriptor(SRS_JSON);
    let forged = descriptor(SRS_FORGED_JSON);

    assert_eq!(honest.constraints, forged.constraints, "same algebra");
    assert_eq!(honest.trace_width, forged.trace_width);
    assert_eq!(
        honest.tables.iter().map(|t| t.id).collect::<Vec<_>>(),
        forged.tables.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    let (a, b) = (declared_manifest(&honest), declared_manifest(&forged));
    assert_ne!(a, b, "the two manifests must not agree");
    let differing: Vec<usize> = (0..ROUTED_ROWS).filter(|&i| a[i] != b[i]).collect();
    assert_eq!(
        differing,
        vec![0],
        "exactly the `delta` slot differs — the two scalar terms and the five scaled generators \
         are identical, so the refusal below cannot be about a generator"
    );
}

/// ⚠ **THE `sg` SLOT IS ABSENT, NOT ZEROED.** `closingAddends` has `3 + n` entries: `delta`,
/// `−(z₁b₀)·U`, `−z₂·H` and the five `−(z₁·s_r)·G_r`. The un-eliminated relation has a fourth
/// non-SRS addend and this manifest has no cell for it — which is the difference between a slot a
/// prover fills with zero and a slot that does not exist.
#[test]
fn the_manifest_has_no_sg_slot() {
    let m = declared_manifest(&descriptor(SRS_JSON));
    assert_eq!(m.len(), 3 + 5);
    let free_sg_rows = cells(FREE_SG_TRACE).len();
    assert_eq!(free_sg_rows, FREE_SG_ROWS);
    assert_ne!(
        m.len(),
        free_sg_rows,
        "the eliminated chain and the un-eliminated one are different lengths, and the missing \
         addend is the `sg` one"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — ⚑⚑ THE VACUITY, REPRODUCED AS A REAL PROOF.
// -------------------------------------------------------------------------------------------

/// ⚑⚑ **THE FREE-`sg` FORGERY PROVES UNDER `-final`.** This is `opening_is_vacuous_when_sg_is_free`
/// executed: a prover who may choose `sg` picks it so the closing check closes, and a descriptor
/// that checks only "the chain vanishes" accepts him. Every row is a genuine `rcbSoundRow` at the
/// Pallas prime, every thread holds, and the terminal `X`/`Z` blocks are canonically zero.
///
/// ⚠ This test PASSING is the wound, not the fix. It is here so the refusal in §3 is measured
/// against a live vacuity rather than against a hypothetical one.
#[test]
fn the_free_sg_forgery_proves_under_the_unrouted_closing_descriptor() {
    let d = descriptor(FINAL_JSON);
    let t = trace(FREE_SG_TRACE, WIDTH, FREE_SG_ROWS);
    let pis = public_inputs(&t);

    let terminal_x: Vec<u64> = cells(FREE_SG_TRACE)[FREE_SG_ROWS - 1][OUT[0]..OUT[0] + SK].to_vec();
    let terminal_z: Vec<u64> = cells(FREE_SG_TRACE)[FREE_SG_ROWS - 1][OUT[2]..OUT[2] + SK].to_vec();
    assert!(
        terminal_x.iter().all(|&v| v == 0) && terminal_z.iter().all(|&v| v == 0),
        "the forger's chain really does reach the canonical point at infinity"
    );

    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the free-`sg` chain proves — this is the vacuity");
    verify_vm_descriptor2(&d, &proof, &pis).expect("and the deployed verifier accepts it");
    println!("free-`sg` forgery PROVES under {FINAL_NAME} — the vacuity, live");
}

/// The honest chain proves under the same descriptor, so §2 is a statement about `sg` and not about
/// the descriptor accepting everything.
#[test]
fn the_bound_chain_proves_under_the_unrouted_closing_descriptor() {
    let d = descriptor(FINAL_JSON);
    let t = trace(BOUND_TRACE, WIDTH, ROUTED_ROWS);
    let pis = public_inputs(&t);
    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the eliminated chain proves");
    verify_vm_descriptor2(&d, &proof, &pis).expect("and verifies");
}

// -------------------------------------------------------------------------------------------
// §3 — ⚑⚑⚑ THE TOOTH. The same prover's data, through the eliminated manifest.
// -------------------------------------------------------------------------------------------

/// The honest pole of the routed pair: `delta` derived from the TRUE `⟨s, G⟩`, so the chain
/// vanishes over the DECLARED addends.
#[test]
fn the_bound_chain_proves_under_the_routed_closing_descriptor() {
    let d = descriptor(SRS_JSON);
    let t = trace(BOUND_ROUTED_TRACE, ROUTED_WIDTH, ROUTED_ROWS);
    let pis = public_inputs(&t);
    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the bound chain proves under the routed descriptor");
    verify_vm_descriptor2(&d, &proof, &pis).expect("and verifies");
    println!("bound chain PROVES under {SRS_NAME}");
}

/// ⚑⚑⚑ **THE FREE-`sg` FORGERY IS REFUSED BY THE AIR.**
///
/// The forger's own `delta*`, `z₁`, `z₂`, `b₀` and the same published `c·Q` — run through the
/// manifest that has no `sg` slot. His chain lands on `z₁·(sg* − ⟨s,G⟩)`, which is not `O`, and the
/// `.last` discharge gate on a terminal limb refuses.
///
/// ⚠ Three things this asserts about the REFUSAL, because a falsifier that stops falsifying is the
/// failure this is built against:
/// * it is a **CONSTRAINT**, not a bus — `assert_violated_constraint_not_bus`;
/// * the moved value is **NON-ZERO** and **inside the declared 8-bit limb width**, so no range
///   lookup can be what refuses;
/// * it comes from `prove_vm_descriptor2_unchecked`, so the producer pre-flight is not what spoke.
#[test]
fn a_free_sg_is_refused_by_the_routed_closing_air() {
    let d = descriptor(SRS_FORGED_JSON);
    let raw = cells(FREE_SG_ROUTED_TRACE);
    let t = trace(FREE_SG_ROUTED_TRACE, ROUTED_WIDTH, ROUTED_ROWS);
    let pis = public_inputs(&t);

    // The forged chain's terminal accumulator is NOT the identity, and the cells that say so are
    // ordinary 8-bit limbs.
    let last = ROUTED_ROWS - 1;
    let nonzero_x = (0..SK).filter(|&i| raw[last][OUT[0] + i] != 0).count();
    let nonzero_z = (0..SK).filter(|&i| raw[last][OUT[2] + i] != 0).count();
    assert!(
        nonzero_x > 0 && nonzero_z > 0,
        "the mutation must be non-zero on both discharged blocks — a falsifier that moved a zero \
         into a zero refuses nothing"
    );
    for i in 0..SK {
        assert!(
            raw[last][OUT[0] + i] < 256 && raw[last][OUT[2] + i] < 256,
            "every terminal limb is inside the declared 8-bit width, so no range lookup is what \
             refuses"
        );
    }

    let refusal =
        must_refuse_or_unsat_panic("a free `sg` under the eliminated closing manifest", || {
            prove_and_verify_adversarial(&d, &t, &pis)
        });
    let reason = refusal.reason();
    assert_violated_constraint_not_bus("free-`sg` closing chain", &reason);
    println!("free-`sg` chain REFUSED under {SRS_NAME}: {reason}");
}

/// ⚑ **AND THE PUBLISHED `c·Q` IS THE SAME IN BOTH.** If the honest and the forged routed traces
/// disagreed on `PI[0..95]`, the refusal above could be a public-input mismatch wearing a
/// constraint's name. They agree on the accumulator ENTERING row 0 and differ only on what leaves
/// the last one, which is the thing the discharge gate reads.
#[test]
fn the_two_routed_traces_publish_the_same_entry_accumulator() {
    let honest = trace(BOUND_ROUTED_TRACE, ROUTED_WIDTH, ROUTED_ROWS);
    let forged = trace(FREE_SG_ROUTED_TRACE, ROUTED_WIDTH, ROUTED_ROWS);
    let (a, b) = (public_inputs(&honest), public_inputs(&forged));
    assert_eq!(a[..96], b[..96], "the same `c·Q` enters both chains");
    assert_ne!(
        a[96..],
        b[96..],
        "and only the terminal accumulator differs"
    );
}

// -------------------------------------------------------------------------------------------
// §4 — the emitter's own arithmetic, re-read rather than re-predicted.
// -------------------------------------------------------------------------------------------

/// ⚑ The parameter dump says what each chain LANDED on. Read here rather than predicted, because a
/// test that predicted the terminal would be asserting the emitter's arithmetic against its own
/// restatement.
#[test]
fn the_emitters_own_terminals_say_which_chain_vanishes() {
    let bound_end = param_point("bound_end");
    let free_sg_end = param_point("free_sg_end");
    let free_sg_routed_end = param_point("free_sg_routed_end");

    assert_eq!(bound_end[0], "0", "the bound chain's X vanishes");
    assert_eq!(bound_end[2], "0", "…and its Z");
    assert_eq!(
        free_sg_end[0], "0",
        "the un-eliminated forgery's X vanishes"
    );
    assert_eq!(free_sg_end[2], "0", "…and its Z — which is the vacuity");
    assert_ne!(
        free_sg_routed_end[0], "0",
        "the SAME forgery through the eliminated manifest does NOT vanish"
    );
    assert_ne!(free_sg_routed_end[2], "0");

    // The forged `sg` is a real point and is not the MSM it was supposed to be.
    let sg = param_point("sg_forged");
    let smsm = param_point("smsm");
    assert_ne!(
        sg, smsm,
        "the forged `sg` is not `⟨s, G⟩` — else the pair is vacuous"
    );
    assert_eq!(param_small("ngen"), vec![5]);
    // ⚠ And no parameter is degenerate: at `z₁ = 0` the `sg` term would drop out for a reason that
    // has nothing to do with the elimination, and the whole pair would say nothing.
    for k in ["c", "z1", "z2", "b0"] {
        assert!(param_small(k)[0] > 1, "`{k}` is degenerate");
    }
}

// -------------------------------------------------------------------------------------------
// §5 — ⚑⚑⚑ `delta`. THE RESIDUAL THIS FILE NAMED, MEASURED AND THEN WELDED.
//
// §4 above ends by saying `delta` is free. This section stops describing that and exhibits it, at
// the emitted bytes, as a STARK proof — and then exhibits the weld that refuses it.
//
// ## The forgery, and it is not one witness
//
// `MinaWrapClosingAir.the_delta_shift_is_invisible` proves the eliminated residual depends on the
// published accumulator and `delta` ONLY THROUGH THEIR SUM. So for every group element `Δ`,
//
//     acc₀ ↦ acc₀ − Δ        delta ↦ delta + Δ        (nothing else touched)
//
// is accepted. `the_whole_shift_orbit_is_admitted` is that at ℤ for every shift;
// `the_transcript_ordered_chain_and_its_shift_both_prove` below is that at Pallas, as two real
// proofs under `dregg-mina-wrap-closing-srs::v1`.
//
// ## Why the fix cannot be algebraic — the citation, at source
//
// Upstream refuses the shift by the ORDER of two adjacent lines, and by nothing else:
//
//     poly-commitment/src/ipa.rs:382-383   sponge.absorb_g(&[opening.delta]);
//                                          let c = ScalarChallenge::new(sponge.challenge())
//                                                      .to_field(&endo_r);
//     poly-commitment/src/ipa.rs:1047-1048 the prover's mirror of the same pair
//     src/lib/pickles/wrap_verifier.ml:420-421   absorb sponge PC delta ;
//                                                let c = squeeze_scalar sponge in
//
// `c` is squeezed from a sponge that already contains `delta`, so a forger who moves `delta` moves
// `c`, and `c·Q` moves with it in a direction nobody controls. That is Fiat–Shamir; no rearrangement
// of the closing equation expresses it, which is why the weld is a TRANSCRIPT weld.
//
// ## The weld — `dregg-mina-wrap-closing-fs::v1`
//
// `absorb_g` of ONE Pallas point is a rate-2 absorb of its two AFFINE coordinates, i.e. exactly
// `perm(state + [x, y, 0])` — which is `dregg-pasta-fp-absorb::v1`'s whole program. So the welded
// descriptor adds 130 legs: 64 `.first` gates pinning row 0's `ADD_X`/`ADD_Y` limbs to the absorbed
// pair, 32 forcing the projective `Z` to `1` (the sponge absorbed AFFINE coordinates), 1 guard, 32
// PI pins publishing the squeeze, and ONE `proof_bind` whose commitment is
// `TR_IN ‖ ADD_X ‖ ADD_Y ‖ TR_OUT` — **192 lanes, the EXACT public-input vector of
// `dregg-pasta-fp-absorb::v1`, limb for limb, no digest and therefore no birthday bound.**
//
// ## ⚠ WHAT THE WELD DOES NOT BUY — say it before quoting any of it
//
// `TR_IN` is a descriptor constant and `TR_OUT` a published witness, so the AIR refuses a SHIFTED
// `delta` against a FIXED descriptor; it does not refuse a re-emission at a fresh
// `(TR_IN, delta, TR_OUT)` triple. What that converts is the SHAPE of the residue: from "a group
// element chosen last, after seeing everything" to "a published scalar `c` that a consumer
// recomputes from `PI[192..223]` and compares against the `c` it formed `c·Q` with."
// `MinaAccumulatorAir` residual 1 is that comparison, and it is CIRCUIT (the deferred MSM) or
// EMITTER or NOWHERE. **Do not say `delta` is bound. Say the residue moved to `c`, and that `c` is
// one field element rather than a free group element.**
// -------------------------------------------------------------------------------------------

const FS_JSON: &str = include_str!("fixtures/mina-wrap-closing-fs.json");
const SRS_FS_JSON: &str = include_str!("fixtures/mina-wrap-closing-srs-fs.json");
const SRS_FS_SHIFTED_JSON: &str = include_str!("fixtures/mina-wrap-closing-srs-fs-shifted.json");
const ABSORB_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-absorb.json");
/// ⚑ The SHIFTED manifest against the HONEST transcript pin — so the addend bus BALANCES and a
/// LogUp imbalance cannot be what refuses the shifted trace. Nothing but the `delta` pin can fire.
const FS_SHIFTED_MANIFEST_JSON: &str =
    include_str!("fixtures/mina-wrap-closing-fs-shifted-manifest.json");

const FS_TRACE: &str = include_str!("fixtures/mina-wrap-closing-fs-trace.txt");
const FS_SHIFTED_TRACE: &str = include_str!("fixtures/mina-wrap-closing-fs-shifted-trace.txt");
const SRS_FS_TRACE: &str = include_str!("fixtures/mina-wrap-closing-srs-fs-trace.txt");
const SRS_FS_SHIFTED_TRACE: &str =
    include_str!("fixtures/mina-wrap-closing-srs-fs-shifted-trace.txt");

const FS_NAME: &str = "dregg-mina-wrap-closing-fs::v1";
const ABSORB_NAME: &str = "dregg-pasta-fp-absorb::v1";

/// `MinaWrapClosingAir.FS_WIDTH` — the routed row, the guard, nine program lanes and the squeeze.
const FS_WIDTH: usize = ROUTED_WIDTH + 10 + SK; // 3091
/// `MinaWrapClosingAir.FS_PI_COUNT`, APPENDED so no accumulator slot moves.
const FS_PI_COUNT: usize = PI_COUNT + SK; // 224
/// `MinaWrapClosingAir.the_weld_is_one_hundred_thirty_legs`.
const FS_CONSTRAINTS: usize = ROUTED_CONSTRAINTS + 130; // 4961

const DBIND: usize = ROUTED_WIDTH; // 3049
const FSVK_0: usize = ROUTED_WIDTH + 1; // 3050
const TROUT_0: usize = ROUTED_WIDTH + 10; // 3059
/// `PastaLadderThread.ADD_X`/`ADD_Y` — the addend blocks the RCB row folds.
const ADD_X: usize = 3 * SK; // 96
const ADD_Y: usize = 4 * SK; // 128

/// `MinaWrapClosingAir.ABSORB_VK_LANES`, transcribed there and recomputed here.
const LEAN_ABSORB_VK_LANES: [i64; 9] = [
    468079883, 144575672, 434275029, 97812532, 500422946, 292012648, 58553016, 222332630, 8040594,
];

/// The library's [`key_limbs9`]; the hand-rolled base-`2^29` packing that stood here was a
/// transcription of it.
fn key_lanes9(bytes: &[u8; 32]) -> [i64; 9] {
    key_limbs9(bytes).map(|l| i64::from(l.as_u32()))
}

/// `-fs` publishes 32 more slots than `-srs`: the squeezed sponge lane, read off row 0's own cells.
fn fs_public_inputs(t: &[Vec<BabyBear>]) -> Vec<BabyBear> {
    let mut pis = public_inputs(t);
    for j in 0..SK {
        pis.push(t[0][TROUT_0 + j]);
    }
    assert_eq!(pis.len(), FS_PI_COUNT);
    pis
}

/// The descriptor's one `proof_bind`.
fn the_weld(d: &EffectVmDescriptor2) -> &ProofBindSpec {
    let mut found = None;
    for c in &d.constraints {
        if let VmConstraint2::ProofBind(m) = c {
            assert!(
                found.is_none(),
                "exactly one `proof_bind` in the welded AIR"
            );
            found = Some(m);
        }
    }
    found.expect("the welded descriptor carries a `proof_bind`")
}

#[test]
/// §5a — the shapes the rest of this section reads, against the Lean theorems that state them.
fn the_welded_artifact_declares_what_this_file_reads() {
    let fs = descriptor(FS_JSON);
    assert_eq!(fs.name, FS_NAME, "closingFsDesc_name");
    assert_eq!(fs.trace_width, FS_WIDTH, "closingFsDesc_width = 3091");
    assert_eq!(
        fs.public_input_count, FS_PI_COUNT,
        "closingFsDesc_piCount = 224"
    );
    assert_eq!(
        fs.constraints.len(),
        FS_CONSTRAINTS,
        "closingFsDesc_constraint_count = 4961"
    );

    // ⚑ the_weld_is_visible_in_the_shape: a shape check DOES tell welded from unwelded.
    let srs = descriptor(SRS_FS_JSON);
    assert_eq!(srs.name, SRS_NAME);
    assert_ne!(fs.trace_width, srs.trace_width);
    assert_ne!(fs.public_input_count, srs.public_input_count);
    assert_ne!(fs.constraints.len(), srs.constraints.len());
}

#[test]
/// ⚑ §5b — **THE WELD PINS THE REAL ABSORB PROGRAM, AND ITS COMMITMENT IS THAT PROGRAM'S PUBLIC
/// INPUT VECTOR.**
///
/// Lean cannot compute blake3, so `MinaWrapClosingAir.ABSORB_VK_LANES` is a transcription — and a
/// transcription is only a gate if something recomputes it. This does, from
/// `pasta-fp-absorb.json`'s own bytes. The wraplink drift is the measured reason: a head once
/// pinned a fingerprint no descriptor in this tree had.
fn the_weld_pins_the_real_absorb_program_and_names_its_pi_vector() {
    let absorb = descriptor(ABSORB_JSON);
    assert_eq!(absorb.name, ABSORB_NAME);
    let fp = effect_vm_descriptor2_semantic_fingerprint(&absorb).expect("representable");
    assert_eq!(
        key_lanes9(&fp),
        LEAN_ABSORB_VK_LANES,
        "MinaWrapClosingAir.ABSORB_VK_LANES must be the recomputed fingerprint of {ABSORB_NAME}"
    );

    let fs = descriptor(FS_JSON);
    let weld = the_weld(&fs);
    assert_eq!(
        weld.vk_pin.as_deref(),
        Some(&LEAN_ABSORB_VK_LANES[..]),
        "the emitted bytes pin the absorb program lane by lane"
    );

    // ⚑ 192 lanes against the sub-program's own 192 public inputs — the same 32×8-bit `pLimb`
    // encoding on both sides, so there is no digest between the two vectors.
    assert_eq!(weld.commit.len(), 3 * SK + 2 * SK + SK);
    assert_eq!(
        weld.commit.len(),
        absorb.public_input_count,
        "the commitment IS the absorb program's public-input vector, lane for lane"
    );

    // ⚑ …and its middle 64 lanes are the CHAIN'S OWN addend cells, not a copy of `delta`.
    for j in 0..2 * SK {
        assert_eq!(
            weld.commit[3 * SK + j],
            LeanExpr::Var(ADD_X + j),
            "commit lane {} must be the column the RCB row folds as row 0's addend",
            3 * SK + j
        );
    }
    // The head lanes are descriptor CONSTANTS — the transcript state entering the absorb.
    for j in 0..3 * SK {
        assert!(
            matches!(weld.commit[j], LeanExpr::Const(_)),
            "the incoming sponge state is a descriptor constant, not a witness"
        );
    }
    // The tail lanes are the PUBLISHED squeeze.
    for j in 0..SK {
        assert_eq!(weld.commit[5 * SK + j], LeanExpr::Var(TROUT_0 + j));
    }
    assert_eq!(
        ADD_Y,
        ADD_X + SK,
        "the two addend blocks really are adjacent"
    );
}

#[test]
/// ⚑⚑⚑ §5c — **THE FORGERY, LIVE: A SHIFTED `delta` PROVES UNDER THE UNWELDED CLOSING AIR.**
///
/// Two chains at the SAME manifest shape, differing in exactly two places — the published
/// accumulator and manifest slot 0 — by `+Δ` and `−Δ` for a real Pallas point `Δ`. **Both prove and
/// both verify.** That is `the_delta_shift_is_invisible` as a STARK proof rather than as a theorem
/// about a model, and it is the wound §5d closes.
///
/// ⚠ This test PASSING is the finding, not the fix.
fn the_transcript_ordered_chain_and_its_shift_both_prove() {
    // The two are genuinely different objects.
    let d0 = param_point("delta_fs");
    let d1 = param_point("delta_shifted");
    let a0 = param_point("acc0_fs");
    let a1 = param_point("acc0_shifted");
    assert_ne!(d0, d1, "the shift really moves `delta`");
    assert_ne!(a0, a1, "…and really moves the published accumulator");
    assert_eq!(d0[2], "1", "`delta` is AFFINE — what `absorb_g` absorbs");
    assert_eq!(
        d1[2], "1",
        "…and so is the shifted one, so the AFFINE pin is not the refusal"
    );

    // Both chains reach the canonical point at infinity.
    for k in ["fs_end", "fs_shifted_end"] {
        let e = param_point(k);
        assert_eq!(e[0], "0", "{k} X vanishes");
        assert_eq!(e[2], "0", "{k} Z vanishes");
    }

    for (json, text, label) in [
        (SRS_FS_JSON, SRS_FS_TRACE, "transcript-ordered"),
        (SRS_FS_SHIFTED_JSON, SRS_FS_SHIFTED_TRACE, "SHIFTED"),
    ] {
        let d = descriptor(json);
        let t = trace(text, ROUTED_WIDTH, ROUTED_ROWS);
        let pis = public_inputs(&t);
        let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("the {label} chain proves: {e}"));
        verify_vm_descriptor2(&d, &proof, &pis).expect("and verifies");
        println!("{label} chain PROVES under {SRS_NAME}");
    }
    println!("⚑ the closing check cannot separate them — the residual sees only acc₀ + delta");
}

#[test]
/// §5d ACCEPT pole — the transcript's own `delta` proves under the welded AIR. Without this the
/// refusal below would be evidence that the welded descriptor accepts nothing.
fn the_welded_air_admits_the_transcripts_own_delta() {
    let d = descriptor(FS_JSON);
    let t = trace(FS_TRACE, FS_WIDTH, ROUTED_ROWS);
    let pis = fs_public_inputs(&t);
    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the transcript-ordered chain proves under the welded descriptor");
    verify_vm_descriptor2(&d, &proof, &pis).expect("and verifies");
    println!("transcript-ordered chain PROVES under {FS_NAME}");
}

#[test]
/// ⚑⚑⚑ §5d REFUSE pole — **THE SHIFTED `delta` IS REFUSED BY THE WELDED AIR.**
///
/// The same shift §5c proves, run against the welded descriptor. A `.first` boundary gate on a
/// pinned `delta` limb fires.
///
/// ⚠ Four things this asserts about the refusal, because a falsifier that stops falsifying is the
/// failure this is built against:
/// * the moved cells are **NON-ZERO** and **inside the declared 8-bit limb width**, so no range
///   lookup can be what refuses;
/// * the chain's **terminal `X`/`Z` blocks are still canonically ZERO**, so the `.last` discharge
///   gate is *not* what refuses — this is a `delta` tooth and not a re-run of §3's;
/// * the shifted `delta`'s projective `Z` limb is still `1`, so the AFFINE pin is not what refuses;
/// * it is a **CONSTRAINT**, not a bus, and it comes from `prove_vm_descriptor2_unchecked`, so the
///   producer pre-flight is not what spoke.
fn a_shifted_delta_is_refused_by_the_welded_closing_air() {
    let d = descriptor(FS_JSON);
    let raw = cells(FS_SHIFTED_TRACE);
    let honest = cells(FS_TRACE);
    let t = trace(FS_SHIFTED_TRACE, FS_WIDTH, ROUTED_ROWS);
    let pis = fs_public_inputs(&t);

    // The falsifier moved something, in-width, on the pinned blocks.
    let moved = (0..2 * SK)
        .filter(|&j| raw[0][ADD_X + j] != honest[0][ADD_X + j])
        .count();
    assert!(
        moved > 0,
        "the shifted trace must differ from the honest one on the PINNED `delta` limbs — a \
         falsifier that moved nothing refuses nothing"
    );
    assert!(
        raw[0][ADD_X..ADD_X + 2 * SK].iter().any(|&v| v != 0),
        "the moved value is non-zero"
    );
    for j in 0..2 * SK {
        assert!(
            raw[0][ADD_X + j] < 256,
            "every pinned limb is inside the declared 8-bit width, so no range lookup refuses"
        );
    }
    // The projective Z is still 1, so the AFFINE pin is not what fires.
    assert_eq!(raw[0][5 * SK], 1, "the shifted `delta` is still affine");
    for j in 1..SK {
        assert_eq!(raw[0][5 * SK + j], 0);
    }
    // ⚑ And the chain still VANISHES, so the discharge gate is not what fires.
    let last = ROUTED_ROWS - 1;
    for i in 0..SK {
        assert_eq!(
            raw[last][OUT[0] + i],
            0,
            "the shifted chain's terminal X is still canonically zero"
        );
        assert_eq!(raw[last][OUT[2] + i], 0, "…and its terminal Z");
    }

    let refusal = must_refuse_or_unsat_panic("a shifted `delta` under the transcript weld", || {
        prove_and_verify_adversarial(&d, &t, &pis)
    });
    let reason = refusal.reason();
    assert_violated_constraint_not_bus("shifted-`delta` closing chain", &reason);
    println!("shifted `delta` REFUSED under {FS_NAME}: {reason}");
}

#[test]
/// §5e — the emitter's own transcript dump, re-asserted so no number is transcribed twice, and so
/// the ORDER the exhibit is about is checkable: `TR_OUT` is a function of `TR_IN` and `delta`, and
/// `c` is a function of `TR_OUT`.
fn the_emitters_transcript_dump_says_delta_came_first() {
    let tr_in = param_point("tr_in");
    let delta = param_point("delta_fs");
    let squeeze = param_point("squeeze");
    let c_fs = param_point("c_fs");
    let tr_out = param_point("tr_out");

    assert_eq!(tr_in.len(), 3, "a Poseidon state over Fp is three lanes");
    assert_eq!(tr_out.len(), 3);
    assert_eq!(
        squeeze[0], tr_out[0],
        "the squeeze IS lane 0 of the permuted state — `sponge.challenge()`"
    );
    assert_ne!(
        tr_in[0], tr_out[0],
        "absorbing `delta` moved the sponge — else the weld would name a no-op"
    );
    assert_ne!(c_fs[0], "0");
    assert_ne!(
        c_fs[0], squeeze[0],
        "`c` is the ENDO LIFT of the low 128 bits, not the raw squeeze \
         (`ScalarChallenge::to_field`)"
    );
    assert_eq!(delta[2], "1", "`absorb_g` absorbs AFFINE coordinates");

    // ⚑ The welded descriptor's commit head IS this `TR_IN`, decomposed into 8-bit limbs.
    let fs = descriptor(FS_JSON);
    let weld = the_weld(&fs);
    let lane0: Vec<i64> = (0..SK)
        .map(|j| match weld.commit[j] {
            LeanExpr::Const(k) => k,
            _ => panic!("the incoming state is a constant"),
        })
        .collect();
    // ⚑ **THIRTY-TWO EIGHT-BIT LIMBS ARE 256 BITS AND DO NOT FIT IN A `u128`.** This was
    // `v |= (*l as u128) << (8 * j)` over `j in 0..32` until 2026-08-08: `8·j` reaches 248, so
    // every `j >= 16` is a shift past the width. In DEBUG that is an `attempt to shift left with
    // overflow` panic — this test was RED at HEAD — and in RELEASE it is a MASKED shift
    // (`8·j mod 128`), which happened to give the right answer only because limbs 16..31 are zero
    // for this particular transcript state. A check that is a panic in one profile and an accident
    // in the other is not a check. Recomposed on decimal digits instead, the same way
    // `mina_statehash_seam_proves::lanes9_to_decimal` does it: no bignum dependency, no width to
    // overflow, and it stays correct if the high limbs ever become non-zero.
    let mut digits: Vec<u32> = vec![0];
    for l in lane0.iter().rev() {
        let mut carry = u64::try_from(*l).expect("a commit limb is a non-negative 8-bit value");
        for d in digits.iter_mut().rev() {
            let cur = u64::from(*d) * 256 + carry;
            *d = (cur % 10) as u32;
            carry = cur / 10;
        }
        while carry > 0 {
            digits.insert(0, (carry % 10) as u32);
            carry /= 10;
        }
    }
    while digits.len() > 1 && digits[0] == 0 {
        digits.remove(0);
    }
    let v: String = digits
        .iter()
        .map(|d| char::from(b'0' + u8::try_from(*d).expect("a decimal digit")))
        .collect();
    assert_eq!(
        v, tr_in[0],
        "commit lanes 0..32 recompose to the transcript state's lane 0"
    );
}

#[test]
/// ⚑⚑⚑ §5f — **THE SURGICAL FALSIFIER: THE BUS BALANCES AND THE PIN STILL REFUSES.**
///
/// §5d proves the shifted trace under a descriptor whose manifest is the HONEST one, so its addend
/// lookup is also unbalanced and a reader could ask which of the two spoke. This descriptor carries
/// the SHIFTED manifest and the HONEST transcript pin: the routing bus balances, the chain vanishes,
/// every limb is in-width, the point is affine — **and the only thing left that can refuse is the
/// `delta` pin.** This is exactly the brief's forgery: a `delta` that satisfies the closing equation
/// and is not the transcript's.
fn a_delta_that_closes_the_equation_but_is_not_the_transcripts_is_refused() {
    let d = descriptor(FS_SHIFTED_MANIFEST_JSON);
    assert_eq!(d.name, FS_NAME);
    assert_eq!(d.trace_width, FS_WIDTH);

    // The manifest IS the shifted one, so the exact-public bus balances on this trace.
    let honest_desc = descriptor(FS_JSON);
    let honest_manifest = declared_manifest(&honest_desc);
    let shifted_manifest = declared_manifest(&d);
    assert_eq!(shifted_manifest.len(), honest_manifest.len());
    assert_ne!(
        shifted_manifest[0], honest_manifest[0],
        "the two manifests differ at slot 0 — the `delta` slot"
    );
    for i in 1..shifted_manifest.len() {
        assert_eq!(
            shifted_manifest[i], honest_manifest[i],
            "…and NOWHERE else, so the shift is the only variable"
        );
    }
    // …and the transcript pin is still the honest one: the `.first` boundary constants that name
    // the absorbed pair have not moved with the manifest.
    let weld_h = the_weld(&honest_desc);
    let weld_s = the_weld(&d);
    assert_eq!(
        weld_h.commit, weld_s.commit,
        "the weld's commitment expression is unchanged — the pin is the transcript's"
    );
    assert_eq!(weld_h.vk_pin, weld_s.vk_pin);

    let raw = cells(FS_SHIFTED_TRACE);
    let t = trace(FS_SHIFTED_TRACE, FS_WIDTH, ROUTED_ROWS);
    let pis = fs_public_inputs(&t);

    // Every discriminating cause OTHER than the pin is ruled out, on the trace itself.
    let last = ROUTED_ROWS - 1;
    for i in 0..SK {
        assert_eq!(raw[last][OUT[0] + i], 0, "the chain still vanishes in X");
        assert_eq!(
            raw[last][OUT[2] + i],
            0,
            "…and in Z — not the discharge gate"
        );
    }
    assert_eq!(raw[0][5 * SK], 1, "affine — not the Z normalisation gate");
    for j in 0..2 * SK {
        assert!(raw[0][ADD_X + j] < 256, "in-width — not a range lookup");
    }
    assert_eq!(
        raw[0][DBIND], 1,
        "the guard is set — the bind is live on row 0"
    );
    for (i, lane) in LEAN_ABSORB_VK_LANES.iter().enumerate() {
        assert_eq!(
            i64::try_from(raw[0][FSVK_0 + i]).unwrap(),
            *lane,
            "the attested program lanes are the pin's — not the vk gate"
        );
    }

    let refusal = must_refuse_or_unsat_panic(
        "a `delta` that closes the equation and is not the transcript's",
        || prove_and_verify_adversarial(&d, &t, &pis),
    );
    let reason = refusal.reason();
    assert_violated_constraint_not_bus("transcript-unbound `delta`", &reason);
    println!("⚑ a closing-equation-satisfying, transcript-UNBOUND `delta` REFUSED: {reason}");
}
