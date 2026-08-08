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
