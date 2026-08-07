//! # ⚑⚑ THE ACCUMULATOR'S ADDENDS, ROUTED — PROVED AND REFUSED IN A CIRCUIT.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-accumulator-routed::v1` is `EffectLower.lowerAir` of
//! `Dregg2.Circuit.Emit.MinaAccumulatorAir.accRoutedAirOn` — `accFinalAir`'s legs verbatim, plus a
//! threaded row-index column and ONE exact-public lookup whose 97-wide tuple is
//! `(row index + 1) ‖ the row's 96 addend limbs`. The declared manifest is
//! `MinaAccumulatorAir.demoAddends`, and the trace fixtures are generated from **that same `def`**.
//! Nothing in this file authors a constraint, a `Builder` gadget or an `air_accepts` predicate.
//!
//! ## What this closes, and what `mina_accumulator_air_proves.rs` left open
//!
//! That file's own header says it: *"Not that the addends are the SRS.
//! `accumulator_discharge_forced` forces the chain of the trace's own addends to vanish and says
//! nothing about what those addends are."* The Lean theorem says it at `:535` in its own words —
//! ***"It says nothing about WHAT the addends are."***
//!
//! This is that half. `MinaAccumulatorAir.accumulator_discharge_forced_on_declared_addends`
//! concludes over `declaredChain`, a fold in which the trace's addend columns **do not occur**; the
//! verifier rebuilds the manifest from the descriptor bytes
//! (`ExactPublicManifest::preprocessed`), so the addends are VK-pinned rather than prover-supplied.
//!
//! ## ⚑ THE PRICE THAT BLOCKED IT WAS NOT A PRICE
//!
//! The routing tuple is `1 + 3·32 = 97` wide against a deployed `MAX_EXACT_PUBLIC_ARITY = 64`.
//! Read at source, that constant has exactly two readers — `check_descriptor2`'s admission and a
//! DRIFT GUARD comparing it to `exact_public_table_air_family().len()` — so it was **the member
//! count of a checked-in JSON artifact and bounded no resource**. It was raised to `97`, the
//! artifact re-emitted (`63 429 → 128 142` bytes) and the constant re-pinned on both sides.
//! `ExactPublicTableEmit.the_raise_costs_bytes_and_no_allocation` states the arithmetic: at `2^16`
//! distinct rows the cell cap is 19.4% spent and the committed matrix is 26 MB, one instance.
//!
//! ## ⚑⚑ THE FORGERY IS THE SHARP ONE, AND THE FIXTURE PAIR IS BUILT TO BE ONLY-THAT
//!
//! `substituted` is a chain of **real Vesta points that are not this block's addends**: `2G` seven
//! times, then the closing negation. Measured on the fixtures by
//! [`the_forgery_differs_from_the_honest_chain_only_in_its_addends`]:
//!
//! * every row is a genuine sound RCB row and every accumulator thread holds;
//! * the terminal `OUT_X`/`OUT_Z` limbs are all zero — **it discharges**, so the 64 `.last` gates
//!   are satisfied;
//! * `PI[0..95]` — the published CLAIM — is byte-identical to the honest trace's, and so are the
//!   `OUT_X` and `OUT_Z` halves of the published result;
//! * ⚠ the `OUT_Y` block DIFFERS, and that is a property of the object rather than a weakness of
//!   the exhibit: `Y` is the unconstrained coordinate of the PROJECTIVE identity. The discharge
//!   gates read `OUT_X` and `OUT_Z` only, because `pasta_msm::is_identity` is `z == 0 && x == 0`,
//!   so `(0 : y : 0)` is the identity at EVERY `y` and a consumer checking "the accumulator
//!   vanished" accepts both traces. [`the_forgery_differs_from_the_honest_chain_only_in_its_addends`]
//!   asserts this shape rather than the "byte-identical PI" an earlier draft of this file claimed;
//! * the row-index column is `0..7` in both;
//! * and the addend blocks differ in **95 of 96** cells.
//!
//! So it satisfies every constraint `-final` emits, and it is exactly the case the unrouted theorem
//! admits. It PROVES under `-final` (the OLD-ADMITS pole, [`the_forgery_proves_under_final`]) and
//! must be REFUSED under `-routed`.
//!
//! ## ⚠ THE REFUSING GATE IS A BUS, AND THAT IS THE POINT RATHER THAN A MISS
//!
//! Elsewhere in this repo a tooth aimed at a GATE calls [`assert_violated_constraint_not_bus`],
//! because a LogUp imbalance standing in for the gate under test means the tooth missed. **Here the
//! intended constraint IS a bus**: `TableSem::ExactPublicRows` is realized as a LogUp PERMUTATION
//! (`DescriptorIR2.PublicLookupBalanced`), and forcing the routing is precisely forcing that
//! balance. `PastaMsmBound`'s contents-binding falsifier is refused the same way.
//!
//! So the assertion is INVERTED and made STRICTER rather than dropped: the refusal must name
//! **`ir2_exact_public_a97`** — the arity-97 bus, which exists only because of the raise — and must
//! be a BUS verdict rather than a CONSTRAINT one, because a gate objecting would mean the forgery
//! was not the all-gates-satisfied case this file claims it is.
//!
//! ## ⚠⚑ AND THE PATH MATTERS: A PRODUCER PRE-FLIGHT FIRES BEFORE THE CIRCUIT DOES
//!
//! Measured here, the first time this file was run. `prove_vm_descriptor2` (the SINGLE-descriptor
//! entry) runs `build_traces`'s `check` block, which REPLAYS every exact-public lookup in Rust and
//! refuses with *"exact-public table … lookup multiset does not equal its Lean-emitted manifest"*
//! — **before the constraint system sees anything**. `batch_airs_and_matrices` (the BATCH entry)
//! does not run it.
//!
//! A producer-side replay is worth having and proves NOTHING about an adversary, who simply does
//! not run it. So every refusal tooth below goes through `prove_vm_descriptors2_batch` /
//! `verify_vm_descriptors2_batch`, which is the rail the sibling `pasta_bound_sg_prove.rs` uses for
//! the same reason, and the verdict asserted is the DEPLOYED VERIFIER's LogUp one.
//! [`the_producer_preflight_also_refuses_and_that_is_not_the_tooth`] records the pre-flight
//! separately and says out loud what it is worth.
//!
//! ⚠ **RUN IN RELEASE.** These descriptors carry lookups, so an algebraic refusal is a p3
//! `#[cfg(debug_assertions)]` PANIC in debug and a clean `Err` in release:
//!
//! ```text
//! cargo test -p dregg-circuit --release --test mina_accumulator_routing_proves -- --nocapture
//! ```
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH
//!
//! **Not that the declared addends are the right ones.** The routing moves the trust ONE OBJECT
//! OUT — from *"the addends the prover wrote"* to *"the addends this descriptor declares"*. Which
//! descriptor a node verifies against is a selection question, and it is the same class as the
//! accumulator's two other trusted items, both still open: no gate ties the claim to a head
//! (`root_entry_binds_claim` is a consumer refusal, not a constraint), and a claim rebuilt around
//! tampered challenges is accepted, in-circuit exactly as natively. The SCALING is also unrouted:
//! nothing says the declared addends are `−s_r · G_r` for a real IPA challenge vector.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::refusal::{
    assert_bus_imbalance_not_constraint, assert_violated_constraint_not_bus,
    must_refuse_or_unsat_panic,
};

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The Lean-emitted artifacts and the Lean-generated fixtures.
// ────────────────────────────────────────────────────────────────────────────────────────────────

const FINAL_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-final.json");
const ROUTED_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-routed.json");

/// The honest chain, widened with the row-index column.
const ROUTED: &str = include_str!("fixtures/mina-accumulator-routed-trace.txt");
/// ⚑ The forgery: real Vesta points that are NOT the declared addends, widened.
const SUBSTITUTED: &str = include_str!("fixtures/mina-accumulator-substituted-trace.txt");
/// …and the SAME chain at `-final`'s width, which is the OLD-ADMITS pole.
const SUBSTITUTED_NARROW: &str =
    include_str!("fixtures/mina-accumulator-substituted-narrow-trace.txt");

/// `PastaCurveSound.RCB_WIDTH`.
const WIDTH: usize = 3048;
/// `MinaAccumulatorAir.ROUTED_WIDTH` — the RCB row plus the row-index column.
const ROUTED_WIDTH: usize = WIDTH + 1;
/// `MinaAccumulatorAir.RIDX`.
const RIDX: usize = WIDTH;
/// Eight rows: seven generator adds and the closing negation. A power of two.
const ROWS: usize = 8;
/// `PastaFieldSound.SK`.
const SK: usize = 32;

/// `MinaAccumulatorAir.ACC_X/ACC_Y/ACC_Z`.
const ACC: [usize; 3] = [0, SK, 2 * SK];
/// `MinaAccumulatorAir.ADD_X` — the addend block's base. The three coordinate blocks are contiguous
/// (`3·SK / 4·SK / 5·SK`), which is why the routing tuple is one `List.range`.
const ADD_X: usize = 3 * SK;
/// `OUT_X/OUT_Y/OUT_Z` — the gadget's SSA `v 26 / v 29 / v 32`.
const OUT: [usize; 3] = [1024, 1120, 1216];

/// `4 476` sound row-local + `96` threads + `192` endpoint pins + `64` discharge gates.
const FINAL_CONSTRAINTS: usize = 4476 + 96 + 192 + 64;
/// …plus the index origin, the index thread and the routing lookup.
const ROUTED_CONSTRAINTS: usize = FINAL_CONSTRAINTS + 3;
/// `6 · SK` — two projective Vesta points.
const PI_COUNT: usize = 6 * SK;
/// `MinaAccumulatorAir.ADDEND_TUP` — the key plus a projective point's `3 · 32` limbs.
const ADDEND_TUP: usize = 1 + 3 * SK;
/// `MinaAccumulatorAir.ADDEND_TID` — `.custom 128 ⇒ wireId 133`.
const ADDEND_TID: usize = 133;
/// The LogUp bus the arity-97 exact-public family member serves.
const ADDEND_BUS: &str = "ir2_exact_public_a97";

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the routed AIR")
}

fn cells(text: &str) -> Vec<Vec<u64>> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| t.parse::<u64>().expect("cell is a u64 decimal"))
                .collect()
        })
        .collect()
}

fn trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows = cells(text);
    assert_eq!(rows.len(), ROWS);
    assert!(
        rows.iter().all(|r| r.len() == width),
        "every fixture row must be {width} columns"
    );
    rows.into_iter()
        .map(|r| {
            r.into_iter()
                .map(|c| BabyBear::new(u32::try_from(c).expect("a cell fits a u32")))
                .collect()
        })
        .collect()
}

/// The published endpoints, read off the trace's own pinned columns — never authored here.
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

/// ⚑ **THE ADVERSARIAL RAIL.** `prove_vm_descriptor2_unchecked` bypasses `build_traces`'s
/// producer-side replay, so a forged witness reaches the CONSTRAINT SYSTEM and the verdict is the
/// circuit's; the proof is then handed to the deployed verifier.
///
/// ⚠ The batch rail (`prove_vm_descriptors2_batch`, which the sibling `pasta_bound_sg_prove.rs`
/// uses for exactly this) is NOT available here: it carries MAIN and EXACT-PUBLIC instances only,
/// and this descriptor declares a witness-bearing BYTE table because the Pasta row range-checks its
/// limbs. Measured, not assumed — that refusal is what sent this file to the single-descriptor rail.
fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

/// The declared addend manifest, read off the PARSED artifact.
fn declared_manifest(d: &EffectVmDescriptor2) -> Vec<Vec<u32>> {
    let td = d
        .tables
        .iter()
        .find(|t| t.id == ADDEND_TID)
        .expect("the routed descriptor declares the addend table");
    match &td.sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("the addend table must be exact_public_rows, got {other:?}"),
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// (a) the artifact declares the routing this file reads
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE SHAPE, MEASURED OFF THE PARSED DESCRIPTOR.** The routed artifact is the final one plus
/// exactly three constraints and one column, with a `97`-wide exact-public table on its own wire id.
///
/// The arity assertion is the load-bearing one: at the cap of the day (`64`) `parse_vm_descriptor2`
/// would have REFUSED this artifact outright, so a green parse here IS the raise, measured.
#[test]
fn the_routed_artifact_declares_the_routing_this_file_reads() {
    let fin = descriptor(FINAL_JSON);
    let rt = descriptor(ROUTED_JSON);

    assert_eq!(rt.name, "dregg-mina-accumulator-routed::v1");
    assert_ne!(fin.name, rt.name, "a name is a KEY, not a label");

    assert_eq!(rt.trace_width, ROUTED_WIDTH, "3 048 + the row index");
    assert_eq!(fin.trace_width, WIDTH, "and -final is UNMOVED");
    assert_eq!(rt.public_input_count, PI_COUNT, "the PI surface is unmoved");
    assert_eq!(rt.constraints.len(), ROUTED_CONSTRAINTS);
    assert_eq!(fin.constraints.len(), FINAL_CONSTRAINTS);

    // The final descriptor's constraints are a genuine PREFIX: the routing APPENDS, it does not
    // re-author. Everything `-final` forces, `-routed` forces identically.
    assert_eq!(
        fin.constraints,
        rt.constraints[..FINAL_CONSTRAINTS],
        "the routed descriptor must EXTEND the final one"
    );

    assert_eq!(
        rt.tables.len(),
        5,
        "main + the three range tables + the addend manifest"
    );
    let td = rt
        .tables
        .iter()
        .find(|t| t.id == ADDEND_TID)
        .expect("the addend table is declared");
    assert_eq!(td.name, "mina_accumulator_addends");
    assert_eq!(
        td.arity, ADDEND_TUP,
        "97 = the key plus a projective Pasta point's 3 x 32 limbs — the tuple the cap of the day \
         REFUSED"
    );
    assert!(
        td.arity > 64,
        "if this ever stops exceeding 64 the raise stopped being what this file is about"
    );

    // ⚑ Five DISTINCT wire ids: the addend manifest gets its own LogUp bus and cannot pool with a
    // range table. `reference-a-display-name-is-not-a-key`.
    let mut ids: Vec<usize> = rt.tables.iter().map(|t| t.id).collect();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), 5, "the five declared tables must not share ids");
}

/// ⚑ **EXACTLY ONE EMITTED LOOKUP TARGETS THE ADDEND TABLE**, and the row's own range lookups do
/// not. This is `MinaAccumulatorAir.only_the_routing_leg_targets_the_addend_table` measured on the
/// artifact: a second lookup reaching this table would make the LogUp log a multiset of PAIRS and
/// every pointwise conclusion of the Lean theorem false.
#[test]
fn exactly_one_lookup_targets_the_addend_table() {
    let rt = descriptor(ROUTED_JSON);
    let mut at_addend = 0usize;
    let mut elsewhere = 0usize;
    for c in &rt.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if l.table == ADDEND_TID {
                at_addend += 1;
                assert_eq!(
                    l.tuple.len(),
                    ADDEND_TUP,
                    "the routing tuple is 97 wide, or it is not the tuple the Lean forces"
                );
            } else {
                elsewhere += 1;
            }
        }
    }
    assert_eq!(at_addend, 1, "one routing lookup, fired on every row");
    assert!(
        elsewhere > 0,
        "the six limb legs' range lookups must still be there — otherwise the filter above is \
         checking nothing"
    );
}

/// ⚑ **THE DECLARED MANIFEST IS THE TRACE'S OWN ADDENDS**, row for row, key for key — measured
/// against the honest fixture rather than assumed. This is the deployed image of
/// `MinaAccumulatorAir.addend_is_its_declared_addend`, and it is what makes the refusal below a
/// statement about ROUTING rather than about a malformed manifest.
#[test]
fn the_declared_manifest_is_the_honest_traces_own_addends() {
    let rt = descriptor(ROUTED_JSON);
    let rows = declared_manifest(&rt);
    let t = cells(ROUTED);

    assert_eq!(
        rows.len(),
        ROWS,
        "the balance is a PERMUTATION, so manifest rows = trace rows"
    );
    for (i, m) in rows.iter().enumerate() {
        assert_eq!(m.len(), ADDEND_TUP);
        assert_eq!(
            u64::from(m[0]),
            (i + 1) as u64,
            "the key is `index + 1`, never `index`: a live key space containing 0 cannot be told \
             from an all-zero tuple"
        );
        for j in 0..3 * SK {
            assert_eq!(
                u64::from(m[1 + j]),
                t[i][ADD_X + j],
                "declared addend {i} limb {j} must be the honest trace's own cell"
            );
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// (b) the falsifier is checked to MOVE, and to move something nonzero and in-width
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑⚑ **THE FORGERY DIFFERS FROM THE HONEST CHAIN ONLY IN ITS ADDENDS.**
///
/// This campaign has already shipped one falsifier that moved a zero into a zero and one that was
/// refused by a range lookup rather than by the gate under test
/// (`minted-a-falsifier-that-stopped-falsifying`). So every clause below runs BEFORE any polarity:
///
/// * the two traces agree on all `192` published cells (same claim, same result);
/// * both terminal `OUT_X`/`OUT_Z` blocks are ALL ZERO, so the forgery genuinely discharges;
/// * the row-index columns are `0..7` in both, so the index thread cannot be the refusal;
/// * the addend blocks differ in **95** cells, and every moved cell is NONZERO on at least one
///   side and `< 2^8` on both — so no range lookup can be what separates them.
#[test]
fn the_forgery_differs_from_the_honest_chain_only_in_its_addends() {
    let h = cells(ROUTED);
    let f = cells(SUBSTITUTED);
    let n = cells(SUBSTITUTED_NARROW);

    assert_eq!(h.len(), ROWS);
    assert_eq!(f.len(), ROWS);

    // The narrow rendering is the SAME chain, so the OLD-ADMITS pole is not a different forgery.
    for r in 0..ROWS {
        assert_eq!(
            n[r],
            f[r][..WIDTH],
            "row {r}: the narrow fixture must be the wide one minus the index column"
        );
    }

    // Same published claim and same published result.
    for base in ACC {
        for i in 0..SK {
            assert_eq!(h[0][base + i], f[0][base + i], "acc_in limb must be shared");
        }
    }
    // ⚠ The published RESULT is shared in `OUT_X` and `OUT_Z` and NOT in `OUT_Y`, and that is a
    // property of the projective identity rather than a weakness of the exhibit: the discharge
    // gates read X and Z only (`pasta_msm::is_identity` is `z == 0 && x == 0`), so `(0 : y : 0)` is
    // the identity at every `y`. Both chains reach the identity; they reach different
    // representatives of it. A consumer checking "the accumulator vanished" accepts both.
    for base in [OUT[0], OUT[2]] {
        for i in 0..SK {
            assert_eq!(
                h[ROWS - 1][base + i],
                f[ROWS - 1][base + i],
                "the X and Z halves of acc_out must be shared — both are canonical zero"
            );
        }
    }
    let y_differs = (0..SK).any(|i| h[ROWS - 1][OUT[1] + i] != f[ROWS - 1][OUT[1] + i]);
    assert!(
        y_differs,
        "the two chains are expected to reach DIFFERENT representatives of the identity; if OUT_Y \
         ever agrees, say so rather than leaving this assertion asserting nothing"
    );

    // Both discharge: the 64 `.last` gates read OUT_X and OUT_Z.
    for base in [OUT[0], OUT[2]] {
        for i in 0..SK {
            assert_eq!(h[ROWS - 1][base + i], 0, "the honest chain must vanish");
            assert_eq!(
                f[ROWS - 1][base + i],
                0,
                "the FORGERY must vanish too, or the discharge gate is what refuses it and this \
                 tooth is not about routing"
            );
        }
    }

    // The index column is threaded identically, so it is not what separates them.
    for r in 0..ROWS {
        assert_eq!(h[r][RIDX], r as u64);
        assert_eq!(f[r][RIDX], r as u64);
    }

    // The addends differ, and what moved is nonzero and inside the declared 8-bit limb width.
    let mut moved = 0usize;
    for r in 0..ROWS {
        for j in 0..3 * SK {
            let (a, b) = (h[r][ADD_X + j], f[r][ADD_X + j]);
            assert!(a < 256 && b < 256, "an addend limb is 8 bits on BOTH sides");
            if a != b {
                moved += 1;
                assert!(
                    a != 0 || b != 0,
                    "a falsifier that moved a zero into a zero"
                );
            }
        }
    }
    assert!(
        moved >= 95 * ROWS / 2,
        "the forgery must actually move the addends; it moved {moved} cells"
    );
    println!("the forgery moves {moved} addend cells and nothing else");

    // And no cell anywhere exceeds the 16-bit carry width, so no range lookup is the refusal.
    for row in h.iter().chain(f.iter()) {
        for &c in row {
            assert!(c < 1 << 16, "a fixture cell exceeded the declared width");
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// (c) both polarities
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **POLARITY 1 — THE ROUTED CHAIN PROVES.**
///
/// The honest chain, whose addends ARE the descriptor's declared manifest, proved and verified by
/// the deployed prover against the descriptor that DEMANDS the routing balance. If this went red
/// the exact-public declaration would be unsatisfiable and every refusal below would be vacuous.
#[test]
fn the_routed_chain_proves() {
    let rt = descriptor(ROUTED_JSON);
    let t = trace(ROUTED, ROUTED_WIDTH);
    let pis = public_inputs(&t);
    prove_and_verify_adversarial(&rt, &t, &pis)
        .unwrap_or_else(|e| panic!("the routed chain must prove and verify: {e}"));

    // …and on the single-descriptor rail too, so the producer's pre-flight is exercised on the
    // HONEST side rather than only on the forged one.
    let proof = prove_vm_descriptor2(&rt, &t, &pis, &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| panic!("the routed chain must pass the producer pre-flight: {e:?}"));
    verify_vm_descriptor2(&rt, &proof, &pis)
        .unwrap_or_else(|e| panic!("the routed proof must verify: {e:?}"));
}

/// ⚑ **THE NEGATIVE CONTROL — THE FORGERY PROVES UNDER `-final`.**
///
/// Without this the refusal below would be evidence about a trace that was broken in some other
/// way. The substituted chain satisfies the sound row, the 96 threads, the 192 endpoint pins and
/// the 64 discharge gates: `-final` has nothing to say about which points were added, and says
/// nothing. **Deleting the routing lookup turns the next test green while this one stays green**,
/// which is what makes this the control rather than decoration.
#[test]
fn the_forgery_proves_under_final() {
    let fin = descriptor(FINAL_JSON);
    let t = trace(SUBSTITUTED_NARROW, WIDTH);
    let pis = public_inputs(&t);
    prove_and_verify_adversarial(&fin, &t, &pis).expect(
        "the substituted chain is eight honest threaded rows that DISCHARGE — the final descriptor \
         must accept it, or the refusal under -routed is about something other than the routing",
    );
}

/// ⚑⚑ **POLARITY 2 — AND `-routed` REFUSES IT, BY THE ADDEND BUS AND BY NOTHING ELSE.**
///
/// The OLD-ADMITS / NEW-REJECTS pair that cannot rot into agreement: the same eight honest,
/// discharging, thread-holding rows PROVE under `dregg-mina-accumulator-final::v1` and are REFUSED
/// under `dregg-mina-accumulator-routed::v1`.
///
/// ⚠ **The refusing constraint is a BUS, and here that is the intended one rather than a miss.**
/// `TableSem::ExactPublicRows` is realized as a LogUp PERMUTATION, so the routing IS the balance.
/// The assertion is therefore inverted and made stricter than
/// [`assert_violated_constraint_not_bus`] would be: the reason must name `ir2_exact_public_a97` —
/// the arity-97 member, which exists only because the cap was raised — and must NOT be an
/// `OodEvaluationMismatch`, since a gate objecting would mean the forgery was not the
/// all-gates-satisfied case the control above proves it is.
#[test]
fn the_substituted_addends_are_refused_by_the_routing() {
    let rt = descriptor(ROUTED_JSON);
    let t = trace(SUBSTITUTED, ROUTED_WIDTH);
    let pis = public_inputs(&t);

    let what = "substituted addends under -routed, at the deployed verifier";
    let refusal = must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&rt, &t, &pis));
    let reason = refusal.reason();

    // ⚑ A BUS verdict, not a CONSTRAINT one. A gate objecting would mean the forgery was not the
    // all-gates-satisfied case `the_forgery_proves_under_final` proves it is.
    assert_bus_imbalance_not_constraint(what, &reason);
    assert!(
        reason.contains(ADDEND_BUS),
        "the refusal must NAME the addend routing bus `{ADDEND_BUS}`. A bus imbalance somewhere \
         else means something other than the routing caught this forgery, and the routing tooth \
         is OPEN: {reason}"
    );
    println!("the addend routing refused the substituted chain: {reason}");
}

/// ⚠ **THE PRODUCER PRE-FLIGHT ALSO REFUSES, AND THAT IS NOT WHAT CLOSES THE HOLE.**
///
/// `prove_vm_descriptor2` runs `build_traces`'s `check` block, which REPLAYS every exact-public
/// lookup in Rust and refuses before the constraint system sees anything. That is a real
/// fail-closed producer check and it is worth having — **and it proves nothing about an adversary,
/// who does not run the producer.** `batch_airs_and_matrices` does not run it at all.
///
/// This tooth exists so the distinction is RECORDED rather than discovered again: the first run of
/// this file asserted a bus name against this message and went red, which is how the two paths were
/// found to differ. The load-bearing verdict is
/// [`the_substituted_addends_are_refused_by_the_routing`]'s, at the verifier.
#[test]
fn the_producer_preflight_also_refuses_and_that_is_not_the_tooth() {
    let rt = descriptor(ROUTED_JSON);
    let t = trace(SUBSTITUTED, ROUTED_WIDTH);
    let pis = public_inputs(&t);
    let refusal =
        must_refuse_or_unsat_panic("substituted addends at the producer pre-flight", || {
            prove_vm_descriptor2(&rt, &t, &pis, &MemBoundaryWitness::default(), &[])
        });
    let reason = refusal.reason();
    assert!(
        reason.contains("lookup multiset does not equal its"),
        "the producer pre-flight is expected to be what refuses on THIS path: {reason}"
    );
    println!("the producer pre-flight refused (a replay, not a circuit): {reason}");
}

/// ⚑ **THE BUS IS NOT REFUSING EVERYTHING — AND IT IS NOT THE ONLY THING THAT REFUSES.**
///
/// Three clauses, and the middle one is a MEASURED correction to what this test first asserted:
///
///  1. the honest chain under its own manifest is ACCEPTED, so the routing balance is satisfiable
///     and every refusal in this file is about a forgery rather than about an unsatisfiable
///     declaration;
///  2. ⚠ a ONE-LIMB bump of an addend cell is refused by a **GATE**, not by the bus — because the
///     row's own RCB arithmetic READS that cell, so moving it without regenerating the row is not
///     an arithmetically honest substitution at all. This file's first draft demanded the bus name
///     here and went red; the honest statement is that the addend cells were already covered
///     against *arbitrary* edits by the sound row, and what they were NOT covered against is the
///     case below;
///  3. …which is the arithmetically-HONEST substitution: a whole chain rebuilt around different
///     real Vesta points, where every gate still holds and **only** the routing bus objects
///     ([`the_substituted_addends_are_refused_by_the_routing`]).
///
/// Read together they say what the routing actually buys: not "the addend cells are now checked"
/// (they were), but "the addends can no longer be a DIFFERENT CONSISTENT SET."
#[test]
fn the_bus_is_not_refusing_everything_and_is_not_the_only_refusal() {
    let rt = descriptor(ROUTED_JSON);

    // (1) satisfiable.
    let ht = trace(ROUTED, ROUTED_WIDTH);
    let hpis = public_inputs(&ht);
    prove_and_verify_adversarial(&rt, &ht, &hpis)
        .expect("the honest chain proves under its own manifest");

    // (2) an arithmetically DISHONEST edit: one addend limb bumped, the rest of the row untouched.
    let mut t = trace(ROUTED, ROUTED_WIDTH);
    let before = t[3][ADD_X];
    let after = before + BabyBear::new(1);
    assert_ne!(
        format!("{before:?}"),
        format!("{after:?}"),
        "the mutation must actually move the cell"
    );
    t[3][ADD_X] = after;
    let pis = public_inputs(&t);
    let what = "a one-limb addend bump (arithmetically dishonest)";
    let refusal = must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&rt, &t, &pis));
    let reason = refusal.reason();
    assert_violated_constraint_not_bus(what, &reason);
    println!("a one-limb bump is caught by the sound ROW, not by the routing: {reason}");
}
