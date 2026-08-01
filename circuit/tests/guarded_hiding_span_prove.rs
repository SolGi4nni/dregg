//! # THE HIDDEN-SPAN DESCRIPTOR PROVES — for the first time
//!
//! `circuit/descriptors/by-name/guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json` is the
//! SOLE emitted hidden-span descriptor. Until 2026-08-01 it had **never been proved**, and could
//! not have been: its span-digest tooth asked the Poseidon2 chip for **arity 8** and its wide-blind
//! commit tooth for **arity 14**, and the deployed `Ir2Air::Chip` carries its admission as a
//! degree-7 product over the arity column
//! (`a·(a−2)·(a−3)·(a−4)·(a−7)·(a−11)·(a−16) = 0`, `descriptor_ir2.rs:3073`). Neither 8 nor 14 is a
//! root, so both constraints were unsatisfiable — at that row, for every assignment, forever.
//! Nothing reported it, because nothing had ever tried: there was no prove path for this
//! descriptor anywhere in the tree.
//!
//! That absence is the reason the defect survived. `chip_absorb_arity_admission_gate` now catches
//! the SHAPE statically, and this file closes the other half: it exercises the descriptor at the
//! DEPLOYED prover, in both directions.
//!
//! * [`hidden_span_descriptor_proves_and_verifies`] — the emitted artifact on disk, an honest
//!   witness, `prove_vm_descriptor2` then `verify_vm_descriptor2`. This is the deliverable; a green
//!   arity gate is a claim about bytes, and this is the machine.
//! * [`the_pre_repair_arities_do_not_prove`] — the SAME descriptor with its two arity tags put back
//!   to 8 and 14 (and nothing else changed — the tuples were already zero-padded to `CHIP_RATE`, so
//!   the pre-repair bytes differ from the repaired ones in exactly those two places). It must be
//!   REFUSED. Without this the green above would be consistent with a prover that accepts anything.
//! * [`the_honest_witness_is_the_deployed_absorb`] — the trace this file builds is the deployed
//!   generator's own absorb (`chip_absorb_all_lanes`), not a re-derivation, and each of its three
//!   chip rows is one the deployed AIR accepts (`chip_air_row_accepts`). A witness builder that
//!   re-implements the absorb would prove its own arithmetic, not the circuit's.

use dregg_circuit::descriptor_ir2::VmConstraint2;
use dregg_circuit::descriptor_ir2::{
    CHIP_RATE, EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes,
    chip_air_row_accepts, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use std::path::{Path, PathBuf};

// ============================================================================
// §1 — the column layout, from the Lean author
// ============================================================================
//
// `metatheory/Dregg2/Circuit/Emit/GuardedHidingSpanWideBlindEmit.lean` §1. Restated here only to
// index the trace; every value below is CHECKED against the descriptor's own tuples in
// `layout_matches_the_emitted_descriptor`, so a drift in the Lean layout fails this file rather
// than silently proving a different circuit.

/// 8 hidden span symbol lanes.
const G_SPAN: usize = 0;
/// `span_digest8 = A11(span ‖ 0,0,0)`.
const G_DIGEST: usize = 8;
/// `C_T`, the public context commitment (PI 0..8).
const G_CT: usize = 16;
/// The 5 fresh blinding lanes — hidden, never PI-bound.
const G_BLIND: usize = 24;
/// `MID = A16(span_digest8 ‖ C_T)`.
const G_MID: usize = 29;
/// `hole_commit = A16(MID ‖ r₀..r₄ ‖ 0,0,0)` (PI 8..16).
const G_HOLE: usize = 37;
/// `guard_table_commitment` (PI 16..24) — PI-pinned, no constraint.
const G_GUARD: usize = 45;
const GHSW_WIDTH: usize = 53;
const GHS_PI_COUNT: usize = 24;
const BLIND_LANES: usize = 5;

/// The two absorb arities the repair moved to, and the two it moved off.
const SPAN_ARITY: u32 = 11;
const COMMIT_ARITY: u32 = 16;
const STAGE1_ARITY: u32 = 16;
const PRE_REPAIR_SPAN_ARITY: u32 = 8;
const PRE_REPAIR_COMMIT_ARITY: u32 = 14;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate dir has a parent")
        .to_path_buf()
}

fn descriptor_path() -> PathBuf {
    repo_root().join(
        "circuit/descriptors/by-name/guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json",
    )
}

fn emitted_json() -> String {
    std::fs::read_to_string(descriptor_path())
        .expect("the emitted hidden-span descriptor is on disk")
}

fn emitted_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(&emitted_json()).expect("the deployed parser accepts it")
}

// ============================================================================
// §2 — the honest witness, built by the DEPLOYED absorb
// ============================================================================

/// One absorb: hand `chip_absorb_all_lanes` — the function `build_traces` itself calls — the arity
/// and the (zero-padded) input lanes, and take all 8 output lanes.
fn absorb(arity: u32, ins: &[BabyBear]) -> [BabyBear; 8] {
    assert!(
        ins.len() <= CHIP_RATE,
        "absorb block exceeds the chip's lanes"
    );
    let mut lanes = [BabyBear::ZERO; CHIP_RATE];
    lanes[..ins.len()].copy_from_slice(ins);
    chip_absorb_all_lanes(arity as usize, &lanes)
}

struct Witness {
    row: Vec<BabyBear>,
    pis: Vec<BabyBear>,
    /// The three absorb blocks, kept for the AIR-acceptance cross-check.
    blocks: Vec<(u32, Vec<BabyBear>)>,
}

/// Build an honest hidden-span opening: a chosen span, a chosen public context `C_T`, a chosen
/// 5-lane blinding vector, and the two folds the descriptor constrains.
fn honest_witness(seed: u32) -> Witness {
    let f = |k: u32| BabyBear::new(seed.wrapping_mul(1_000_003).wrapping_add(k));

    let span: Vec<BabyBear> = (0..8).map(|k| f(0x100 + k)).collect();
    let ct: Vec<BabyBear> = (0..8).map(|k| f(0x200 + k)).collect();
    let blind: Vec<BabyBear> = (0..BLIND_LANES as u32).map(|k| f(0x300 + k)).collect();
    let guard: Vec<BabyBear> = (0..8).map(|k| f(0x400 + k)).collect();

    // span_digest8 = A11(span8 ‖ 0,0,0) — the three pad lanes are what buys the ADMITTED arity 11.
    let mut span_block = span.clone();
    span_block.extend([BabyBear::ZERO; 3]);
    let digest = absorb(SPAN_ARITY, &span_block);

    // MID = A16(span_digest8 ‖ C_T)
    let mut stage1_block = digest.to_vec();
    stage1_block.extend_from_slice(&ct);
    let mid = absorb(STAGE1_ARITY, &stage1_block);

    // hole_commit = A16(MID ‖ r₀..r₄ ‖ 0,0,0)
    let mut stage2_block = mid.to_vec();
    stage2_block.extend_from_slice(&blind);
    stage2_block.extend([BabyBear::ZERO; 3]);
    let hole = absorb(COMMIT_ARITY, &stage2_block);

    let mut row = vec![BabyBear::ZERO; GHSW_WIDTH];
    row[G_SPAN..G_SPAN + 8].copy_from_slice(&span);
    row[G_DIGEST..G_DIGEST + 8].copy_from_slice(&digest);
    row[G_CT..G_CT + 8].copy_from_slice(&ct);
    row[G_BLIND..G_BLIND + BLIND_LANES].copy_from_slice(&blind);
    row[G_MID..G_MID + 8].copy_from_slice(&mid);
    row[G_HOLE..G_HOLE + 8].copy_from_slice(&hole);
    row[G_GUARD..G_GUARD + 8].copy_from_slice(&guard);

    let mut pis = Vec::with_capacity(GHS_PI_COUNT);
    pis.extend_from_slice(&ct);
    pis.extend_from_slice(&hole);
    pis.extend_from_slice(&guard);

    Witness {
        row,
        pis,
        blocks: vec![
            (SPAN_ARITY, span_block),
            (STAGE1_ARITY, stage1_block),
            (COMMIT_ARITY, stage2_block),
        ],
    }
}

/// Every row identical: the three chip lookups are row-local and must hold at EVERY row, and the
/// PI pins read the first. Two rows so the trace is not degenerate at height 1.
fn honest_trace(w: &Witness) -> Vec<Vec<BabyBear>> {
    vec![w.row.clone(), w.row.clone()]
}

// ============================================================================
// §3 — the layout this file indexes IS the descriptor's
// ============================================================================

/// Read the `(arity, input columns, output columns)` of each chip lookup straight off the parsed
/// descriptor, so the constants in §1 cannot drift away from the Lean author unnoticed.
fn chip_sites(desc: &EffectVmDescriptor2) -> Vec<(i64, Vec<Option<usize>>, Vec<usize>)> {
    let mut out = Vec::new();
    for k in &desc.constraints {
        let VmConstraint2::Lookup(l) = k else {
            continue;
        };
        let LeanExpr::Const(arity) = l.tuple[0] else {
            panic!("chip lookup arity must be a constant")
        };
        let ins = (0..CHIP_RATE)
            .map(|i| match l.tuple[1 + i] {
                LeanExpr::Var(c) => Some(c),
                LeanExpr::Const(0) => None,
                ref e => panic!("unexpected chip input lane {e:?}"),
            })
            .collect();
        let outs = (0..8)
            .map(|j| match l.tuple[1 + CHIP_RATE + j] {
                LeanExpr::Var(c) => c,
                ref e => panic!("chip output lane must be a column, got {e:?}"),
            })
            .collect();
        out.push((arity, ins, outs));
    }
    out
}

#[test]
fn layout_matches_the_emitted_descriptor() {
    let desc = emitted_descriptor();
    assert_eq!(
        desc.name,
        "dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1"
    );
    assert_eq!(desc.trace_width, GHSW_WIDTH);
    assert_eq!(desc.public_input_count, GHS_PI_COUNT);

    let sites = chip_sites(&desc);
    assert_eq!(
        sites.len(),
        3,
        "span digest, stage-1 fold, wide-blind tooth"
    );

    // Site 0 — the span digest: arity 11, the 8 span lanes then three literal-zero pad lanes.
    let (a0, in0, out0) = &sites[0];
    assert_eq!(*a0, SPAN_ARITY as i64);
    assert_eq!(
        in0[..8],
        (G_SPAN..G_SPAN + 8).map(Some).collect::<Vec<_>>()[..]
    );
    assert!(
        in0[8..].iter().all(Option::is_none),
        "the pad lanes are literal zeros"
    );
    assert_eq!(*out0, (G_DIGEST..G_DIGEST + 8).collect::<Vec<_>>());

    // Site 1 — the stage-1 fold: arity 16, span_digest8 ‖ C_T, all sixteen lanes live.
    let (a1, in1, out1) = &sites[1];
    assert_eq!(*a1, STAGE1_ARITY as i64);
    let stage1_cols: Vec<Option<usize>> = (G_DIGEST..G_DIGEST + 8)
        .chain(G_CT..G_CT + 8)
        .map(Some)
        .collect();
    assert_eq!(*in1, stage1_cols);
    assert_eq!(*out1, (G_MID..G_MID + 8).collect::<Vec<_>>());

    // Site 2 — the wide-blind tooth: arity 16, MID ‖ the whole 5-lane blinding block ‖ pad.
    let (a2, in2, out2) = &sites[2];
    assert_eq!(*a2, COMMIT_ARITY as i64);
    let stage2_cols: Vec<Option<usize>> = (G_MID..G_MID + 8)
        .chain(G_BLIND..G_BLIND + BLIND_LANES)
        .map(Some)
        .chain(std::iter::repeat_n(None, 3))
        .collect();
    assert_eq!(*in2, stage2_cols);
    assert_eq!(*out2, (G_HOLE..G_HOLE + 8).collect::<Vec<_>>());

    // No blinding lane is published. The hiding bound `Q/|R|` is only meaningful while `r` is
    // witness-only, and a PI pin on any of the five would void it outright.
    for c in G_BLIND..G_BLIND + BLIND_LANES {
        assert!(
            !desc.constraints.iter().any(|k| matches!(
                k,
                VmConstraint2::Base(VmConstraint::PiBinding { col: pc, .. }) if *pc == c
            )),
            "blinding lane column {c} is PI-bound — the blinding is not hidden"
        );
    }
}

// ============================================================================
// §4 — the deliverable, and its negative
// ============================================================================

#[test]
fn the_honest_witness_is_the_deployed_absorb() {
    let w = honest_witness(7);
    // Each absorb block, at its arity, is a row the DEPLOYED chip AIR accepts. This is the same
    // predicate `chip_absorb_arity_admission_gate` derives the admitted set from — asked here of
    // the ACTUAL blocks this descriptor absorbs, not of the all-zero probe row.
    for (arity, block) in &w.blocks {
        let mut lanes = [BabyBear::ZERO; CHIP_RATE];
        lanes[..block.len()].copy_from_slice(block);
        assert!(
            chip_air_row_accepts(*arity, &lanes),
            "the deployed chip AIR REFUSES the honest arity-{arity} absorb this descriptor emits"
        );
    }
    // And the pre-repair arities are refused on the very same blocks — the defect, measured at the
    // AIR rather than argued from the admitted set.
    let mut span_lanes = [BabyBear::ZERO; CHIP_RATE];
    span_lanes[..8].copy_from_slice(&w.blocks[0].1[..8]);
    assert!(
        !chip_air_row_accepts(PRE_REPAIR_SPAN_ARITY, &span_lanes),
        "arity 8 is accepted — the wound this file documents is not real"
    );
    let mut commit_lanes = [BabyBear::ZERO; CHIP_RATE];
    commit_lanes[..13].copy_from_slice(&w.blocks[2].1[..13]);
    assert!(
        !chip_air_row_accepts(PRE_REPAIR_COMMIT_ARITY, &commit_lanes),
        "arity 14 is accepted — the wound this file documents is not real"
    );
}

/// **THE DELIVERABLE.** The emitted hidden-span descriptor proves and verifies at the deployed
/// prover. It never had.
#[test]
fn hidden_span_descriptor_proves_and_verifies() {
    let desc = emitted_descriptor();
    let w = honest_witness(7);
    assert_eq!(w.pis.len(), desc.public_input_count, "PI shape");
    let trace = honest_trace(&w);

    let proof = prove_vm_descriptor2(&desc, &trace, &w.pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest hidden-span opening must PROVE against the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &w.pis).expect("and the proof must VERIFY");
}

/// The same, on a second independent opening — so the green above is not one lucky witness.
#[test]
fn hidden_span_descriptor_proves_on_a_second_opening() {
    let desc = emitted_descriptor();
    let w = honest_witness(0x5EED);
    let trace = honest_trace(&w);
    let proof = prove_vm_descriptor2(&desc, &trace, &w.pis, &MemBoundaryWitness::default(), &[])
        .expect("a second honest opening proves");
    verify_vm_descriptor2(&desc, &proof, &w.pis).expect("and verifies");
}

/// **THE NEGATIVE — the descriptor as it stood before the repair is UNPROVABLE.**
///
/// The pre-repair bytes are the repaired bytes with the two arity tags put back: the tuples were
/// already zero-padded to `CHIP_RATE` by `padToE`, so `11 → 8` and `16 → 14` in the first and third
/// lookups is the WHOLE difference (verified below by reconstructing from the emitted JSON). The
/// honest witness — the same span, context and blinding — must be refused, because at arities 8 and
/// 14 the admission product does not vanish and no assignment exists.
#[test]
fn the_pre_repair_arities_do_not_prove() {
    let repaired = emitted_json();
    // Reconstruct the pre-repair shape by rewriting exactly the two arity tags, positionally: the
    // first `"const","v":11` and the first `"const","v":16` that open a lookup tuple.
    let pre = repaired
        .replacen(
            "\"tuple\":[{\"t\":\"const\",\"v\":11}",
            "\"tuple\":[{\"t\":\"const\",\"v\":8}",
            1,
        )
        .replacen(
            "\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":29}",
            "\"tuple\":[{\"t\":\"const\",\"v\":14},{\"t\":\"var\",\"v\":29}",
            1,
        );
    assert_ne!(pre, repaired, "the reconstruction must actually differ");
    let pre_desc = parse_vm_descriptor2(&pre).expect("the pre-repair bytes still parse");
    let arities: Vec<i64> = chip_sites(&pre_desc)
        .into_iter()
        .map(|(a, _, _)| a)
        .collect();
    assert_eq!(
        arities,
        vec![
            PRE_REPAIR_SPAN_ARITY as i64,
            STAGE1_ARITY as i64,
            PRE_REPAIR_COMMIT_ARITY as i64
        ],
        "the reconstruction is the pre-repair arity triple"
    );

    let w = honest_witness(7);
    let trace = honest_trace(&w);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(
            &pre_desc,
            &trace,
            &w.pis,
            &MemBoundaryWitness::default(),
            &[],
        )
        .and_then(|p| verify_vm_descriptor2(&pre_desc, &p, &w.pis))
    }));
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "the PRE-REPAIR descriptor (arities 8 and 14) PROVED — then the arity admission product is \
         not doing what this repair claims, and the repair is unnecessary"
    );
}
