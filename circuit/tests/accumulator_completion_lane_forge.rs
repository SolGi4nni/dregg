//! # ADVERSARIAL AUDIT — the accumulator-root COMPLETION-LANE forge (ORPHAN-SWEEP dangerous #1).
//!
//! ## The claim under attack
//!
//! `docs/audit/ORPHAN-SWEEP.md` §3b/§5.1 asserts a LIVE light-client soundness gap: the deployed
//! `noteSpendV3` / `noteCreateV3` / `createCellV3` carry the nullifier / commitments / cells root
//! update as an inline `MapOp` whose denotation is "lane 0 only — a `scalarRootGroup`; no after-spine
//! keystone forces lanes 1..7 — the root stays ~31-bit" (`EffectVmEmitRotationV3.lean:1570`). The
//! 8-felt binding was said to be proven ONLY about an orphaned assurance-twin (`effAccumWriteV3`), so
//! a PURE LIGHT CLIENT would bind these three roots at ~31 bits (equivocation ~2^15.5), NOT the
//! campaign-claimed faithful ~124 bits.
//!
//! ## The attack (the R1 discipline: forge against the descriptor the LC ACTUALLY RUNS)
//!
//! This is the exact `setfield_completion_lane_forge.rs` pattern, retargeted at the accumulator root.
//! Whereas the existing `vk_epoch_notes_light_client_binding.rs` teeth forge the LANE-0 scalar limb
//! (`B_COMMITMENTS_ROOT` / `B_NULLIFIER_ROOT`) and prove the lane-0 grow-gate bites, they DO NOT test
//! the sweep's precise claim — that the HIGH SEVEN lanes (1..7, the completion limbs) of the root are
//! unbound. This tooth forges EXACTLY those completion lanes:
//!
//!   * Build an honest `NoteCreate` turn through the LIVE WIDE producer
//!     (`generate_rotated_note_create_wide` — the exact function
//!     `sdk::full_turn_proof`/`cipherclerk`/`turn::executor::proof_verify` route a NoteCreate lead
//!     through; see `vk_epoch_notes_light_client_binding::notecreate_forced_on_wire_through_live_wide_producer`).
//!   * Read the deployed descriptor's `.insert` `MapOp` `new_root` 8-felt group columns directly from
//!     the PARSED wide descriptor (`WIDE_REGISTRY_STAGED_TSV`).
//!   * FORGE the high seven `new_root` lanes (cols[1..8]) to arbitrary values ≠ the genuine
//!     sorted-Poseidon2 insert, keeping lane 0 (cols[0], the scalar limb) HONEST. Both registries put
//!     that 8-felt group in the AFTER rotated block — lane 0 at `AFTER_BASE + B_COMMITMENTS_ROOT`
//!     (in-block limb 27), the completion lanes at in-block limbs 75..81 — so the forge is INSIDE the
//!     after-spine absorb window and moves `STATE_COMMIT`. The test therefore re-runs
//!     `recompute_after_blocks_for_test` and re-derives the wide carriers/PIs, leaving the map-op
//!     grow-gate as the ONLY thing that can still bite. Per the sweep, nothing should.
//!   * Run `prove_vm_descriptor2` + `verify_vm_descriptor2` ALONE (the pure LC circuit verify).
//!
//! ## ⚠ THE COMMITTED WIDE GEOMETRY IS NOT THE PRODUCER'S OUTPUT GEOMETRY
//!
//! `generate_rotated_note_create_wide` emits the OLD-geometry wide row (2936 columns). The committed
//! wide registry row is S2-COMPACTED then E1-COMPACTED (1892), and the LIVE route applies exactly that
//! staging immediately after the family dispatch, inside
//! `trace_rotated::generate_rotated_effect_vm_descriptor_and_trace_wide`. A test that calls the family
//! producer DIRECTLY and skips the staging is indexing COMMITTED-geometry columns into an OLD-geometry
//! row. That is precisely what this tooth did between the E1 cutover (`86f1c12a1`, 2026-07-23) and this
//! repair: `new_root` lane 1 (committed col 348) landed on OLD col 348 = BEFORE-block limb 160, read
//! `BB(0)`, and the non-vacuity guard fired — correctly. See [`stage_to_committed_geometry`].
//!
//! ## The verdict this test pins
//!
//!   * If the completion-lane forge PROVES + VERIFIES → the sweep's LIVE gap is REAL: the deployed LC
//!     descriptor binds the accumulator root at only lane-0 ~31 bits.
//!   * If it is UNSAT → the deployed `MapOp` grow-gate binds ALL EIGHT `new_root` lanes to the genuine
//!     node8 sorted insert (~124-bit), and the sweep conflated the Lean after-spine `scalarRootGroup`
//!     denotation with the actually-deployed 8-felt map-op binding — the R1 staged-vs-deployed trap.
//!
//! The second test repeats the forge against the sweep's OWN cited registry — the narrow "1-felt"
//! `V3_STAGED_REGISTRY_TSV` `noteCreateVmDescriptor2R24` — to settle whether even that member binds
//! 8-felt.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::bare_floor_refuse_weld;
use dregg_circuit::effect_vm::trace_rotated::{
    ACCUM_INSERT_HOST_WIDTH, AFTER_BASE, B_COMMITMENTS_ROOT, RotatedBlockWitness,
    append_wide_carriers, compact_e1_columns, compact_s2_columns, empty_caveat_manifest,
    generate_rotated_note_create_trace_with_commitments_tree, generate_rotated_note_create_wide,
    recompute_after_blocks_for_test, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

fn registry_json_static(tsv: &'static str, name: &str) -> &'static str {
    tsv.lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in registry"))
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The insert-shaped map-op's `new_root` 8-felt group COLUMNS, read straight off the parsed
/// descriptor.
///
/// BOTH insert kinds count. The deployed noteCreate members route `MapKind::AafiInsert`
/// (append-at-free-index) — `dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen-gentian-deployed-\
/// bare-refuse` carries exactly one map-op and its `op` is `aafi_insert`. This helper used to match
/// `MapKind::Insert` ALONE, so on the deployed descriptor it found nothing and panicked "has no
/// INSERT map-op", taking both teeth in this file down with it. Which of the two insert shapes the
/// emit picks is not what this file is auditing — the audit is whether the `new_root` COMPLETION
/// LANES are bound — so it accepts either and forges the same 8-felt group.
fn insert_new_root_cols(desc: &EffectVmDescriptor2) -> Vec<usize> {
    for c in &desc.constraints {
        if let VmConstraint2::MapOp(m) = c {
            if matches!(m.op, MapKind::Insert | MapKind::AafiInsert) {
                return m
                    .new_root
                    .iter()
                    .map(|e| match e {
                        LeanExpr::Var(i) => *i,
                        other => panic!("new_root lane is not a Var column: {other:?}"),
                    })
                    .collect();
            }
        }
    }
    panic!(
        "descriptor {} has no insert-shaped map-op (neither Insert nor AafiInsert)",
        desc.name
    );
}

/// **STAGE AN OLD-GEOMETRY WIDE ROW TO THE COMMITTED WIDE GEOMETRY** — the S2 then E1 column
/// deletions the deployed registry row was emitted under (Lean `RotWideCompactS2.compactS2` /
/// `RotWideCompactE1.compactE1`, whose per-member kill-sets Rust reads from the Lean-emitted
/// `s2_compact_generated` / `e1_compact_generated` tables).
///
/// This is not a test convenience: it is the SAME pair of calls the live route makes on the SAME
/// producer output, at `trace_rotated::generate_rotated_effect_vm_descriptor_and_trace_wide`
/// immediately after the per-family dispatch. The per-family wide producers
/// (`generate_rotated_note_create_wide` and its siblings) deliberately stop at the old geometry
/// because the dispatcher owns the staging — so EVERY direct caller owes it, and a caller that
/// forgets is reading committed column indices out of an old-geometry row.
fn stage_to_committed_geometry(trace: &[Vec<BabyBear>], registry_key: &str) -> Vec<Vec<BabyBear>> {
    let mut staged = trace.to_vec();
    compact_s2_columns(&mut staged, registry_key)
        .expect("S2 compaction (the committed wide geometry)");
    compact_e1_columns(&mut staged, registry_key)
        .expect("E1 compaction (the committed wide geometry)");
    staged
}

/// The OLD-geometry column that lands at committed column `committed_col` under S2 ∘ E1 for
/// `registry_key` — i.e. the column a forge must write to move the felt the DEPLOYED descriptor reads.
///
/// DERIVED, never transcribed: an index-tagged probe row is staged through the SAME Lean-emitted kill
/// tables the live route uses, so the mapping follows the next flag day automatically instead of
/// rotting into a hardcoded coordinate (which is the failure mode this whole file just lived through).
fn old_geometry_col(registry_key: &str, old_width: usize, committed_col: usize) -> usize {
    let probe: Vec<Vec<BabyBear>> = vec![(0..old_width).map(|i| BabyBear::new(i as u32)).collect()];
    stage_to_committed_geometry(&probe, registry_key)[0][committed_col].as_u32() as usize
}

/// `true` iff prove/verify REFUSES (Err or panic) on the given trace + PIs — the light-client verdict.
fn refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> bool {
    match classify("refused", || {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// The honest NoteCreate ingredients shared by both registries.
struct Fixture {
    st: CellState,
    effects: Vec<Effect>,
    before_w: rw::RotationWitness,
    after_w: rw::RotationWitness,
    before_commitments: Vec<HeapLeaf>,
    /// The genuine post-insert 8-felt commitments root (the value the grow-gate forces `new_root` to).
    after_root8: [BabyBear; 8],
}

fn build_fixture() -> Fixture {
    let before_balance: i64 = 60_000;
    let value: u64 = 250;
    let cm = BabyBear::new(0xC0FFEE);
    let effect = Effect::NoteCreate {
        commitment: cm,
        value,
    };

    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let before_commitments = vec![
        HeapLeaf::entry(BabyBear::new(0x111), BabyBear::new(1)),
        HeapLeaf::entry(BabyBear::new(0x222), BabyBear::new(1)),
    ];
    // The genuine post-insert root: the fresh commitment (param0 = cm, value = 250) appended.
    let mut honest_after_leaves = before_commitments.clone();
    honest_after_leaves.push(HeapLeaf::entry(cm, BabyBear::new(value as u32)));
    let after_root8 = CanonicalHeapTree8::new(honest_after_leaves, HEAP_TREE_DEPTH).root8();
    let after_root8: [BabyBear; 8] = std::array::from_fn(|i| after_root8[i]);

    Fixture {
        st,
        effects,
        before_w,
        after_w,
        before_commitments,
        after_root8,
    }
}

const FORGED_LANES: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];

/// **THE PRIMARY ATTACK — the deployed WIDE (light-client) geometry.** Forge the commitments-root's
/// completion lanes 1..7 while keeping lane 0 honest; run the pure LC verify. If the deployed `.insert`
/// grow-gate binds all 8 felts, this is UNSAT and the sweep's ~31-bit gap is REFUTED.
#[test]
fn wide_notecreate_completion_lane_forge_verdict() {
    let fx = build_fixture();
    let name =
        rotated_descriptor_name_for_effect(&fx.effects[0]).expect("NoteCreate cohort member");
    assert_eq!(name, "noteCreateVmDescriptor2R24");
    let wide_desc = parse_vm_descriptor2(registry_json_static(WIDE_REGISTRY_STAGED_TSV, name))
        .expect("WIDE noteCreate descriptor parses");
    assert_eq!(
        wide_desc.public_input_count, 67,
        "the wide 8-felt-commit geometry a light client runs (51 base + 16 wide commit PIs)"
    );

    let new_root_cols = insert_new_root_cols(&wide_desc);
    assert_eq!(
        new_root_cols.len(),
        8,
        "the map-op new_root is an 8-felt group"
    );

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();
    let (trace, dpis, map_heaps) = generate_rotated_note_create_wide(
        &fx.st,
        &fx.effects,
        &bridge(&fx.before_w),
        &bridge(&fx.after_w),
        &caveat,
        &fx.before_commitments,
    )
    .expect("live wide note-create producer builds the trace");
    let old_width = trace[0].len();

    // The family producer stops at the OLD wide geometry; the deployed descriptor speaks the
    // S2+E1-COMPACTED one. Stage exactly as the live dispatcher does before reading a single column.
    let htrace = stage_to_committed_geometry(&trace, name);
    // The staged row is the committed geometry MINUS the gentian refuse-weld's gate-internal aux
    // band, which is not producer-emitted: `prove_vm_descriptor2` zero-grows to `trace_width` and
    // fills it (`bare_floor_refuse_weld::fill_refuse_aux`). This is the SAME residue the live
    // dispatcher checks against its claim-PI tail, so pin it exactly rather than with an inequality.
    assert_eq!(
        htrace[0].len() + bare_floor_refuse_weld::refuse_weld_widen(&wide_desc),
        wide_desc.trace_width,
        "staged honest row is the COMMITTED wide geometry the light client runs (old {old_width} → \
         staged {}, + the refuse-weld aux band = committed {})",
        htrace[0].len(),
        wide_desc.trace_width
    );

    // NON-VACUITY: the honest producer fills the completion lanes (cols[1..8]) with the GENUINE
    // 8-felt sorted-insert root lanes 1..7 — and at least one is nonzero (so the forge below moves a
    // genuinely bound felt, not dead padding). Read at the DESCRIPTOR's own columns, on the row the
    // descriptor is actually evaluated against.
    for lane in 1..8 {
        assert_eq!(
            htrace[0][new_root_cols[lane]], fx.after_root8[lane],
            "honest: new_root completion lane {lane} carries the genuine node8 sorted-insert felt"
        );
    }
    assert!(
        (1..8).any(|lane| fx.after_root8[lane] != BabyBear::ZERO),
        "the genuine 8-felt root has ≥1 nonzero high lane (the forge is non-vacuous)"
    );

    // POSITIVE (no downgrade): the honest turn proves + verifies at the wide geometry.
    let proof = prove_vm_descriptor2(&wide_desc, &htrace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: honest wide noteCreate proves");
    verify_vm_descriptor2(&wide_desc, &proof, &dpis)
        .expect("NO DOWNGRADE: honest wide noteCreate verifies");

    // ⚑ THE REFUSAL ORACLE IS NOT STUCK-AT-TRUE. `refused` counts ANY Err-or-panic as a refusal, so a
    // width mismatch, a missing witness or a stray unwrap would read as "the grow-gate bit". Pin that
    // it ACCEPTS this same honest staged trace against the same descriptor / PIs / heaps — then the
    // UNSAT verdict it returns below is a REAL bite of the forged felt, not a harness artifact.
    assert!(
        !refused(&wide_desc, &htrace, &dpis, &mem_boundary, &map_heaps),
        "the refusal oracle must ACCEPT the honest staged trace — otherwise the forge verdict below \
         is vacuous"
    );

    // THE FORGE: set the high seven new_root lanes to arbitrary values ≠ the genuine insert, on EVERY
    // row, keeping lane 0 (the scalar limb) honest. The forge is written in OLD-geometry coordinates
    // (`old_geometry_col` inverts the staging) because the two re-derivations below —
    // `recompute_after_blocks_for_test` and `append_wide_carriers` — both reason in the old geometry;
    // the staging is re-applied afterwards. This 8-felt group is the AFTER rotated block's
    // commitments-root group, INSIDE the after-spine absorb window, so those two re-derivations are
    // what leave the trace FULLY self-consistent (matching carriers + wide commit PIs) with the
    // map-op grow-gate as the ONLY thing that can still bite.
    let old_cols: Vec<usize> = new_root_cols
        .iter()
        .map(|&c| old_geometry_col(name, old_width, c))
        .collect();
    assert_eq!(
        old_cols[0],
        AFTER_BASE + B_COMMITMENTS_ROOT,
        "the deployed map-op's new_root lane 0 IS the AFTER commitments-root limb (not a read-appendix \
         scratch column) — so the group this tooth forges is the one the block commits"
    );
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[old_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    // Keep lane 0 honest (self-check: unchanged).
    assert_eq!(
        ftrace[0][old_cols[0]], trace[0][old_cols[0]],
        "lane 0 (the scalar root limb) stays honest — only the high seven lanes are forged"
    );
    recompute_after_blocks_for_test(&mut ftrace);
    let base_pi_len = dpis.len() - 16;
    let fdpis = append_wide_carriers(
        &mut ftrace,
        dpis[..base_pi_len].to_vec(),
        ACCUM_INSERT_HOST_WIDTH,
    );
    let fstaged = stage_to_committed_geometry(&ftrace, name);

    // Non-vacuity: at the DESCRIPTOR's own columns, every forged completion lane genuinely differs
    // from the honest root — the felt the grow-gate reads MOVED, and it was nonzero and bound before
    // it moved (the honest assertions above).
    assert!(
        (1..8).all(|lane| fstaged[0][new_root_cols[lane]] != fx.after_root8[lane]),
        "the forged high lanes differ from the genuine insert (the grow-gate's UNSAT precondition)"
    );

    let unsat = refused(&wide_desc, &fstaged, &fdpis, &mem_boundary, &map_heaps);
    if unsat {
        eprintln!(
            "ACCUM VERDICT (wide/LC geometry): the commitments-root COMPLETION-LANE forge is UNSAT — \
             the deployed .insert grow-gate binds ALL EIGHT new_root felts to the genuine node8 sorted \
             insert (~124-bit). ORPHAN-SWEEP dangerous #1 is REFUTED (staged-vs-deployed conflation)."
        );
    } else {
        eprintln!(
            "ACCUM VERDICT (wide/LC geometry): the commitments-root COMPLETION-LANE forge \
             PROVES+VERIFIES — the deployed LC descriptor binds only lane 0 (~31-bit). ORPHAN-SWEEP \
             dangerous #1 is a CONFIRMED LIVE gap."
        );
    }
    assert!(
        unsat,
        "ACCUM FORGE LIVE: a noteCreate forged to differ ONLY in the commitments-root's high seven \
         completion lanes proves+verifies through the deployed wide descriptor — the light client \
         binds the accumulator root at lane-0 ~31-bit (ORPHAN-SWEEP dangerous #1 CONFIRMED)."
    );
}

/// **THE SWEEP'S OWN CITED REGISTRY — narrow `V3_STAGED_REGISTRY_TSV` (the alleged lane-0 member).**
/// Repeat the completion-lane forge against the exact "1-felt" member the sweep grounds its ~31-bit
/// claim on. If UNSAT, even that member's inline map-op binds 8-felt.
#[test]
fn narrow_v3_notecreate_completion_lane_forge_verdict() {
    let fx = build_fixture();
    let name =
        rotated_descriptor_name_for_effect(&fx.effects[0]).expect("NoteCreate cohort member");
    let desc = parse_vm_descriptor2(registry_json_static(V3_STAGED_REGISTRY_TSV, name))
        .expect("narrow v3 noteCreate descriptor parses");

    let new_root_cols = insert_new_root_cols(&desc);
    assert_eq!(
        new_root_cols.len(),
        8,
        "the map-op new_root is an 8-felt group"
    );

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();
    let (trace, dpis, map_heaps) = generate_rotated_note_create_trace_with_commitments_tree(
        &fx.st,
        &fx.effects,
        &bridge(&fx.before_w),
        &bridge(&fx.after_w),
        &caveat,
        &fx.before_commitments,
    )
    .expect("narrow commitments-tree note-create producer builds the trace");

    for lane in 1..8 {
        assert_eq!(
            trace[0][new_root_cols[lane]], fx.after_root8[lane],
            "honest (narrow v3): new_root completion lane {lane} carries the genuine node8 insert felt"
        );
    }

    // POSITIVE (no downgrade).
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: honest narrow noteCreate proves");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: honest narrow noteCreate verifies");

    // ⚑ THE REFUSAL ORACLE IS NOT STUCK-AT-TRUE (see the wide tooth): it ACCEPTS the honest trace, so
    // its UNSAT verdict on the forged one below is a real bite.
    assert!(
        !refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "the refusal oracle must ACCEPT the honest narrow trace — otherwise the forge verdict below \
         is vacuous"
    );

    // THE FORGE: high seven lanes → arbitrary ≠ genuine; lane 0 honest. In the narrow geometry the
    // completion lanes (limbs 74..80) ARE within the after-spine absorb window, so we recompute the
    // after-block commit chain and re-derive the NEW_COMMIT PI so the trace is self-consistent; the
    // grow-gate on the map-op remains the operative binder.
    use dregg_circuit::effect_vm::trace_rotated::{B_STATE_COMMIT, V1_PI_COUNT};
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[new_root_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    recompute_after_blocks_for_test(&mut ftrace);
    let mut fdpis = dpis.clone();
    fdpis[V1_PI_COUNT + 1] = ftrace[ftrace.len() - 1][AFTER_BASE + B_STATE_COMMIT];

    let unsat = refused(&desc, &ftrace, &fdpis, &mem_boundary, &map_heaps);
    if unsat {
        eprintln!(
            "ACCUM VERDICT (narrow v3, the sweep's cited registry): the completion-lane forge is UNSAT \
             — even the '1-felt' V3_STAGED member's inline .insert map-op binds all 8 new_root felts. \
             The sweep's ~31-bit lane-0 claim is REFUTED on its own cited descriptor."
        );
    } else {
        eprintln!(
            "ACCUM VERDICT (narrow v3): the completion-lane forge PROVES+VERIFIES — the narrow member \
             binds only lane 0 (~31-bit), as the sweep claimed."
        );
    }
    assert!(
        unsat,
        "the narrow v3 noteCreate completion-lane forge must be UNSAT (the inline map-op binds 8-felt) \
         — else the sweep's lane-0 gap is live on V3_STAGED_REGISTRY_TSV"
    );
}
