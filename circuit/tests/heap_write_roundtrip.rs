//! # HEAP-WRITE producer≡descriptor ROUNDTRIP + AFTER-root 8-felt binding forge.
//!
//! ## The gap under attack (R3, v13-class)
//!
//! `heapWriteVmDescriptor2R24` is the write-bearing Class-A member. Unlike the effect-dispatched
//! cohort it has NO live selector — there is no `Effect::HeapWrite` variant at all, so it is reached
//! only through the dedicated per-family producer [`generate_rotated_heap_write_wide`]. R3 flagged it
//! as the sharpest surviving v13-class gap: a DISTINCT heap-splice producer, structurally pinned only,
//! with no end-to-end prove+verify roundtrip that would catch the producer silently diverging from the
//! committed descriptor while the drift gate stays green (the v13 stale-descriptor scare class).
//!
//! The staleness risk is REAL and visible: the source carries drifted geometry comments whose ACTUAL
//! runtime values moved under them, and a sibling structural test
//! (`heap_write_deployed_root_forced.rs`) hard-codes a STALE `new_root` lane-0 column that no longer
//! matches the committed descriptor. So the only trustworthy check is an EXECUTED roundtrip that
//! binds the producer's laid columns to the committed descriptor's map-op columns through an actual
//! proof — and every geometry here is DERIVED (host + carriers − S2 − E1; columns pushed through the
//! deployed compaction) rather than transcribed, so the next flag-day moves the pins with the bytes.
//!
//! ## Which descriptor the wire actually runs
//!
//! The DEPLOYED light-client verifier (`turn/src/executor/proof_verify.rs:1088`) resolves the rotated
//! member out of `WIDE_REGISTRY_STAGED_TSV`, then prefers its welded twin — EXCEPT for the four
//! `LIVE_ONLY_BARE_KEYS` (`:1146`), of which `heapWriteVmDescriptor2R24` is one: its genuine
//! before→after projection is multi-domain (heap + registers), so the single-domain cohort weld
//! refuses it and the producer keeps it on the BARE wide leg. So the bare-wide member this file
//! proves against **is** the member the wire runs, and the forge below is a verdict on the deployed
//! path — not on a staged twin.
//!
//! (An earlier revision of this file claimed the opposite — that the deployed light client verifies
//! against the narrow `V3_STAGED_REGISTRY_TSV` — and carried two v3-live legs built on that claim.
//! It is FALSE at HEAD; see the retirement note below.)
//!
//! ## What this file pins
//!
//!  (a) ROUNDTRIP — the wide producer's trace PROVES + light-client VERIFIES against the COMMITTED
//!      bare-wide `heapWriteVmDescriptor2R24`, AND the producer's written after-root columns are
//!      byte-identical to the descriptor's `.write` map-op `new_root` columns — asserted as the S2+E1
//!      IMAGE of `AFTER_BASE + HEAP_ROOT_GROUP`, so the BANDS are pinned and not merely the count
//!      (the anti-drift catcher). It also pins the deployed producer against its own pre-compaction
//!      stage: `generate_rotated_heap_write_wide` must be byte-identical to
//!      `generate_rotated_heap_write_wide_raw` followed by the two deployed compaction calls.
//!  (b) AFTER-ROOT 8-FELT FORGE — forge the `.write` `new_root` completion lanes 1..7 to garbage
//!      while keeping lane 0 honest, **on the RAW pre-compaction row**, recompute the after
//!      block-commit + wide carriers there, then carry the forgery through the SAME compaction the
//!      honest row takes, and run the pure LC verify. If UNSAT, the deployed `.write` map-op binds
//!      ALL EIGHT after-root felts to the genuine sorted-Merkle splice (~124-bit), not lane-0
//!      (~31-bit).
//!
//! ## Why (b) is built on the RAW row (this file's own repaired vacuity)
//!
//! The previous revision forged the ALREADY-COMPACTED row and then called `append_wide_carriers` on
//! it, which re-inflated 1963 → 3065. `prove_vm_descriptor2` then refused on SHAPE (`base row width
//! 3065 must equal descriptor trace_width 1963`) and the tooth's `refused()` read that width
//! complaint as an unsat verdict. It was VACUOUS: neutering the forgery entirely — writing all eight
//! lanes back honest — left the test GREEN and still printing "binds ALL EIGHT after-root felts".
//!
//! Two facts force the raw-row construction. The S2 band `[bb+418, bb+478)` deletes the AFTER block's
//! entire 1-felt chain-carrier stratum, so a patched AFTER block-commit has nowhere to land on a
//! compacted row; and the wide carriers sit at `HEAP_WRITE_HOST_WIDTH`, a RAW coordinate. So the
//! forgery is written at the raw rotated coordinates and carried through `compact_s2_columns ∘
//! compact_e1_columns` beside the honest row — the same method the frozen-audit-slot forgery uses in
//! `effect_vm_rotation_flip.rs` (`cd24980fe8`), and for the same reason: the deleted bands would
//! otherwise renumber the forged column out from under the tooth.
//!
//! Every refusal in this file goes through [`refusal_reason`], which pins the committed SHAPE first
//! and REDs on a shape fault, so a width complaint can never be laundered into an unsat verdict
//! again.
//!
//! ## Retired: the two v3-live legs
//!
//! `roundtrip_v3_live_descriptor` and `after_root_forge_is_unsat_against_DEPLOYED_v3_registry` paired
//! the wide producer's TRUNCATED trace with the narrow `V3_STAGED_REGISTRY_TSV` member. That member
//! is STRANDED at HEAD: no producer emits its geometry (there is no `Effect::HeapWrite` variant, so no
//! narrow V3 path reaches it), and its S2 bands (read off `S2_COMPACT_TABLE`, not transcribed — they
//! moved at the 2026-07-26 vestige flag-day) all lie inside the narrow v3 width, so no prefix or
//! re-inflation of the wide row recovers it. Both legs were RED, and the premise they rested on (that
//! v3-live is the deployed registry) is false. Their distinct assertions are PORTED onto the wide tooth
//! below, marked `PORTED`.
//!
//! ## The 2026-07-26 VESTIGE FLAG-DAY, and why this file is the arbiter of it
//!
//! `EffectVmEmitHeapRoot.siteHeapLeaf` — an arity-2 `hash[addr, value]` chip lookup that stopped being
//! any leaf of any deployed tree when `heap_root.rs` became an IMT on 2026-07-12 — was DELETED from the
//! emit, moving this member's bytes in all three committed registries and therefore its VK. The
//! deletion is structurally pinned in `heap_write_deployed_root_forced.rs`; what THIS file supplies is
//! the executed verdict, and it is the one that matters: the honest producer still PROVES and the light
//! client still VERIFIES against the exact member the wire runs, and the after-root forge is still
//! UNSAT. Every geometry here is DERIVED (host + carriers − S2 − E1, columns pushed through the
//! deployed compaction), so it followed the moved bytes rather than needing a hand edit.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MemBoundaryWitness, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::layout_generated::HEAP_ROOT_GROUP;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_STATE_COMMIT, BEFORE_BASE, HEAP_WRITE_HOST_WIDTH, RotatedBlockWitness,
    WIDE_CARRIER_APPENDIX, append_wide_carriers, compact_e1_columns, compact_s2_columns,
    empty_caveat_manifest, generate_rotated_heap_write_wide, generate_rotated_heap_write_wide_raw,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{Outcome, assert_committed_shape, classify, shape_fault};
use dregg_turn::rotation_witness as rw;

const KEY: &str = "heapWriteVmDescriptor2R24";

fn registry_json(tsv: &'static str, name: &str) -> &'static str {
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

/// Total columns this member's OWN E1 kill-set (the Epoch-1 SECOND flag-day) deletes, summed from
/// the Lean-emitted single source `E1_COMPACT_TABLE` — exactly what `compact_e1_columns` drains.
fn e1_deleted_cols(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, runs)| runs.iter().map(|(a, b)| b - a).sum())
        .unwrap_or_else(|| panic!("{key} not in E1_COMPACT_TABLE"))
}

/// The RAW (pre-compaction) wide row width the producer assembles before it compacts: the OPTION-I
/// after-spine host + the wide-carrier appendix.
fn raw_wide_width() -> usize {
    HEAP_WRITE_HOST_WIDTH + WIDE_CARRIER_APPENDIX
}

/// **THE COMMITTED BARE-WIDE WIDTH, DERIVED** — the raw wide row MINUS the S2 stratum (Epoch 1: the
/// two rotated 1-felt chain carrier bands + their 840 graduated chip-lane columns) MINUS this
/// member's own E1 kill-set. Both deletions come from the Lean-emitted tables the producer itself
/// drains, so this pin follows the next compaction instead of rotting into a dead gate.
fn committed_wide_width() -> usize {
    raw_wide_width()
        - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
        - e1_deleted_cols(KEY)
}

/// The RAW (pre-compaction) columns of the AFTER rotated block's heap-root 8-felt group — lane 0 the
/// scalar heap-root limb, lanes 1..7 the completion limbs — read from the Lean-emitted layout row
/// `HEAP_ROOT_GROUP` rather than transcribed. These are the columns the producer writes the faithful
/// 8-felt splice root into, and the columns the `.write` map-op's `new_root` binds.
fn raw_after_heap_root_cols() -> Vec<usize> {
    HEAP_ROOT_GROUP
        .iter()
        .map(|&off| AFTER_BASE + off)
        .collect()
}

/// **THE COMPACTION IMAGE of raw producer columns — the BAND pin.** Where each pre-compaction column
/// lands in the S2+E1-compacted member, computed by running the DEPLOYED compaction
/// (`compact_s2_columns` then `compact_e1_columns` — the very calls the wide producer makes) over a
/// row of column IDENTITIES. A column COUNT is not enough: a table regen that deletes a DIFFERENT
/// band of the SAME size renumbers these columns, and the honest proof would go UNSAT with no
/// explanation. Deriving the image makes that regen fail HERE, naming the moved column.
fn compacted_cols(key: &str, raw_width: usize, raw_cols: &[usize]) -> Vec<usize> {
    let mut identity: Vec<Vec<BabyBear>> =
        vec![(0..raw_width).map(|c| BabyBear::new(c as u32)).collect()];
    compact_s2_columns(&mut identity, key).expect("S2 compaction of the identity row");
    compact_e1_columns(&mut identity, key).expect("E1 compaction of the identity row");
    raw_cols
        .iter()
        .map(|&raw| {
            identity[0]
                .iter()
                .position(|&v| v == BabyBear::new(raw as u32))
                .unwrap_or_else(|| {
                    panic!(
                        "raw column {raw} was DELETED by the {key} kill-set — it cannot be a \
                            surviving binding column"
                    )
                })
        })
        .collect()
}

/// The `.write` map-op's `new_root` 8-felt group COLUMNS, straight off the parsed descriptor.
fn write_new_root_cols(desc: &EffectVmDescriptor2) -> Vec<usize> {
    for c in &desc.constraints {
        if let VmConstraint2::MapOp(m) = c {
            if m.op == MapKind::Write {
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
    panic!("descriptor {} has no WRITE map-op", desc.name);
}

/// **THE DEPLOYED COMPACTION** — the two calls `generate_rotated_heap_write_wide` itself makes on the
/// raw row, in the order it makes them (E1's bands are stated in the S2-compacted geometry, so the
/// order is load-bearing). Applied to the honest row and the forged row ALIKE.
fn compact_like_the_producer(trace: &mut Vec<Vec<BabyBear>>) {
    compact_s2_columns(trace, KEY).expect("deployed S2 compaction of the heap-write row");
    compact_e1_columns(trace, KEY).expect("deployed E1 compaction of the heap-write row");
}

/// **THE REFUSAL DISCRIMINATOR.** Run prove+verify and return the refusal REASON, or `None` if the
/// witness was ACCEPTED.
///
/// Both layers now live in [`dregg_circuit::refusal`], so every tooth in the tree inherits them —
/// this file's private copies were lifted there:
///
///  * the committed SHAPE is pinned first ([`assert_committed_shape`]), so the prover is genuinely
///    asked about this witness rather than about the row's width;
///  * [`classify`] REDs on any panic that is not the p3 debug prover's documented unsat verdict (a
///    stray unwrap, a trace-assembly `debug_assert`, a height assert) **and** on any `Err` naming a
///    `refusal::SHAPE_FAULT_MARKERS` arity fault.
fn refusal_reason(
    what: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> Option<String> {
    assert_committed_shape(what, desc, trace, dpis);
    match classify(what, || {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal by the constraint system.
        Outcome::UnsatPanic(m) => Some(format!("p3 unsat verdict — {m}")),
        // The pre-flight in-trace replay refusing fail-closed (the PREFERRED mechanism per
        // `dregg_circuit::refusal`); `classify` has already redded any width/arity complaint.
        Outcome::Err(e) => Some(format!("fail-closed replay refusal — {e}")),
        Outcome::Accepted(_) => None,
    }
}

/// Build the honest wide heap-write turn (the exact fixture `wide_new_members_cover` uses). With
/// `raw = true` it returns the PRE-compaction row [`generate_rotated_heap_write_wide_raw`] assembles;
/// with `raw = false` it returns exactly what the DEPLOYED producer emits. Same inputs either way,
/// so the two are comparable byte-for-byte.
fn heap_write_fixture(raw: bool) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let st = CellState::new(100, 5);
    let value_full: u64 = 30;
    let effects = vec![Effect::Mint {
        value_lo: BabyBear::new(value_full as u32),
        mint_hash: BabyBear::new(0),
        value_full,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(100, 5);
    let after_cell = producer_cell(100 + value_full as i64, 6);
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

    let coll = BabyBear::new(42);
    let key = BabyBear::new(7);
    let value = BabyBear::new(123);
    let mut absorb_in = [BabyBear::new(0); 11];
    absorb_in[0] = coll;
    absorb_in[1] = key;
    let addr = chip_absorb_all_lanes(2, &absorb_in)[0];
    let heap = vec![
        HeapLeaf::entry(addr, BabyBear::new(9)),
        HeapLeaf::entry(BabyBear::new(999_983), BabyBear::new(1)),
    ];

    let built = if raw {
        generate_rotated_heap_write_wide_raw(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &empty_caveat_manifest(),
            coll,
            key,
            value,
            &heap,
        )
    } else {
        generate_rotated_heap_write_wide(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &empty_caveat_manifest(),
            coll,
            key,
            value,
            &heap,
        )
    };
    let (trace, dpis, map_heaps) = built.expect("wide heap-write generation");
    (trace, dpis, map_heaps)
}

/// The honest turn as the DEPLOYED producer emits it (compacted).
fn honest_heap_write() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    heap_write_fixture(false)
}

/// **(a) ROUNDTRIP + ANTI-DRIFT.** The wide producer PROVES + light-client VERIFIES against the
/// COMMITTED `heapWriteVmDescriptor2R24`, and the columns the producer laid the after heap-root group
/// into are byte-identical to the committed descriptor's `.write` map-op `new_root` columns. This is
/// the executed check the structural teeth cannot give: a producer that laid the group at the STALE
/// (188/237-based) columns while the committed descriptor moved to 188/415 would be UNSAT here.
///
/// It also pins the deployed producer against its own pre-compaction stage — the accessor the forge
/// below builds on cannot drift from what deploys.
#[test]
fn roundtrip_wide_producer_matches_committed_descriptor() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY))
        .expect("committed bare-wide heapWriteVmDescriptor2R24 parses");
    assert_eq!(
        wide_desc.trace_width,
        committed_wide_width(),
        "committed bare-wide width"
    );
    assert_eq!(wide_desc.public_input_count, 20, "committed bare-wide PIs");

    let new_root_cols = write_new_root_cols(&wide_desc);
    assert_eq!(new_root_cols.len(), 8, "after-root is an 8-felt group");
    // THE ANTI-DRIFT PIN, DERIVED THROUGH THE BANDS. The producer writes the after heap-root group
    // at the RAW columns `AFTER_BASE + HEAP_ROOT_GROUP[lane]`, then compacts; the committed
    // descriptor's `new_root` must be exactly the image of those raw columns under the DEPLOYED S2
    // + E1 kill-sets. This binds the producer and the frozen descriptor to the same felts through
    // the same bands — a compaction that drops different bands of the same size REDs here rather
    // than leaving the honest proof mysteriously UNSAT.
    let raw_cols = raw_after_heap_root_cols();
    assert_eq!(
        new_root_cols,
        compacted_cols(KEY, raw_wide_width(), &raw_cols),
        "committed .write new_root columns == the S2+E1 image of AFTER_BASE + HEAP_ROOT_GROUP — the \
         anti-drift pin"
    );
    // PORTED (retired v3-live legs asserted "all 8 lanes within the width"): every lane survives the
    // compaction AND lands inside the row the light client is handed. `compacted_cols` REDs by name
    // if a lane's raw column was DELETED; this pins the other half.
    assert!(
        new_root_cols.iter().all(|&c| c < wide_desc.trace_width),
        "every .write new_root lane must land inside the committed width {} — got {new_root_cols:?}",
        wide_desc.trace_width
    );

    // THE PRE-COMPACTION IDENTITY PIN. `generate_rotated_heap_write_wide` is exactly
    // `generate_rotated_heap_write_wide_raw` + the two deployed compaction calls. The forge below
    // builds on the raw accessor, so this is what keeps that accessor honest: if the deployed entry
    // ever grows a step the raw one lacks, the forgery would be exercising a different object and
    // this REDs first.
    let (raw_trace, raw_dpis, raw_heaps) = heap_write_fixture(true);
    assert_eq!(
        raw_trace[0].len(),
        raw_wide_width(),
        "the pre-compaction row is the OPTION-I host + wide carriers"
    );
    let mut raw_then_compacted = raw_trace.clone();
    compact_like_the_producer(&mut raw_then_compacted);
    let (trace, dpis, map_heaps) = honest_heap_write();
    assert_eq!(
        raw_then_compacted, trace,
        "DEPLOYED producer == raw producer + the deployed compaction (trace)"
    );
    assert_eq!(
        raw_dpis, dpis,
        "DEPLOYED producer == raw producer + the deployed compaction (public inputs)"
    );
    assert_eq!(
        raw_heaps.len(),
        map_heaps.len(),
        "DEPLOYED producer == raw producer + the deployed compaction (map heap count)"
    );
    for (h_raw, h_dep) in raw_heaps.iter().zip(map_heaps.iter()) {
        assert_eq!(
            h_raw.len(),
            h_dep.len(),
            "DEPLOYED producer == raw producer (map heap leaf count)"
        );
        for (l_raw, l_dep) in h_raw.iter().zip(h_dep.iter()) {
            assert!(
                l_raw.addr == l_dep.addr
                    && l_raw.value == l_dep.value
                    && l_raw.next_addr == l_dep.next_addr,
                "DEPLOYED producer == raw producer (map heap leaf)"
            );
        }
    }

    assert_eq!(
        trace[0].len(),
        wide_desc.trace_width,
        "producer width == descriptor width"
    );
    assert_eq!(
        dpis.len(),
        wide_desc.public_input_count,
        "producer PI count == descriptor PI count"
    );

    // PORTED (retired v3-live legs pinned `write_new_root_cols(v3) == raw_after_heap_root_cols()`
    // against a descriptor with NO producer at HEAD): the RAW-coordinate claim now rides the path
    // that actually deploys — the producer lays the genuine 8-felt splice root at `AFTER_BASE +
    // HEAP_ROOT_GROUP` on the pre-compaction row, and compaction carries those same felts into the
    // committed `new_root` columns.
    for lane in 0..8 {
        assert_eq!(
            raw_trace[0][raw_cols[lane]], trace[0][new_root_cols[lane]],
            "after-root lane {lane}: raw column {} and compacted column {} must carry the SAME felt",
            raw_cols[lane], new_root_cols[lane]
        );
    }

    // Non-vacuity: the producer actually laid the genuine 8-felt splice root into those columns, with
    // ≥1 nonzero completion lane (so the forge below moves a genuinely bound felt).
    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();
    assert!(
        (1..8).any(|l| honest_root[l] != BabyBear::ZERO),
        "the genuine 8-felt after-root has ≥1 nonzero completion lane"
    );

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&wide_desc, &trace, &dpis, &mb, &map_heaps)
        .expect("ROUNDTRIP: wide heap-write producer must PROVE against the committed descriptor");
    verify_vm_descriptor2(&wide_desc, &proof, &dpis)
        .expect("ROUNDTRIP: light client must VERIFY the wide heap-write proof");
    eprintln!(
        "HEAP-WRITE ROUNDTRIP (bare-wide {}/{}): producer≡descriptor — PROVED + VERIFIED, after-root \
         group laid at the committed new_root columns {new_root_cols:?} (raw {raw_cols:?}). This is \
         the member turn/src/executor/proof_verify.rs:1088 resolves and :1146 keeps BARE. Coverage \
         gap CLOSED, benign.",
        wide_desc.trace_width, wide_desc.public_input_count
    );
}

const FORGED_LANES: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];

/// **(b) AFTER-ROOT 8-FELT BINDING FORGE — on the DEPLOYED member.** Forge the `.write` `new_root`
/// completion lanes 1..7 to garbage on every row while keeping lane 0 honest, recompute the after
/// block-commit chain + wide carriers so the ONLY thing that can bite is the map-op grow-gate on the
/// completion lanes, then run the pure LC verify. UNSAT ⟹ the deployed `.write` map-op binds all 8
/// after-root felts to the genuine sorted-Merkle splice (~124-bit), not lane-0.
///
/// The forgery is built at the RAW rotated coordinates and carried through the SAME compaction as
/// the honest row (see the module header): the S2 flag-day deleted the AFTER block's 1-felt chain
/// stratum, so a patched after block-commit and the re-derived wide carriers only exist
/// pre-compaction. `heapWriteVmDescriptor2R24` is one of `proof_verify.rs:1146`'s
/// `LIVE_ONLY_BARE_KEYS`, so this bare-wide member IS the light client's — the verdict is on the
/// deployed path.
#[test]
fn after_root_completion_lane_forge_is_unsat() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY)).unwrap();
    let new_root_cols = write_new_root_cols(&wide_desc);
    let raw_cols = raw_after_heap_root_cols();
    assert_eq!(
        new_root_cols,
        compacted_cols(KEY, raw_wide_width(), &raw_cols),
        "the forged RAW columns must be the ones compaction carries into the committed new_root"
    );

    // THE RAW (pre-compaction) honest row — the geometry the forgery has to be authored at.
    let (raw_trace, raw_dpis, map_heaps) = heap_write_fixture(true);
    assert_eq!(raw_trace[0].len(), raw_wide_width());
    assert_eq!(raw_dpis.len(), 20);
    let mb = MemBoundaryWitness::default();

    // POSITIVE (no downgrade): the honest turn, carried through the deployed compaction, proves +
    // verifies. Without this the negative below would be satisfied by a tooth that rejects
    // everything.
    let mut htrace = raw_trace.clone();
    compact_like_the_producer(&mut htrace);
    let hdpis = raw_dpis.clone();
    assert_committed_shape("honest heap-write", &wide_desc, &htrace, &hdpis);
    let honest_proof = prove_vm_descriptor2(&wide_desc, &htrace, &hdpis, &mb, &map_heaps)
        .expect("NO DOWNGRADE: honest wide heap-write proves");
    verify_vm_descriptor2(&wide_desc, &honest_proof, &hdpis)
        .expect("NO DOWNGRADE: honest wide heap-write verifies");

    // THE FORGE, AT RAW COORDINATES: garble lanes 1..7 on every row; keep lane 0 honest. These
    // completion lanes are the after rotated block's heap-root completion limbs, so they feed the
    // after STATE_COMMIT and the 8-felt after commit carriers — recompute the after block-commit and
    // re-derive the wide carriers/PIs so the trace is fully self-consistent and the map-op grow-gate
    // is the sole possible binder.
    let honest_raw_root: Vec<BabyBear> = raw_cols.iter().map(|&c| raw_trace[0][c]).collect();
    let mut ftrace = raw_trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[raw_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    assert_eq!(
        ftrace[0][raw_cols[0]], raw_trace[0][raw_cols[0]],
        "lane 0 (the scalar heap-root limb) stays honest — only the high seven lanes are forged"
    );
    assert!(
        (1..8).any(|l| ftrace[0][raw_cols[l]] != honest_raw_root[l]),
        "the forged high lanes differ from the genuine splice root (the grow-gate's UNSAT precondition)"
    );

    dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut ftrace);
    // Rebuild the base 4 PIs (pi1 = the recomputed after state-commit on the last row) + wide
    // carriers, ALL at the raw geometry the producer itself uses.
    let last = ftrace.len() - 1;
    let mut base4 = raw_dpis[..4].to_vec();
    base4[0] = ftrace[0][BEFORE_BASE + B_STATE_COMMIT];
    base4[1] = ftrace[last][AFTER_BASE + B_STATE_COMMIT];
    let fdpis = append_wide_carriers(&mut ftrace, base4, HEAP_WRITE_HOST_WIDTH);
    assert_eq!(fdpis.len(), 20);
    assert_eq!(ftrace[0].len(), raw_wide_width());

    // THE SAME COMPACTION THE HONEST ROW TOOK. The deleted bands would otherwise renumber the forged
    // columns out from under the tooth — and re-inflating a compacted row instead is precisely the
    // shape fault that made this tooth vacuous.
    compact_like_the_producer(&mut ftrace);
    assert_eq!(
        ftrace[0].len(),
        htrace[0].len(),
        "the forged row and the honest row are the SAME shape — the forgery is the only difference"
    );
    for lane in 1..8 {
        assert_ne!(
            ftrace[0][new_root_cols[lane]], htrace[0][new_root_cols[lane]],
            "after compaction, forged lane {lane} must still differ at committed column {}",
            new_root_cols[lane]
        );
    }

    let reason = refusal_reason(
        "after_root_completion_lane_forge_is_unsat",
        &wide_desc,
        &ftrace,
        &fdpis,
        &mb,
        &map_heaps,
    );
    match &reason {
        Some(why) => eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge is UNSAT — the deployed .write \
             map-op binds ALL EIGHT after-root felts to the genuine sorted-Merkle splice (~124-bit). \
             The 8-felt AFTER-root binding is faithfully enforced, not lane-0. Refusal mechanism: \
             {why}"
        ),
        None => eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge PROVES+VERIFIES — the deployed \
             descriptor binds only after-root lane 0 (~31-bit). A LIVE 8-felt gap."
        ),
    }
    assert!(
        reason.is_some(),
        "AFTER-ROOT FORGE: a heap-write forged to differ ONLY in the after-root's high seven \
         completion lanes proves+verifies through the deployed descriptor — the 8-felt AFTER-root is \
         NOT bound (lane-0 only). This is a live light-client soundness gap."
    );
}

/// **THE SHAPE-VACUITY GUARD, DEMONSTRATED AGAINST THE REAL PROVER** — the reason
/// `dregg_circuit::refusal` now reds on an arity `Err`, proved rather than documented.
///
/// This file's repaired vacuity (header §"Why (b) is built on the RAW row") was a *string* the real
/// prover emits. The lifted guard nets that string — but a marker list is only as good as its match
/// against what the prover ACTUALLY says, and that is a fact about `prove_vm_descriptor2`, not about
/// `refusal.rs`. So: take the HONEST fixture (which `after_root_completion_lane_forge_is_unsat`
/// proves + verifies), mis-shape it, and hand it to the SAME `classify` every tooth uses.
///
/// **The mis-shape is a WIDENING, and the direction is load-bearing.** Measured here: a row one
/// column SHORT of `trace_width` PROVES, because `trace_with_chip_lanes`
/// (`descriptor_ir2.rs:6075`) zero-`resize`s any short row up to the descriptor width *before* the
/// arity pre-flight sees it — by design, so a producer may build at the pre-lane width. Only a row
/// WIDER than the committed width reaches `descriptor_ir2.rs:5957` and returns the width `Err`. That
/// is exactly the historical fault (`append_wide_carriers` re-inflating 1963 → 3065), so widening is
/// what this gate reproduces. It is also why `assert_committed_shape` — which catches BOTH directions
/// structurally — is the primary guard and the marker list only the second net.
///
/// Both poles are asserted:
///
///  * the prover's own message must still trip `refusal::shape_fault` (if the string ever drifts, the
///    marker list is stale and this reds — the marker net cannot silently stop netting);
///  * `classify` must therefore PANIC rather than return `Outcome::Err`. Before the lift it returned
///    `Outcome::Err`, and any tooth reading that as "refused" recorded a refusal it never earned.
#[test]
fn a_misshaped_trace_reds_instead_of_counting_as_a_refusal() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY)).unwrap();
    let (raw_trace, raw_dpis, map_heaps) = heap_write_fixture(true);
    let mb = MemBoundaryWitness::default();

    let mut htrace = raw_trace;
    compact_like_the_producer(&mut htrace);
    assert_committed_shape("honest heap-write", &wide_desc, &htrace, &raw_dpis);

    // THE MIS-SHAPE: one column WIDER than the committed width, everything else honest.
    let mut wide = htrace.clone();
    for row in wide.iter_mut() {
        row.push(BabyBear::ZERO);
    }
    assert_eq!(wide[0].len(), wide_desc.trace_width + 1);

    // POLE 1 — the prover's ACTUAL words are still what the marker list nets.
    // (`Ir2BatchProof` is not `Debug`, so no `expect_err` — match it.)
    let raw_err = match prove_vm_descriptor2(&wide_desc, &wide, &raw_dpis, &mb, &map_heaps) {
        Err(e) => e,
        Ok(_) => panic!(
            "an over-wide trace PROVED — the arity pre-flight at descriptor_ir2.rs:5957 is GONE, and \
             the shape-vacuity class is wide open again"
        ),
    };
    let marker = shape_fault(&raw_err).unwrap_or_else(|| {
        panic!(
            "the prover's arity complaint is no longer matched by \
             refusal::SHAPE_FAULT_MARKERS — the marker net has gone STALE and every tooth is \
             exposed again. Prover said: {raw_err}"
        )
    });
    eprintln!("SHAPE-VACUITY GUARD: prover said {raw_err:?}; netted by marker {marker:?}");

    // POLE 2 — so `classify`, the primitive under every tooth, REFUSES TO RETURN a verdict.
    let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        classify("misshaped heap-write", || {
            let proof = prove_vm_descriptor2(&wide_desc, &wide, &raw_dpis, &mb, &map_heaps)?;
            verify_vm_descriptor2(&wide_desc, &proof, &raw_dpis)
        })
    }));
    let payload = verdict
        .err()
        .expect(
            "classify RETURNED a verdict for a mis-shaped trace — the shape guard is not armed, and \
             a tooth reading Outcome::Err as 'refused' is once again vacuous",
        )
        .downcast::<String>()
        .expect("the guard panics with a formatted message");
    assert!(
        payload.contains("SHAPE/ARITY fault"),
        "the panic must NAME the shape fault, not merely happen: {payload}"
    );
}
