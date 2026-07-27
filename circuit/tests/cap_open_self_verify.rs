//! # THE IN-CIRCUIT CAP-MEMBERSHIP OPEN — self-verifies END-TO-END through `prove_vm_descriptor2`.
//!
//! The Lean keystone `Dregg2.Circuit.Emit.CapOpenEmit.attenuateCapOpenEffV3` (descriptor
//! `dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff`, trace_width CAP_OPEN_WIDTH = rotated + cap-open
//! appendix) PROVES that a `DeployedCapOpen.Satisfied` cap-membership row opens the deployed
//! depth-16 cap-tree at a write-mask leaf whose target is the turn's `src`. This test realizes
//! that descriptor in Rust on a REAL witness: it builds a genuine rotated AttenuateCapability
//! base trace (`ROT_WIDTH`), widens it to `CAP_OPEN_WIDTH` with the cap-open appendix filled by
//! `widen_to_cap_open` (genuine `cap_chip_absorb` leaf + node digests — the SINGLE in-circuit chip
//! hash the cap-tree commits to), lays the cap-WRITE after-spine, and PROVES through
//! `prove_vm_descriptor2`. Every width here is DERIVED from `trace_rotated`'s constants; the
//! literals this header used to carry (`311-wide`, `369`) were three flag-days dead. The
//! proof self-verifies before returning, so a green test == the cap-open chip-lookups + base gates
//! are exercised end-to-end against the IR-v2 interpreter's auto-gathered chip table.
//!
//! LAW #1: this test fills COLUMNS only; every constraint is the Lean-declared chip lookup /
//! base gate the IR-v2 interpreter realizes generically. No hand-authored Rust constraint
//! semantics.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover cap_open_attenuate_self_verifies -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::sel;
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_AFTER_SPINE_SPAN, CAP_OPEN_BASE, CAP_OPEN_WIDTH, CapOpenWitness, DFA_RC_LEN,
    FACET_MASK_HI, RotatedBlockWitness, SIGNATURE_AUTH_TAG, WRITE_MASK_LO, empty_caveat_manifest,
    generate_rotated_cap_attenuate_after_spine, generate_rotated_effect_vm_trace,
    widen_to_cap_open,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

// The LIVE attenuate cap-open descriptor (genuine submask facet + decoded tier). The Signature-pinned
// `attenuateCapOpenVmDescriptor2R24` was deleted (Stage D — the apex authority leg now refines this
// `-eff` membership descriptor, the one the deployed prover routes).
const CAP_OPEN_KEY: &str = "attenuateCapOpenEffVmDescriptor2R24";

/// Resolve a registry descriptor JSON by key from the committed staged TSV.
fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Build the rotated AttenuateCapability base trace (`ROT_WIDTH`) + the 46-PI cap-open vector from
/// real before/after producer witnesses.
///
/// ⚠ **NO nonce-FREEZE patch, and that is the point.** `attenuateCapOpenEffVmDescriptor2R24` is a
/// cap-WRITE member (`effCapOpenWriteV3` — the read appendix PLUS the after-spine), and every
/// WRITE-bearing wrapper rides the nonce-TICK face: the descriptor's gate
/// `(col78 − col56) − (1 − sel[NOOP]) == 0` demands `after.nonce == before.nonce + 1` on the active
/// row. `patch_attenuate_base_for_cap_open` FREEZES the nonce (`after := before`) — correct for the
/// authority-only attenuate base, WRONG here, and the deployed SDK leg skips it for exactly this
/// reason (`sdk/src/full_turn_proof.rs`: *"when the write wrapper is active, SKIP the nonce-freeze
/// patch (it would freeze the nonce against the wrapper's tick gate…)"*). This test called it
/// unconditionally, and that was one half of the measured `[#4, #10]` row-0 UNSAT; the bare
/// generator already emits the tick (`before = 0`, `after = 1`).
fn build_attenuate_base() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::AttenuateCapability {
        cap_slot_hash: [BabyBear::new(0x51); 8],
        narrower_commitment: [BabyBear::new(0x52); 8],
        phase_b: None,
    }];

    let mut ledger = Ledger::new();
    // Attenuate is a state-passthrough on balance/fields/nonce-tick; the after-cell ticks nonce.
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

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

    let caveat = empty_caveat_manifest();
    let (trace, pis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated AttenuateCapability base trace must generate");
    // The cap-open faces were never rc-wrapped in the Lean emit (the committed
    // `attenuateCapOpenEffVmDescriptor2R24` carries the UNWRAPPED 46-PI base), so lift the dsl rc
    // tail off — exactly as the SDK cap-open leg builder does.
    let mut dpis = pis;
    dpis.truncate(dpis.len() - DFA_RC_LEN);
    (trace, dpis)
}

/// Re-read the FOUR rotated commit PIs (`V1_PI_COUNT..+4`) off the trace.
///
/// MUST be called after anything that rewrites a rotated block commit. The after-spine
/// (`generate_rotated_cap_attenuate_after_spine`) overrides the BEFORE/AFTER cap-root 8-felt GROUPS
/// and then calls `recompute_block_commit` on BOTH blocks — which moves
/// `BEFORE_BASE + B_STATE_COMMIT` (col 367), the exact column the descriptor's FIRST-row `piBinding`
/// pins to PI 42. A dpis vector captured before the after-spine is stale there.
///
/// ⚠ The WIDE leg does not need this (`append_wide_carriers` ZEROES the two retired 1-felt commit
/// pins under STAGE-1 PIN RETIREMENT), which is why the gap only ever bit the NARROW member.
fn refresh_rotated_commit_pis(trace: &[Vec<BabyBear>], dpis: &mut [BabyBear]) {
    use dregg_circuit::effect_vm::trace_rotated::{
        AFTER_BASE, B_COMMITTED_HEIGHT, B_STATE_COMMIT, BEFORE_BASE, C_CAVEAT_COMMIT, CAVEAT_BASE,
        V1_PI_COUNT,
    };
    let last = trace.len() - 1;
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT + 1] = trace[last][AFTER_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT + 2] = trace[last][AFTER_BASE + B_COMMITTED_HEIGHT];
    dpis[V1_PI_COUNT + 3] = trace[last][CAVEAT_BASE + C_CAVEAT_COMMIT];
}

/// A real cap-membership witness: a chosen transfer-conferring leaf (the FAITHFUL two-axis
/// facet × tier — mask_lo == EFFECT_TRANSFER, mask_hi == 0, auth_tag == Signature) at a position
/// in a small c-list, the depth-16 ABSORB-node path + recomposed root, src pinned to leaf.target.
fn cap_open_witness() -> CapOpenWitness {
    // Leaf fields in CapOpenCols order: [slot_hash, target, auth_tag, mask_lo, mask_hi, expiry,
    // breadstuff]. The FAITHFUL two-axis gate pins: auth_tag == 1 (Signature tier), mask_lo ==
    // EFFECT_TRANSFER (the transferFacetGate), mask_hi == 0 (the facetHiGate); target == src
    // (the targetBind).
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),            // slot_hash
        BabyBear::new(7_777),              // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (== 1, Signature tier)
        BabyBear::new(WRITE_MASK_LO),      // mask_lo (== EFFECT_TRANSFER = 2)
        BabyBear::new(FACET_MASK_HI),      // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(42),                 // breadstuff
    ];
    // A second (distinct, non-write) leaf to make the c-list non-trivial.
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds")
}

/// The narrowed KEEP_MASK the attenuate effect carries (`narrower_commitment[1]` — the mask the
/// held cap is narrowed TO). `build_attenuate_base` emits `narrower_commitment = [0x52; 8]`.
const KEEP_MASK: u32 = 0x52;
/// The held cap's mask at the cap KEY (the submask non-amplification tooth compares the narrowed
/// KEEP_MASK against this: `0x52 ⊑ 0xFF`). Mirrors the SDK leg's c-list `held_mask`.
const HELD_MASK: u32 = 0xFF;

/// Lay the cap-WRITE AFTER-spine on a `CAP_OPEN_WIDTH`-wide cap-open trace, taking it to the
/// descriptor's `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`. The after-spine narrows the OPENED
/// leaf in place (`mask_lo := KEEP_MASK`) and folds it over the SHARED sibling path to the AFTER
/// `cap_root8`, which is what forces the faithful 8-felt cap-write (`effCapOpenWriteV3_forces_write8`)
/// — no arity-2 map-op, hence no map heap.
fn lay_attenuate_after_spine(
    trace: &mut [Vec<BabyBear>],
    w: &CapOpenWitness,
    dpis: &mut [BabyBear],
) {
    generate_rotated_cap_attenuate_after_spine(
        trace,
        w,
        w.leaf[0], // the cap KEY = the opened leaf's slot_hash
        BabyBear::new(HELD_MASK),
        BabyBear::new(KEEP_MASK),
    )
    .expect("attenuate cap-write after-spine lays");
    // The after-spine rewrote both rotated block commits — the four commit PIs are now stale.
    refresh_rotated_commit_pis(trace, dpis);
}

/// The cap-open descriptor parses; the witness builds + recomposes its cap_root over the genuine
/// `cap_chip_absorb` (the single in-circuit chip hash) depth-16 fold; the rotated attenuate
/// base trace builds; and the cap-open appendix columns fill to the
/// witness values. Both the leaf lookup (arity 7) and the 16 node lookups (arity 3) are
/// chip-realizable single absorbs; the full prove is `cap_open_attenuate_self_verifies`.
#[test]
fn cap_open_witness_and_appendix_are_genuine() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_KEY)).expect("cap-open descriptor parses");
    // attenuate is a cap-WRITE descriptor (`effCapOpenWriteV3`): the 329 read appendix PLUS the 143
    // after-spine recompute that forces the faithful 8-felt cap-write (`*_forces_write8`). This
    // structural test exercises the READ appendix at `[CAP_OPEN_BASE, +329)`; the after-spine sits past
    // it (the full cap-write trace fill is the SDK-covered handoff `cap_open_attenuate_self_verifies`).
    assert_eq!(
        desc.trace_width,
        CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN,
        "cap-open WRITE width = read appendix (CAP_OPEN_WIDTH) + after-spine"
    );
    assert_eq!(
        desc.public_input_count, 46,
        "cap-open carries the rotated 46 PIs"
    );

    let (mut trace, pis) = build_attenuate_base();
    assert_eq!(pis.len(), 46);

    let w = cap_open_witness();
    assert_eq!(
        w.recomposes(),
        w.cap_root,
        "the witness path must recompose the committed cap_root (absorb-node fold)"
    );
    assert_eq!(
        w.src, w.leaf[1],
        "src must equal the leaf target (targetBind)"
    );
    assert_eq!(
        w.leaf[3],
        BabyBear::new(WRITE_MASK_LO),
        "the chosen leaf mask_lo must be EFFECT_TRANSFER (transferFacetGate)"
    );
    assert_eq!(
        w.leaf[4],
        BabyBear::new(FACET_MASK_HI),
        "the chosen leaf mask_hi must be 0 (facetHiGate)"
    );
    assert_eq!(
        w.leaf[2],
        BabyBear::new(SIGNATURE_AUTH_TAG),
        "the chosen leaf auth_tag must be the Signature tier (authTagGate)"
    );

    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");
    assert_eq!(trace[0].len(), CAP_OPEN_WIDTH, "cap-open trace width");
    assert_eq!(trace[0][CAP_OPEN_BASE + 3], BabyBear::new(WRITE_MASK_LO));
    // Phase H-CAP-8 native 8-felt layout: cap_root group at +287..294, src at +295.
    for j in 0..8 {
        assert_eq!(trace[0][CAP_OPEN_BASE + 287 + j], w.cap_root[j]);
    }
    assert_eq!(trace[0][CAP_OPEN_BASE + 295], w.src);
    // The top node8 group (level 15, at +15+17*15+9 = +279..286) equals the recomposed root group.
    for j in 0..8 {
        assert_eq!(
            trace[0][CAP_OPEN_BASE + 15 + 17 * 15 + 9 + j],
            w.cap_root[j],
            "node8[15] (top fold) lane {j} == cap_root"
        );
    }
}

/// END-TO-END self-verify through `prove_vm_descriptor2`.
///
/// The cap-tree is committed to the SINGLE in-circuit hash `cap_root.rs::cap_chip_absorb` (the IR-v2
/// chip's BUS_P2 absorb). The cap-LEAF lookup is the arity-7 (`big = 1`, rate-8) chip absorb of the
/// 7 leaf fields; each of the 16 NODE lookups is the arity-3 absorb of `[FACT_MARK, left, right]`.
/// The chip realizes BOTH shapes as one row apiece (the `big = [arity == 7]` seeding lane), so the
/// auto-gathered chip table carries a matching row for every cap-open lookup, and the proof
/// self-verifies end-to-end against the IR-v2 interpreter. This is decision #1 made good: the Lean
/// `DeployedCapOpen.SchemeRealizedByChip` bridge is DISCHARGED (the chip genuinely realizes the cap
/// hash), so the membership leg is sound outright, not relative to a carried hypothesis.
// ⚑ THE `[#4, #10]` ROW-0 UNSAT IS CLOSED (2026-07-27) — and it was NEITHER prime suspect.
//
// The measured reason this replaced named HELD_MASK/KEEP_MASK (cols 72/73) and "the row-0 boundary
// the pad rows do not carry". Both were wrong. Resolving the two indices against the descriptor
// (p3 numbers `assert_zero` calls in `Ir2Air::eval` order — every `when_first_row` pin, then every
// `when_last_row` pin, then the `when_transition` gates) puts them at:
//
//   * #4  = FIRST-row `piBinding { col: 367, pi_index: 42 }` — col 367 is
//           `BEFORE_BASE + B_STATE_COMMIT`, the BEFORE block's rotated commit. The after-spine
//           overrides the cap-root GROUPS and re-runs `recompute_block_commit` on both blocks, so a
//           PI vector captured before it is stale. Fixed by `refresh_rotated_commit_pis`.
//   * #10 = the gate `(col78 − col56) − (1 − sel[NOOP]) == 0` — the NONCE TICK. This descriptor is
//           a cap-WRITE member and rides the tick face; the test was applying
//           `patch_attenuate_base_for_cap_open`, whose whole job is to FREEZE the nonce. The bare
//           generator already ticks it (before 0 → after 1), and the deployed SDK leg skips that
//           patch for write-bearing wrappers for precisely this reason. Fixed in
//           `build_attenuate_base`.
//
// Neither fix touches a constraint: the AIR is the Lean-emitted descriptor, unchanged, and both
// repairs are trace/PI FILL on the producer side. LAW #1 holds.
#[test]
fn cap_open_attenuate_self_verifies() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_KEY)).expect("cap-open descriptor parses");
    let (mut trace, mut pis) = build_attenuate_base();
    let w = cap_open_witness();
    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");
    lay_attenuate_after_spine(&mut trace, &w, &mut pis);

    // The arity-2 cap-write map-op is DROPPED from this descriptor: the faithful 8-felt write is
    // forced by the AFTER-spine (`effCapOpenWriteV3_forces_write8`) laid just above. So the map_log
    // is empty and an empty `map_heaps` is correct.
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    prove_vm_descriptor2(&desc, &trace, &pis, &mem_boundary, &map_heaps)
        .expect("cap-open attenuate trace must prove (and self-verify) end-to-end");
    eprintln!(
        "CAP-OPEN ATTENUATE (R=24 + 58-col cap-membership appendix) — PROVED + SELF-VERIFIED \
         end-to-end; the depth-16 absorb-node membership fold opens the committed cap_root at a \
         write-mask leaf whose target is the turn's src."
    );

    // (5) NEGATIVE TOOTH A: a FORGED sibling breaks the membership path → the node chain no
    //     longer recomposes capRoot (rootPin fails) → UNSAT.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            // tamper sibling lane 0 at level 0 (8-felt sib group at base + 15..22) but keep the chip
            // node columns as-is: the chip lookup for level 0 now evaluates a tuple whose hash != the
            // node column, so the auto-gathered chip table no longer matches → the LogUp lookup fails.
            row[CAP_OPEN_BASE + 15] += BabyBear::ONE;
        }
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, &t, &pis, &mem_boundary, &map_heaps)
        }));
        let rejected = matches!(refused, Err(_)) || matches!(refused, Ok(Err(_)));
        assert!(
            rejected,
            "a forged sibling (broken membership path) MUST be UNSAT"
        );
    }

    // (6) NEGATIVE TOOTH B: a leaf whose mask_lo != EFFECT_TRANSFER makes the transferFacetGate
    //     non-zero → UNSAT (the facet does not permit the transfer effect-kind).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_OPEN_BASE + 3] = BabyBear::new(WRITE_MASK_LO + 1); // mask_lo off the facet pin
        }
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, &t, &pis, &mem_boundary, &map_heaps)
        }));
        let rejected = matches!(refused, Err(_)) || matches!(refused, Ok(Err(_)));
        assert!(
            rejected,
            "a leaf whose mask_lo != EFFECT_TRANSFER (facet does not permit transfer) MUST be UNSAT"
        );
    }

    // (7) NEGATIVE TOOTH C: a leaf whose auth_tag != Signature makes the authTagGate non-zero →
    //     UNSAT (the committed tier is not the satisfiable Signature tier).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_OPEN_BASE + 2] = BabyBear::new(SIGNATURE_AUTH_TAG + 1); // auth_tag off the tier pin
        }
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, &t, &pis, &mem_boundary, &map_heaps)
        }));
        let rejected = matches!(refused, Err(_)) || matches!(refused, Ok(Err(_)));
        assert!(
            rejected,
            "a leaf whose auth_tag != Signature (wrong tier) MUST be UNSAT"
        );
    }

    eprintln!(
        "CAP-OPEN NEGATIVE TEETH GREEN: forged sibling rejected; wrong facet rejected; wrong tier \
         rejected."
    );
}

/// THE SELECTOR-GATE FORGERY TOOTH (cap-open family). The cap-open descriptors now carry the
/// `selectorGate <baseRuntimeSelector>` tooth (Lean `EffectVmEmitRotationV3.withSelectorGate`,
/// `Dregg2.Circuit.Emit.CapOpenEmit` — the attenuate cap-open gates on `sel::ATTENUATE_CAPABILITY =
/// 48`). The per-row body `(1 - sel[NOOP])·(1 - sel[48])` is forced ZERO on every row, so a non-pad
/// row must carry the descriptor's OWN runtime selector. A row carrying a FOREIGN selector
/// (`sel[NOOP] = 0`, `sel[48] = 0`, `sel[TRANSFER] = 1`) makes the body `1·1 = 1 ≠ 0` → UNSAT, at
/// `prove_vm_descriptor2` ALONE (no ledger). This closes the gate-asymmetry residual that the
/// value-cohort fix (`b9b8b6973`) left open on the cap-open family — defense-in-depth made symmetric.
#[test]
fn cap_open_attenuate_foreign_selector_row_is_unsat() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_KEY)).expect("cap-open descriptor parses");
    let (mut trace, mut pis) = build_attenuate_base();
    let w = cap_open_witness();
    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");
    lay_attenuate_after_spine(&mut trace, &w, &mut pis);

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];

    // Honest baseline proves+self-verifies (the active row carries sel[48], the pads carry sel[NOOP]).
    prove_vm_descriptor2(&desc, &trace, &pis, &mem_boundary, &map_heaps)
        .expect("honest attenuate cap-open trace proves before the forgery");

    // Locate a NOOP pad row (the honest tail) and flip it to a FOREIGN selector (TRANSFER), the
    // smoking gun the appended gate forbids: a row whose transition this descriptor never binds.
    let pad = trace
        .iter()
        .position(|row| row[sel::NOOP] == BabyBear::ONE)
        .expect("the cap-open trace carries at least one NOOP pad row");
    assert_eq!(
        trace[pad][sel::ATTENUATE_CAPABILITY],
        BabyBear::ZERO,
        "the pad row does not carry the attenuate selector"
    );
    trace[pad][sel::NOOP] = BabyBear::ZERO;
    trace[pad][sel::TRANSFER] = BabyBear::ONE;

    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(&desc, &trace, &pis, &mem_boundary, &map_heaps)
    }));
    let rejected = matches!(refused, Err(_)) || matches!(refused, Ok(Err(_)));
    assert!(
        rejected,
        "SOUNDNESS (light-client unfoolable): a foreign-selector (TRANSFER) row under the \
         attenuate cap-open descriptor MUST be UNSAT — the appended `selectorGate \
         ATTENUATE_CAPABILITY` rejects it"
    );

    eprintln!(
        "CAP-OPEN SELECTOR-GATE FORGERY TOOTH GREEN: a foreign-TRANSFER row under \
         attenuateCapOpenEffVmDescriptor2R24 is UNSAT (the selector-binding gate bites)."
    );
}

/// **THE CAP-OPEN TAIL WIDE ROUNDTRIP.** The committed wide cap-WRITE member
/// `attenuateCapOpenEffVmDescriptor2R24` in `rotation-wide-registry-staged.tsv`: the genuine cap-open
/// attenuate trace, widened to `CAP_OPEN_WIDTH`, given its after-spine, lifted to the wide geometry by
/// `generate_rotated_cap_attenuate_after_spine_wide` (carriers at the WRITE host
/// `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`, NOT at `GRAD_ROT_WIDTH`), then run through the
/// deployed `compact_s2_columns ∘ compact_e1_columns` — PROVES + VERIFIES. The executor-anchoring
/// differential holds: `wire_commit_8_chip(trusted before-limbs) == the circuit's published BEFORE
/// 8-felt commit`.
///
/// ⚠ EVERY GEOMETRY PIN HERE IS DERIVED. The previous body hard-coded `host 818 / wide 1026 / carrier
/// base 914 / carrier 12 / 37 limbs` — a geometry three flag-days dead, which is why this test failed
/// on its FIRST assertion (`left: 2021, right: 2184`) rather than on anything about the cap-open. The
/// compaction step is what makes the deployed width 2021 rather than the raw appended
/// `2119 + WIDE_CARRIER_APPENDIX`; a wide descriptor width is never "host + appendix".
///
/// ADDITIVE: the live 1-felt cap-open path / TSV / VK are UNTOUCHED — the wide member is the parallel
/// 8-felt lane from `CapOpenEmit.v3RegistryCapOpenWide` (`WIDE_REGISTRY_STAGED_TSV`).
#[test]
fn cap_open_wide_proves_verifies_and_executor_anchors() {
    use dregg_circuit::descriptor_ir2::verify_vm_descriptor2;
    use dregg_circuit::effect_vm::trace_rotated::{
        B_IROOT, BEFORE_BASE, NUM_PRE_LIMBS, WIDE_CARRIER_APPENDIX, WIDE_COMMIT_CARRIER,
        compact_e1_columns, compact_s2_columns, generate_rotated_cap_attenuate_after_spine_wide,
    };
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;

    let wide_json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(CAP_OPEN_KEY) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("cap-open wide member in WIDE_REGISTRY_STAGED_TSV");
    let desc = parse_vm_descriptor2(wide_json).expect("cap-open wide descriptor parses");
    // The WRITE host: the read appendix PLUS the after-spine. The wide carriers ride PAST it.
    let host_width = CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN;
    let raw_wide_width = host_width + WIDE_CARRIER_APPENDIX;
    assert_eq!(
        desc.public_input_count,
        46 + 16,
        "cap-open wide PIs = the 46 rotated base + the 16 wide commit pins"
    );

    let (mut trace, pis) = build_attenuate_base();
    let w = cap_open_witness();
    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");
    assert_eq!(trace[0].len(), CAP_OPEN_WIDTH, "cap-open READ width");

    // The after-spine + the wide carriers in ONE deployed producer (the narrow lift plus
    // `append_wide_carriers` — they cannot drift). The 16 wide commit PIs append past the base 46.
    let dpis = generate_rotated_cap_attenuate_after_spine_wide(
        &mut trace,
        pis,
        &w,
        w.leaf[0],
        BabyBear::new(HELD_MASK),
        BabyBear::new(KEEP_MASK),
    )
    .expect("cap-open wide after-spine lift");
    assert_eq!(trace[0].len(), raw_wide_width, "raw appended wide width");
    assert_eq!(dpis.len(), desc.public_input_count, "wide PI count");

    // EXECUTOR ANCHORING, taken on the RAW (pre-compaction) row, where the carrier columns still
    // sit at their appended coordinates: the trusted before-limbs through the chip-faithful chain
    // == the circuit's published BEFORE 8-felt commit carrier.
    let before_commit_base = host_width + 8 * WIDE_COMMIT_CARRIER;
    let before_limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS)
        .map(|j| trace[0][BEFORE_BASE + j])
        .collect();
    let before_iroot = trace[0][BEFORE_BASE + B_IROOT];
    let anchored = dregg_circuit::poseidon2::wire_commit_8_chip(&before_limbs, before_iroot);
    let circuit_commit: [BabyBear; 8] = core::array::from_fn(|j| trace[0][before_commit_base + j]);
    assert_eq!(
        anchored, circuit_commit,
        "cap-open wide: wire_commit_8_chip(trusted before-limbs) == the circuit BEFORE commit carrier"
    );
    assert!(
        circuit_commit[1..].iter().any(|f| *f != BabyBear::ZERO),
        "cap-open wide: the commit is genuinely 8-felt-wide (lanes 1..8 not all zero)"
    );
    // And the published PIs ARE that carrier (the 16 wide pins ride past the base 46).
    for j in 0..8 {
        assert_eq!(
            dpis[46 + j],
            circuit_commit[j],
            "cap-open wide PI {} = BEFORE 8-felt commit felt {j}",
            46 + j
        );
    }

    // THE S2 + E1 DELETIONS: the raw appended row is old-geometry; the deployed producer drops the
    // retired 1-felt chain bands and the dead v1-face bands so the rows match the committed member.
    compact_s2_columns(&mut trace, CAP_OPEN_KEY).expect("S2 compaction on the raw wide trace");
    compact_e1_columns(&mut trace, CAP_OPEN_KEY).expect("E1 compaction on the S2-compacted trace");
    assert_eq!(
        trace[0].len(),
        desc.trace_width,
        "the COMPACTED wide row matches the committed descriptor width — not host + appendix"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("CAP-OPEN WIDE must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("CAP-OPEN WIDE proof must verify independently");
    eprintln!(
        "CAP-OPEN WIDE (attenuate cap-WRITE, R=24, width {}, {} PIs, FAITHFUL 8-felt commit): \
         PROVED + VERIFIED.",
        desc.trace_width, desc.public_input_count
    );
}
