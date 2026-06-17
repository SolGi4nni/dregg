//! # THE IN-CIRCUIT CAP-MEMBERSHIP OPEN — self-verifies END-TO-END through `prove_vm_descriptor2`.
//!
//! The Lean keystone `Dregg2.Circuit.Emit.CapOpenEmit.capOpenAttenuateV3` (descriptor
//! `dregg-effectvm-attenuateA-v1-rot24-v3-capopen`, trace_width 369 = 311 rotated + 58 cap-open
//! appendix) PROVES that a `DeployedCapOpen.Satisfied` cap-membership row opens the deployed
//! depth-16 cap-tree at a write-mask leaf whose target is the turn's `src`. This test realizes
//! that descriptor in Rust on a REAL witness: it builds a genuine rotated AttenuateCapability
//! base trace (the proven 311-wide attenuate path), widens it to 369 with the cap-open appendix
//! filled by `widen_to_cap_open` (genuine `cap_chip_absorb` leaf + node digests — the SINGLE
//! in-circuit chip hash the cap-tree commits to), and PROVES through `prove_vm_descriptor2`. The
//! proof self-verifies before returning, so a green test == the cap-open chip-lookups + base gates
//! are exercised end-to-end against the IR-v2 interpreter's auto-gathered chip table.
//!
//! LAW #1: this test fills COLUMNS only; every constraint is the Lean-declared chip lookup /
//! base gate the IR-v2 interpreter realizes generically. No hand-authored Rust constraint
//! semantics.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover cap_open_attenuate_self_verifies -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_BASE, CAP_OPEN_WIDTH, CapOpenWitness, FACET_MASK_HI, RotatedBlockWitness,
    SIGNATURE_AUTH_TAG, WRITE_MASK_LO, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    patch_attenuate_base_for_cap_open, widen_to_cap_open,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

const CAP_OPEN_KEY: &str = "attenuateCapOpenVmDescriptor2R24";

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

/// Build the proven 311-wide rotated AttenuateCapability base trace + 38 PIs from real
/// before/after producer witnesses (the path the rotation flip test proves green).
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
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let (mut trace, pis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated AttenuateCapability base trace must generate");
    // Wire the attenuate phase-B bindings the bare generator does not carry (nonce passthrough +
    // cap-root advance binding); returns the corrected 38-PI vector.
    let dpis = patch_attenuate_base_for_cap_open(&mut trace, &pis)
        .expect("attenuate base phase-B wiring");
    (trace, dpis)
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
        BabyBear::new(0xA11CE),                // slot_hash
        BabyBear::new(7_777),                  // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG),     // auth_tag (== 1, Signature tier)
        BabyBear::new(WRITE_MASK_LO),          // mask_lo (== EFFECT_TRANSFER = 2)
        BabyBear::new(FACET_MASK_HI),          // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),            // expiry
        BabyBear::new(42),                     // breadstuff
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

/// The cap-open descriptor parses; the witness builds + recomposes its cap_root over the genuine
/// `cap_chip_absorb` (the single in-circuit chip hash) depth-16 fold; the proven 311-wide attenuate
/// base trace builds + carries the phase-B wirings; and the cap-open appendix columns fill to the
/// witness values. Both the leaf lookup (arity 7) and the 16 node lookups (arity 3) are
/// chip-realizable single absorbs; the full prove is `cap_open_attenuate_self_verifies`.
#[test]
fn cap_open_witness_and_appendix_are_genuine() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_KEY)).expect("cap-open descriptor parses");
    assert_eq!(desc.trace_width, CAP_OPEN_WIDTH, "cap-open width");
    assert_eq!(desc.public_input_count, 38, "cap-open carries the rotated 38 PIs");

    let (mut trace, pis) = build_attenuate_base();
    assert_eq!(pis.len(), 38);

    let w = cap_open_witness();
    assert_eq!(
        w.recomposes(),
        w.cap_root,
        "the witness path must recompose the committed cap_root (absorb-node fold)"
    );
    assert_eq!(w.src, w.leaf[1], "src must equal the leaf target (targetBind)");
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
    assert_eq!(trace[0].len(), CAP_OPEN_WIDTH, "370-col cap-open trace");
    assert_eq!(trace[0][CAP_OPEN_BASE + 3], BabyBear::new(WRITE_MASK_LO));
    assert_eq!(trace[0][CAP_OPEN_BASE + 56], w.cap_root);
    assert_eq!(trace[0][CAP_OPEN_BASE + 57], w.src);
    // The top node column equals the recomposed root (the rootPin gate's witness).
    assert_eq!(
        trace[0][CAP_OPEN_BASE + 10 + 3 * 15],
        w.cap_root,
        "node[15] (top fold) == cap_root"
    );
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
#[test]
fn cap_open_attenuate_self_verifies() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_KEY)).expect("cap-open descriptor parses");
    let (mut trace, pis) = build_attenuate_base();
    let w = cap_open_witness();
    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");

    // Attenuate's map ops are guard-gated OFF on this generator's output (the map-op guard column
    // is 0 on every row), so the map_log is empty and an empty `map_heaps` is correct.
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
            // tamper sibling at level 0 (col base + 8) but keep the chip node columns as-is:
            // the chip lookup for level 0 now evaluates a tuple whose hash != the node column,
            // so the auto-gathered chip table no longer matches → the LogUp lookup fails.
            row[CAP_OPEN_BASE + 8] += BabyBear::ONE;
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
