//! # THE VK-EPOCH LIGHT-CLIENT BINDING BITE — noteSpend / noteCreate FORCED ON-WIRE.
//!
//! ## What this closes (`docs/VK-EPOCH-PLAN.md`, the notes family — #13 noteCreate, #14 noteSpend)
//!
//! noteSpend is the GOLD-STANDARD in-circuit gate of the whole effect vocabulary: its nullifier
//! accumulator lives on a ROTATED limb (`B_NULLIFIER_ROOT = 26`), witness-carried, and the live
//! `noteSpendVmDescriptor2R24` descriptor carries TWO selector-gated map-ops —
//! `nullifierFreshOp` (`.absent`: the spent nullifier is a NON-MEMBER of the BEFORE nullifier tree
//! — the in-circuit double-spend tooth) and `nullifierInsertOp` (`.write`: the AFTER root IS the
//! genuine sorted-Poseidon2 insert of the spent nullifier). noteCreate is the append-only twin on
//! the `commitments_root` limb (`B_COMMITMENTS_ROOT = 27`), carrying `commitmentsInsertOp`
//! (`.insert`: the AFTER commitments root IS the genuine sorted insert of the published note
//! commitment).
//!
//! Unlike the perms/VK weld (which forces an AFTER digest limb EQUAL to a *declared param*), the
//! notes-family forcing is a MAP-OP GROW-GATE: the map-op pins
//!
//!     AFTER root  ==  op(BEFORE root, key)        (op ∈ {`.write`, `.insert`})
//!
//! against a real sorted-Poseidon2 tree threaded as the prover's `map_heaps` witness. The overridden
//! AFTER root is in turn absorbed by `recompute_block_commit` into each block's `B_STATE_COMMIT`
//! carrier → the published rotated OLD/NEW commit PIs (`V1_PI_COUNT`, `V1_PI_COUNT + 1`). So the
//! binding chain a LIGHT CLIENT verifies, with NO trusted post-cell, is:
//!
//!     NEW_COMMIT (claimed, PI-anchored)  ⟹  B_STATE_COMMIT carrier
//!       ⟹  AFTER nullifier/commitments-root limb (absorbed)
//!       ⟹  (map-op `.write`/`.insert`)  AFTER == op(BEFORE, key)  ⟹  the genuine grown set
//!
//! A post-state forged to differ ONLY in the nullifier-root / commitments-root — a root the kernel
//! never genuinely grew — is NOT the sorted insert of the published key, so the `.write`/`.insert`
//! op has NO membership/update witness and `prove_vm_descriptor2` REFUSES it (or the absorbed-commit
//! mismatch reds `verify_vm_descriptor2`). The forge is rejected by the IN-CIRCUIT grow-gate, NOT a
//! host re-derivation.
//!
//! ## The light-client discriminator (the plan's bar, §6 / the guardrail)
//!
//! Both teeth run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE — the exact circuit
//! verify a light client runs. That path NEVER calls `apply_effect_to_cell` and NEVER anchors an
//! off-cell record-pin PI, so these tests are INHERENTLY the *anchor-disabled* discriminator: a
//! reject here is the in-circuit grow-gate biting, not a full-node host re-derivation.
//!
//!   * POSITIVE (no downgrade): an HONEST noteSpend / noteCreate turn proves + verifies green.
//!   * NEGATIVE (the bite): a post-state forged to differ ONLY in the nullifier-root /
//!     commitments-root — a root the kernel never grew — is UNSAT.
//!
//! Gated on `prover` (compiles `descriptor_ir2`). Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_notes_light_client_binding -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};
use dregg_circuit::effect_vm::trace_rotated::{
    ACCUM_INSERT_HOST_WIDTH, AFTER_BASE, B_COMMITMENTS_ROOT, B_NULLIFIER_ROOT, B_STATE_COMMIT,
    BEFORE_BASE, CAP_OPEN_SPAN, ROT_WIDTH, RotatedBlockWitness, WIDE_WIDTH, append_wide_carriers,
    empty_caveat_manifest, generate_rotated_note_create_trace_with_commitments_tree,
    generate_rotated_note_create_wide, generate_rotated_note_spend_trace_with_nullifier_tree,
    recompute_after_blocks_for_test, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_turn::rotation_witness as rw;

/// The rotated OLD/NEW commit PI slots (the rotated leg's published commitment) — the four-pin
/// block appended after the 42 v1 PIs. The grow-gate generators re-derive these from the overridden
/// limb so the published commitment binds the grown set.
const PI_OLD_COMMIT: usize = 42; // V1_PI_COUNT
const PI_NEW_COMMIT: usize = 43; // V1_PI_COUNT + 1

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
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

/// The producer's cell (open perms; the EffectVM credits balance by the note value).
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics) on the given trace + PIs.
fn refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

/// **noteSpend FORCED ON-WIRE (light-client-verifiable).** An honest noteSpend turn proves +
/// verifies; a post-state forged to differ ONLY in the nullifier-root (limb 26 of the AFTER block —
/// and the published commit absorbing it — carry a root the kernel NEVER grew, while the spent
/// nullifier param stays honest) is UNSAT through `prove`/`verify` ALONE — the in-circuit
/// `.write`/`.absent` grow-gate (`nullifierInsertOp`/`nullifierFreshOp`) bites with NO off-cell
/// `apply_effect_to_cell` re-derivation. This is the GOLD-STANDARD in-circuit gate.
#[test]
fn notespend_forced_on_wire_rejects_forged_nullifier_root_anchor_disabled() {
    let before_balance: i64 = 90_000;
    let value: u64 = 500;

    // The HONEST noteSpend: the EffectVM credits balance by `value` (the shielding convention).
    let effect = Effect::NoteSpend {
        nullifier: BabyBear::new(0xBEEF),
        value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("NoteSpend is a cohort member");
    assert_eq!(name, "noteSpendVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated noteSpend descriptor parses");
    assert_eq!(
        desc.public_input_count, 51,
        "noteSpend PIs = ROT_NULLIFIER_PI_COUNT (47 = 46 rotated + 1 nullifier-forcing pin) + \
         DFA_RC_LEN (4 dsl rc pins) = 51 (committed noteSpendVmDescriptor2R24)"
    );

    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[7u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    // A non-empty BEFORE nullifier set (distinct from the spent nullifier `0xBEEF`) — the openable
    // sorted-Poseidon2 accumulator the grow-gate forces against.
    let before_nullifiers = vec![
        HeapLeaf {
            addr: BabyBear::new(0x1111),
            value: BabyBear::new(1),
        },
        HeapLeaf {
            addr: BabyBear::new(0x2222),
            value: BabyBear::new(1),
        },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_nullifiers,
    )
    .expect("nullifier-tree wiring must produce a deployment-real noteSpend trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    // ANTI-VACUITY: the nullifier-root limb GENUINELY MOVED across the spend (the grow-gate forces a
    // real insert; the after-root is NOT the before-root).
    assert_ne!(
        trace[0][BEFORE_BASE + B_NULLIFIER_ROOT],
        trace[trace.len() - 1][AFTER_BASE + B_NULLIFIER_ROOT],
        "the spend genuinely grows the nullifier set (the bound limb distinguishes BEFORE from AFTER)"
    );
    // The honest after-root IS the genuine sorted insert (the grow-gate is satisfiable — non-vacuous).
    let nf_key = trace[0][PARAM_BASE + param::NULLIFIER];
    let nf_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];
    let mut honest_after_leaves = before_nullifiers.clone();
    honest_after_leaves.push(HeapLeaf {
        addr: nf_key,
        value: nf_value,
    });
    let honest_after_root =
        CanonicalHeapTree8::new(honest_after_leaves, HEAP_TREE_DEPTH).root8()[0];
    assert_eq!(
        trace[trace.len() - 1][AFTER_BASE + B_NULLIFIER_ROOT],
        honest_after_root,
        "honest: the committed AFTER nullifier-root == the genuine sorted insert (grow-gate holds)"
    );

    // POSITIVE TOOTH (no downgrade): the honest noteSpend turn proves + verifies — light-client
    // path, no trusted post-cell.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: the honest noteSpend turn must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest noteSpend proof must verify independently");

    // NEGATIVE TOOTH (the bite): forge the AFTER nullifier-root (limb 26 of EVERY after block) to a
    // root the kernel NEVER grew, re-fill the dependent commit chain so the published commit is
    // self-consistent for the forged root, and re-derive the NEW commit PI. The `.write` map-op pins
    // the after-root to the GENUINE sorted insert, so a forged after-root has NO witness → UNSAT.
    // The declared spent nullifier (param0 / PI[46]) stays honest — the ONLY thing that breaks is
    // the in-circuit grow-gate. NO off-cell anchor is consulted.
    let bump = BabyBear::new(0x9999);
    let mut forged_trace = trace.clone();
    for row in forged_trace.iter_mut() {
        row[AFTER_BASE + B_NULLIFIER_ROOT] = row[AFTER_BASE + B_NULLIFIER_ROOT] + bump;
    }
    // Re-fill the after-block commit chain so STATE_COMMIT matches the forged limb (a clean,
    // self-consistent nullifier-root-ONLY post-state delta).
    recompute_after_blocks_for_test(&mut forged_trace);
    let mut forged_dpis = dpis.clone();
    forged_dpis[PI_NEW_COMMIT] = forged_trace[forged_trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];

    // The smoking gun: the committed AFTER nullifier-root is the FORGED value, but the spent
    // nullifier param is unchanged — the grow-gate's `after == insert(before, key)` precondition is
    // broken.
    assert_ne!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_NULLIFIER_ROOT],
        honest_after_root,
        "the forged AFTER nullifier-root is NOT the genuine sorted insert — the grow-gate's UNSAT precondition"
    );
    assert_ne!(
        forged_dpis[PI_NEW_COMMIT], dpis[PI_NEW_COMMIT],
        "the forged post-state publishes a DIFFERENT commit (it differs only in the nullifier-root)"
    );
    assert_eq!(
        forged_trace[0][PARAM_BASE + param::NULLIFIER],
        nf_key,
        "the declared spent nullifier is unchanged (the effect is honest; only the root is forged)"
    );

    assert!(
        refused(
            &desc,
            &forged_trace,
            &forged_dpis,
            &mem_boundary,
            &map_heaps
        ),
        "SOUNDNESS (light-client unfoolable, anchor-disabled): a post-state forged to differ ONLY \
         in the nullifier-root — a root the kernel never grew — MUST be UNSAT through prove/verify \
         ALONE; the in-circuit `.write` grow-gate (nullifierInsertOp) bites with NO off-cell \
         apply_effect_to_cell re-derivation"
    );

    eprintln!(
        "VK-EPOCH noteSpend FORCED ON-WIRE: honest spend proves+verifies; a nullifier-root-ONLY \
         forged post-state is UNSAT through verify_vm_descriptor2 ALONE (no off-cell anchor) — the \
         in-circuit grow-gate binds the grown nullifier set into the commitment for a ledgerless client."
    );
}

/// **noteCreate FORCED ON-WIRE (light-client-verifiable).** An honest noteCreate turn proves +
/// verifies; a post-state forged to differ ONLY in the commitments-root (limb 27 of the AFTER
/// block — and the published commit absorbing it — carry a root the kernel NEVER grew, while the
/// published note commitment stays honest) is UNSAT through `prove`/`verify` ALONE — the in-circuit
/// `.insert` grow-gate (`commitmentsInsertOp`) bites with NO off-cell anchor. noteCreate is
/// append-only (no `.absent` freshness precondition).
#[test]
fn notecreate_forced_on_wire_rejects_forged_commitments_root_anchor_disabled() {
    let before_balance: i64 = 60_000;
    let value: u64 = 250;

    let cm = BabyBear::new(0xC0FFEE);
    let effect = Effect::NoteCreate {
        commitment: cm,
        value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("NoteCreate is a cohort member");
    assert_eq!(name, "noteCreateVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated noteCreate descriptor parses");
    assert_eq!(
        desc.public_input_count, 51,
        "noteCreate PIs = ROT_NULLIFIER_PI_COUNT (47 = 46 rotated + 1 commitment-forcing pin) + \
         DFA_RC_LEN (4 dsl rc pins) = 51 (committed noteCreateVmDescriptor2R24)"
    );

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
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    // A non-empty BEFORE commitments set (distinct from the published commitment).
    let before_commitments = vec![
        HeapLeaf {
            addr: BabyBear::new(0x111),
            value: BabyBear::new(1),
        },
        HeapLeaf {
            addr: BabyBear::new(0x222),
            value: BabyBear::new(1),
        },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_create_trace_with_commitments_tree(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_commitments,
    )
    .expect("commitments-tree wiring must produce a deployment-real noteCreate trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    // ANTI-VACUITY: the commitments-root limb GENUINELY MOVED across the create.
    assert_ne!(
        trace[0][BEFORE_BASE + B_COMMITMENTS_ROOT],
        trace[trace.len() - 1][AFTER_BASE + B_COMMITMENTS_ROOT],
        "the create genuinely grows the commitments set (the bound limb distinguishes BEFORE from AFTER)"
    );
    // The honest after-root IS the genuine sorted insert (grow-gate satisfiable — non-vacuous).
    let cm_key = trace[0][PARAM_BASE + param::NULLIFIER]; // param0 (the commitment rides param slot 0)
    let cm_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];
    let mut honest_after_leaves = before_commitments.clone();
    honest_after_leaves.push(HeapLeaf {
        addr: cm_key,
        value: cm_value,
    });
    let honest_after_root =
        CanonicalHeapTree8::new(honest_after_leaves, HEAP_TREE_DEPTH).root8()[0];
    assert_eq!(
        trace[trace.len() - 1][AFTER_BASE + B_COMMITMENTS_ROOT],
        honest_after_root,
        "honest: the committed AFTER commitments-root == the genuine sorted insert (grow-gate holds)"
    );

    // POSITIVE TOOTH (no downgrade).
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: the honest noteCreate turn must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest noteCreate proof must verify independently");

    // NEGATIVE TOOTH: forge the AFTER commitments-root (limb 27 of every after block) to a root the
    // kernel never grew, re-fill the commit chain, re-derive the NEW commit PI. The `.insert` map-op
    // pins after == insert(before, key), so a forged after-root has NO witness → UNSAT. The
    // published note commitment stays honest. NO off-cell anchor.
    let bump = BabyBear::new(0x9999);
    let mut forged_trace = trace.clone();
    for row in forged_trace.iter_mut() {
        row[AFTER_BASE + B_COMMITMENTS_ROOT] = row[AFTER_BASE + B_COMMITMENTS_ROOT] + bump;
    }
    recompute_after_blocks_for_test(&mut forged_trace);
    let mut forged_dpis = dpis.clone();
    forged_dpis[PI_NEW_COMMIT] = forged_trace[forged_trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];

    assert_ne!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_COMMITMENTS_ROOT],
        honest_after_root,
        "the forged AFTER commitments-root is NOT the genuine sorted insert — the grow-gate's UNSAT precondition"
    );
    assert_ne!(
        forged_dpis[PI_NEW_COMMIT], dpis[PI_NEW_COMMIT],
        "the forged post-state publishes a DIFFERENT commit (it differs only in the commitments-root)"
    );
    assert_eq!(
        forged_trace[0][PARAM_BASE + param::NULLIFIER],
        cm_key,
        "the published note commitment is unchanged (the effect is honest; only the root is forged)"
    );

    // Sanity: the OLD commit pin is untouched (the forge is an AFTER-only delta).
    assert_eq!(
        forged_dpis[PI_OLD_COMMIT], dpis[PI_OLD_COMMIT],
        "the OLD commit pin is unchanged (the forge differs only in the AFTER commitments-root)"
    );

    assert!(
        refused(
            &desc,
            &forged_trace,
            &forged_dpis,
            &mem_boundary,
            &map_heaps
        ),
        "SOUNDNESS (light-client unfoolable, anchor-disabled): a post-state forged to differ ONLY \
         in the commitments-root — a root the kernel never grew — MUST be UNSAT through prove/verify \
         ALONE; the in-circuit `.insert` grow-gate (commitmentsInsertOp) bites with NO off-cell \
         apply_effect_to_cell re-derivation"
    );

    eprintln!(
        "VK-EPOCH noteCreate FORCED ON-WIRE: honest create proves+verifies; a commitments-root-ONLY \
         forged post-state is UNSAT through verify_vm_descriptor2 ALONE (no off-cell anchor) — the \
         in-circuit grow-gate binds the grown commitments set into the commitment for a ledgerless client."
    );
}

/// Resolve a WIDE rotated descriptor JSON by registry key (the 8-felt-commit geometry the LIVE
/// producer/verifier route through).
fn wide_rotated_descriptor_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV
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
        .unwrap_or_else(|| panic!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
}

/// **noteCreate FORCED ON-WIRE THROUGH THE LIVE WIDE PRODUCER (the routing weld).** The light-client
/// producer (`sdk::full_turn_proof` / `cipherclerk`) and verifier (`turn::executor::proof_verify`)
/// now ROUTE a NoteCreate lead through [`generate_rotated_note_create_wide`] — the commitments-set
/// grow-gate wide producer — exactly as note-spend routes through its nullifier-tree wide producer.
/// (Before the weld, NoteCreate fell through to `generate_rotated_transfer_shape_wide`, which carries
/// the bare 46-PI base and ERRORS on the 47-PI commitment-pinned NoteCreate base — fail-closed, the
/// honest create was UN-PROVABLE through the live wide path.)
///
/// This test exercises the EXACT wide producer the live path calls, at the wide (8-felt-commit, 67-PI)
/// geometry a light client verifies: an honest noteCreate proves + verifies through the WIDE
/// descriptor; a post-state forged to differ in the commitments-root (a root the kernel never grew)
/// is UNSAT — the in-circuit `.insert` grow-gate bites at the wide geometry too.
#[test]
fn notecreate_forced_on_wire_through_live_wide_producer() {
    let before_balance: i64 = 60_000;
    let value: u64 = 250;

    let cm = BabyBear::new(0xC0FFEE);
    let effect = Effect::NoteCreate {
        commitment: cm,
        value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("NoteCreate is a cohort member");
    assert_eq!(name, "noteCreateVmDescriptor2R24");

    // The WIDE descriptor (the 8-felt-commit geometry the live producer/verifier route through).
    let wide_desc = parse_vm_descriptor2(wide_rotated_descriptor_json(name))
        .expect("WIDE noteCreate descriptor parses");
    assert_eq!(
        wide_desc.public_input_count, 67,
        "WIDE noteCreate PIs = narrow 51-PI base (47 + 4 dsl rc) + 16 wide commit PIs = 67 \
         (committed wide noteCreateVmDescriptor2R24)"
    );

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
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    let before_commitments = vec![
        HeapLeaf {
            addr: BabyBear::new(0x111),
            value: BabyBear::new(1),
        },
        HeapLeaf {
            addr: BabyBear::new(0x222),
            value: BabyBear::new(1),
        },
    ];

    // THE LIVE WIDE PRODUCER (the exact function `full_turn_proof`/`cipherclerk`/`proof_verify` now
    // call for a NoteCreate lead).
    let (wide_trace, wide_dpis, wide_map_heaps) = generate_rotated_note_create_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_commitments,
    )
    .expect("the live wide note-create producer must build a wide trace (was fail-closed before the weld)");
    assert_eq!(
        wide_trace[0].len(),
        WIDE_WIDTH + CAP_OPEN_SPAN,
        "note-create is now the insert-shaped effAccumInsertV3 member: WIDE_WIDTH + the \
         CAP_OPEN_SPAN read appendix (the commitments-accumulator sorted-insert membership)"
    );
    assert_eq!(
        wide_dpis.len(),
        67,
        "wide PI vector (51 base = 47 + 4 dsl rc, + 16 wide commit PIs)"
    );

    // POSITIVE TOOTH (no downgrade): the honest noteCreate proves + verifies through the WIDE
    // descriptor — the geometry a light client runs.
    let proof = prove_vm_descriptor2(
        &wide_desc,
        &wide_trace,
        &wide_dpis,
        &mem_boundary,
        &wide_map_heaps,
    )
    .expect("NO DOWNGRADE: the honest noteCreate must prove through the live WIDE producer");
    verify_vm_descriptor2(&wide_desc, &proof, &wide_dpis)
        .expect("NO DOWNGRADE: the honest wide noteCreate proof must verify independently");

    // NEGATIVE TOOTH (the bite, at wide geometry, ISOLATED to the grow-gate): CLONE the honest WIDE
    // trace (insert-shaped, 1792, carrying the GENUINE §J′ insert READ appendix that opens the fresh
    // commitment against the honest post-insert root), forge the AFTER commitments-root limb (a root
    // the kernel never grew), re-fill the base AFTER-block commit chain (`recompute_after_blocks_for_test`)
    // AND re-fill the wide carriers over the forged base (`append_wide_carriers`, which resizes to the
    // SAME 1792 layout the honest producer laid at `ACCUM_INSERT_HOST_WIDTH`, re-reads the 8-felt wide
    // commit from the now-forged AFTER block, and re-derives the wide commit PIs — leaving the §J′
    // insert appendix at `ACCUM_INSERT_READ_BASE` UNTOUCHED). The forged trace is now FULLY
    // self-consistent at 1792 EXCEPT the in-circuit `.insert` grow-gate: the appendix still proves
    // `insert(before, key) == honest_root`, but the AFTER commitments-root limb is forged, so the
    // grow-gate pins the limb against the appendix's genuine post-insert root → forged ≠ honest → no
    // membership witness → UNSAT. This is a REAL grow-gate refuse — an adversary presenting a FULLY
    // self-consistent forged commit (matching carriers + PIs) is STILL caught by the grow-gate — NOT a
    // width mismatch and NOT a stale-carrier/PI mismatch.
    let bump = BabyBear::new(0x9999);
    let mut forged_trace = wide_trace.clone();
    for row in forged_trace.iter_mut() {
        row[AFTER_BASE + B_COMMITMENTS_ROOT] = row[AFTER_BASE + B_COMMITMENTS_ROOT] + bump;
    }
    recompute_after_blocks_for_test(&mut forged_trace);
    // Re-fill the wide carriers + re-derive the wide commit PIs over the forged base (the honest
    // producer's base PI prefix rides `wide_dpis[..base_pi_len]`; the wide append re-adds the 8 BEFORE
    // + 8 AFTER commit felts). This makes the wide 8-felt-commit absorb lookups + PI bindings hold for
    // the forged base, so the ONLY unsatisfiable constraint left is the grow-gate.
    let base_pi_len = wide_dpis.len() - 16;
    let forged_dpis = append_wide_carriers(
        &mut forged_trace,
        wide_dpis[..base_pi_len].to_vec(),
        ACCUM_INSERT_HOST_WIDTH,
    );
    assert_eq!(
        forged_trace[0].len(),
        WIDE_WIDTH + CAP_OPEN_SPAN,
        "forged wide width matches the insert-shaped WIDE_WIDTH + CAP_OPEN_SPAN"
    );
    assert_ne!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_COMMITMENTS_ROOT],
        wide_trace[wide_trace.len() - 1][AFTER_BASE + B_COMMITMENTS_ROOT],
        "the forged AFTER commitments-root differs from the honest (grow-gate's UNSAT precondition)"
    );

    // The forged wide trace is fully self-consistent (carriers + PIs re-derived over the forged base)
    // EXCEPT the `.insert` grow-gate: the appendix's genuine post-insert root ≠ the forged AFTER
    // commitments-root limb → no membership witness → UNSAT.
    assert!(
        refused(
            &wide_desc,
            &forged_trace,
            &forged_dpis,
            &mem_boundary,
            &wide_map_heaps
        ),
        "SOUNDNESS (light-client unfoolable, wide geometry): a forged commitments-root post-state is \
         UNSAT through the LIVE WIDE producer's descriptor — the in-circuit `.insert` grow-gate bites \
         with NO off-cell anchor, exactly as on the live producer/verifier path"
    );

    eprintln!(
        "VK-EPOCH noteCreate FORCED ON-WIRE (live wide routing): the honest create proves+verifies \
         through generate_rotated_note_create_wide (the exact producer full_turn_proof/cipherclerk/ \
         proof_verify now route for NoteCreate); a forged commitments-root is UNSAT at the 8-felt wide \
         geometry — the routing weld closes the fail-closed gap."
    );
}
