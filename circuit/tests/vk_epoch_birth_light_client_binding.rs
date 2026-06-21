//! # THE VK-EPOCH BIRTH-FAMILY LIGHT-CLIENT BINDING BITE — createCell / factory / spawn FORCED ON-WIRE.
//!
//! ## What this closes (`docs/VK-EPOCH-PLAN.md`, STAGE B / Family A — the BIRTH family)
//!
//! Family 1 (`vk_epoch_perms_vk_light_client_binding.rs`, commit d58545a5f) proved setPermissions /
//! setVK are FORCED-ON-WIRE via an in-circuit DIGEST-LIMB WELD (`permsVKWeldGate`: committed AFTER
//! perms/vk sub-limb == declared `param0`). The BIRTH family — createCell, createCellFromFactory,
//! spawn — rides a DIFFERENT (and stronger) in-circuit primitive: the ACCOUNTS-SET GROW-GATE on the
//! rotated `cells_root` limb (limb 0), the deployment-real sibling of the noteSpend nullifier
//! grow-gate. It is NOT a single-felt weld; it is a sorted-Poseidon2 MAP-OP pair the live
//! `{createCell,factory,spawn}VmDescriptor2R24` carry (`EffectVmEmitRotationV3.{createCellV3,
//! factoryV3,spawnV3}`):
//!
//!   * `cellsFreshOp` (`.absent`) — the new-cell key is a NON-MEMBER of the BEFORE accounts tree
//!     (no id collision);
//!   * `cellsInsertOp` (`.insert`) — the AFTER `cells_root` IS the GENUINE sorted insert of the
//!     new-cell key into the BEFORE accounts tree.
//!
//! The AFTER `cells_root` limb (limb 0) is ABSORBED by `wireCommitR` into the published
//! `B_STATE_COMMIT` carrier → the rotated `NEW_COMMIT` anchor (PI 43). So the binding chain a LIGHT
//! CLIENT verifies, with NO trusted post-cell, is:
//!
//!     NEW_COMMIT (PI 43, the claimed rotated NEW commit)  ⟹  B_STATE_COMMIT carrier
//!       ⟹  AFTER cells_root limb (absorbed)  ⟹  (`.insert` map-op) == insert(BEFORE cells_root, key)
//!       ⟹  (`.absent` map-op) key ∉ BEFORE  ⟹  key == PI 46 (the new-cell-key pin, == effect param)
//!
//! A forged post-state — a turn that CLAIMS a cell was born but whose AFTER accounts root is NOT the
//! genuine sorted insert (a fabricated root, or a FROZEN root with no growth) — absorbs a `cells_root`
//! the `.insert` op cannot witness, so `prove_vm_descriptor2` has no satisfying assignment → UNSAT.
//! The map-op threads the BEFORE accounts leaf-set as the single `map_heaps` entry; it is the SAME
//! sorted-Poseidon2 set-membership the circuit already enforces for noteSpend.
//!
//! ## The light-client discriminator (the plan's bar, §6 / the guardrail)
//!
//! Both teeth run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE — the same circuit
//! verify a light client runs (`sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`, which
//! NEVER calls `apply_effect_to_cell`). So this is INHERENTLY the anchor-disabled discriminator: a
//! reject here is the IN-CIRCUIT grow-gate biting, NOT the host re-derivation.
//!
//!   * POSITIVE (no downgrade): an HONEST createCell / factory / spawn turn over a GENUINE grown
//!     accounts-set proves + verifies.
//!   * NEGATIVE (the bite), two poles per effect:
//!       - FORGED after-root: the AFTER `cells_root` is bumped to a set the kernel never grew (the
//!         dependent commit + NEW_COMMIT PI recomputed self-consistently) — UNSAT (the `.insert` op
//!         pins the after-root to the genuine insert);
//!       - FROZEN after-root: the AFTER `cells_root` EQUALS the BEFORE (no growth — the pre-grow-gate
//!         shape) — UNSAT (the `.insert` op forces `after = insert(before, key) ≠ before`).
//!
//! Unlike family-2 (refusal/lifecycle PAYLOAD), there is NO off-cell-anchor residual here: the
//! grow-gate is genuinely in-circuit, so all three birth effects are LIGHT-CLIENT FORCED-ON-WIRE.
//!
//! Gated on `prover` (compiles `descriptor_ir2`). Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_birth_light_client_binding -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::PARAM_BASE;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_STATE_COMMIT, BEFORE_BASE, ROT_WIDTH, RotatedBlockWitness, V1_PI_COUNT,
    empty_caveat_manifest, generate_rotated_create_cell_trace_with_accounts_tree,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_turn::rotation_witness as rw;

/// The rotated `cells_root` accounts-accumulator limb (limb 0 of every rotated block).
const B_CELLS_ROOT: usize = 0;
/// The rotated NEW_COMMIT public input (rotated commit pair = PI 42/43).
const PI_NEW_COMMIT: usize = V1_PI_COUNT + 1;

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

/// The producer's before-cell (the actor cell the birth turn opens over).
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
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
    desc: &EffectVmDescriptor2,
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

/// The shared birth-family discriminator harness. Given a birth `effect`, its expected rotated
/// descriptor `name`, and the param column carrying the new-cell key (`key_col`: 0 for
/// createCell/spawn, 1/CHILD_VK_DERIVED for factory), it asserts BOTH poles through the
/// LIGHT-CLIENT path (`prove`/`verify` ALONE — no off-cell anchor):
///   * POSITIVE: the honest grown-accounts-set turn proves + verifies.
///   * NEGATIVE #1 (forged after-root): a bumped AFTER `cells_root` (commit recomputed) is UNSAT.
///   * NEGATIVE #2 (frozen after-root): AFTER `cells_root` == BEFORE (no growth) is UNSAT.
fn assert_birth_forced_on_wire(effect: Effect, name: &str, key_col: usize, label: &str) {
    let resolved =
        rotated_descriptor_name_for_effect(&effect).expect("birth effect is a rotated cohort member");
    assert_eq!(resolved, name, "{label}: expected rotated descriptor name");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated birth descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "{label}: birth descriptor carries 46 prefix PIs + the appended new-cell-key pin"
    );

    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![effect];

    // The before/after producer witnesses (the birth actor row freezes the balance + ticks the
    // nonce; `cells_root` is then overridden by the accounts-tree grow-gate wrapper).
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
    let before_w =
        rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    // A non-empty BEFORE accounts set (distinct from the new-cell key — the `.absent` precondition).
    let before_accounts = vec![
        HeapLeaf { addr: BabyBear::new(0xAA01), value: BabyBear::new(0xAA01) },
        HeapLeaf { addr: BabyBear::new(0xAA02), value: BabyBear::new(0xAA02) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_create_cell_trace_with_accounts_tree(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_accounts,
    )
    .expect("accounts-tree grow-gate wiring must produce a deployment-real birth trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");
    assert_eq!(dpis.len(), 47, "{label}: birth rotated PI is 47 (new-cell-key slot appended)");

    // ANTI-VACUITY: the grow-gate GENUINELY moved limb 0 (the AFTER accounts root differs from the
    // BEFORE root — the set actually grew; the close is not over a frozen column).
    let before_root = CanonicalHeapTree::new(before_accounts.clone(), HEAP_TREE_DEPTH).root();
    assert_eq!(
        trace[0][BEFORE_BASE + B_CELLS_ROOT],
        before_root,
        "{label}: BEFORE cells_root limb == the genuine BEFORE accounts root"
    );
    assert_ne!(
        trace[trace.len() - 1][AFTER_BASE + B_CELLS_ROOT],
        before_root,
        "{label}: AFTER cells_root limb GREW (anti-omission — the insert actually happened)"
    );
    // The published new-cell-key pin (PI 46) IS the create-row key column (the effect param).
    assert_eq!(
        dpis[46], trace[0][PARAM_BASE + key_col],
        "{label}: PI 46 = the create row's new-cell key (param[{key_col}])"
    );

    // POSITIVE TOOTH (no downgrade): the honest birth turn proves + verifies — light-client path,
    // no trusted post-cell.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .unwrap_or_else(|e| panic!("{label}: NO DOWNGRADE: honest birth turn must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("{label}: NO DOWNGRADE: honest birth proof must verify: {e}"));

    // NEGATIVE TOOTH #1 (FORGED after-root): bump the AFTER cells_root (limb 0 of every after-block)
    // to a set the kernel never grew; recompute the dependent commit + NEW_COMMIT PI self-consistently.
    // The `.insert` map-op pins the after-root to the GENUINE sorted insert, so the forged root has no
    // witness → UNSAT through prove/verify ALONE (the in-circuit grow-gate, no off-cell anchor).
    {
        let bump = BabyBear::new(0x9999);
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[AFTER_BASE + B_CELLS_ROOT] = row[AFTER_BASE + B_CELLS_ROOT] + bump;
        }
        let mut p = dpis.clone();
        p[PI_NEW_COMMIT] = t[t.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // self-consistent forged NEW_COMMIT
        assert!(
            refused(&desc, &t, &p, &mem_boundary, &map_heaps),
            "{label}: SOUNDNESS (light-client unfoolable, anchor-disabled): a FORGED after \
             cells_root (a set the kernel never grew) MUST be UNSAT through prove/verify ALONE — \
             the in-circuit `.insert` grow-gate pins the after-root, NO off-cell apply_effect_to_cell"
        );
    }

    // NEGATIVE TOOTH #2 (FROZEN after-root): AFTER cells_root EQUALS the BEFORE (no growth — the
    // pre-grow-gate shape). The `.insert` op forces `after = insert(before, key) ≠ before`, so a
    // frozen accounts root has no witness → UNSAT.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[BEFORE_BASE + B_CELLS_ROOT] = before_root;
            row[AFTER_BASE + B_CELLS_ROOT] = before_root; // FROZEN: after == before
        }
        assert!(
            refused(&desc, &t, &dpis, &mem_boundary, &map_heaps),
            "{label}: SOUNDNESS: a FROZEN cells_root (after == before, no growth) MUST be UNSAT — \
             the `.insert` grow-gate forces a genuine insert"
        );
    }

    eprintln!(
        "VK-EPOCH {label} FORCED ON-WIRE: honest birth proves+verifies; a forged AND a frozen \
         cells_root are each UNSAT through verify_vm_descriptor2 ALONE (no off-cell anchor) — the \
         in-circuit accounts-set `.insert` grow-gate binds the born cell into the commitment for a \
         ledgerless client."
    );
}

/// **createCell FORCED ON-WIRE (light-client-verifiable).** An honest createCell turn over a genuine
/// grown accounts set proves + verifies; a forged OR frozen AFTER `cells_root` is UNSAT through
/// `prove`/`verify` ALONE — the in-circuit accounts-set grow-gate bites with NO off-cell anchor.
#[test]
fn createcell_forced_on_wire_rejects_forged_cells_root_anchor_disabled() {
    let new_cell_id = BabyBear::new(0xCE11);
    let effect = Effect::CreateCell {
        create_hash: [new_cell_id; 8],
    };
    assert_birth_forced_on_wire(effect, "createCellVmDescriptor2R24", 0, "createCell");
}

/// **createCellFromFactory FORCED ON-WIRE (light-client-verifiable).** The factory twin of the
/// createCell bite: the born child's key rides `param1` (CHILD_VK_DERIVED), and the SAME accounts-set
/// grow-gate (limb 0, `cellsInsertOp .insert`) forces the genuine sorted insert. A forged/frozen
/// `cells_root` is UNSAT through the light-client path ALONE.
#[test]
fn factory_forced_on_wire_rejects_forged_cells_root_anchor_disabled() {
    // The derived child VK is the born child's key (the grow-gate key column for factory = param1).
    let effect = Effect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC0),
        child_vk_derived: BabyBear::new(0xC417),
    };
    assert_birth_forced_on_wire(
        effect,
        "factoryVmDescriptor2R24",
        dregg_circuit::effect_vm::columns::param::CHILD_VK_DERIVED,
        "createCellFromFactory",
    );
}

/// **spawn FORCED ON-WIRE (light-client-verifiable).** The spawn twin: the born child's key rides
/// `param0`, and the SAME accounts-set grow-gate (limb 0) forces the genuine sorted insert. A
/// forged/frozen `cells_root` is UNSAT through the light-client path ALONE.
///
/// NOTE (the named spawn residual): spawn ALSO performs a CAP-HANDOFF (the child cap-root move +
/// delegation snapshot), which is ORTHOGONAL to the accounts-set insert and rides the cap-write
/// axis (§A of the plan, the cap-write data-availability work owned by a parallel batch). THIS test
/// closes spawn's ACCOUNTS-SET birth column on-wire; the cap-handoff column is a separate axis.
#[test]
fn spawn_forced_on_wire_rejects_forged_cells_root_anchor_disabled() {
    let spawn_id = BabyBear::new(0x5BA1);
    let effect = Effect::SpawnWithDelegation {
        spawn_hash: [spawn_id; 8],
    };
    assert_birth_forced_on_wire(effect, "spawnVmDescriptor2R24", 0, "spawn");
}
