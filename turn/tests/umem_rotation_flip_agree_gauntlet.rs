//! # THE UMEM ROTATION-FLIP AGREE GAUNTLET — Rank 5, suite 1 (the semantic safety).
//!
//! The flag-day bump of the universal-map rotation needs ONE thing green before it
//! can flip: the executor's authoritative universal-map projection
//! (`record_kernel_boundary_agrees` — the Rank 2 anchor, `turn/src/umem.rs`) must
//! AGREE with the deployed per-map-table representation across the WHOLE cohort of
//! real turns, not just a single hand-built exemplar. This is the umem-form-vs-
//! deployed-per-map semantic-identity check — the differential the 3-verb circuit's
//! gauntlets anchor on.
//!
//! For every cohort effect's state-touch — transfer / set-field (register +
//! overflow) / set-heap (the openable `heap_map` plane) / grant / attenuate — this
//! suite executes a GENERATED CORPUS of real turns through the production
//! `TurnExecutor` and checks, over every after-cell:
//!
//!   * `record_kernel_boundary_agrees(cell)` is `Ok` (the universal-map projection
//!     reproduces, value-for-value, the committed `fields_root` / `heap_root` /
//!     canonical `cap_root`); and
//!   * the SPECIFIC plane the effect moved has its derived boundary root equal to
//!     the cell's committed root — spelled out so the agreement is no `== self`
//!     tautology (the derivation never reads the stored roots).
//!
//! The corpus lands entirely in the FAITHFUL CLASS (tombstone-free cells, per Rank
//! 2's scope): every cohort lane grows live caps contiguously and writes openable
//! map planes with no dropped state, so the derived roots match the deployed ones
//! exactly.
//!
//! VK-RISK-FREE: this drives the production executor and reads the committed
//! after-cells through pure projection/representation functions. No descriptor /
//! wire / VK touch; the recursion-gated `umem_witness_enabled` lane stays off the
//! proving path (we flip it on only to prove the authoritative representation
//! coexists with the witness lane untouched).

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, capability::CapabilityRef};
use dregg_turn::umem::{BoundaryDisagreement, RecordKernelBoundary, record_kernel_boundary_agrees};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

const STATE_SLOTS: usize = dregg_cell::state::STATE_SLOTS;

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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bytes(n: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0] = n;
    b[31] = n.wrapping_add(1);
    b
}

fn turn_with(agent: CellId, target: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn umem_executor() -> TurnExecutor {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    // Irrelevant to the bridge (we read the committed after-cells), but flip it
    // on to prove the authoritative representation coexists with the
    // recursion-gated-off witness lane untouched.
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);
    executor
}

/// THE GAUNTLET ASSERTION: every present cell of the after-ledger passes the
/// bridge agreement — the universal-map projection reproduces its per-map-table
/// roots. Returns the count of cells checked (a non-vacuity guard).
fn assert_ledger_agrees(ledger: &Ledger) -> usize {
    let mut n = 0;
    for (id, cell) in ledger.iter() {
        let r: Result<RecordKernelBoundary, BoundaryDisagreement> =
            record_kernel_boundary_agrees(cell);
        assert!(
            r.is_ok(),
            "cell {id:?} RecordKernelState projection must agree with its \
             per-map-table roots: {:?}",
            r.err()
        );
        n += 1;
    }
    n
}

/// Spell out the per-map-table representation a single cell's projection agrees
/// with (no tautology: `record_kernel_boundary_agrees` re-derives each root from
/// the projected plane alone, never reading these stored roots).
fn assert_cell_planes_agree(cell: &Cell) {
    let b = record_kernel_boundary_agrees(cell)
        .expect("cohort after-cell must agree with its per-map-table roots");
    assert_eq!(b.fields_root, cell.state.fields_root, "derived fields_root");
    assert_eq!(b.heap_root, cell.state.heap_root, "derived heap_root");
    assert_eq!(
        b.cap_root,
        dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities),
        "derived cap_root (the EffectVM cap_root column)"
    );
}

// ===========================================================================
// LANE 1 — transfer (the paired debit/credit balance writes).
// The roots are untouched; the projection must still reproduce them exactly.
// ===========================================================================
#[test]
fn agree_gauntlet_transfer_corpus() {
    let mut checked = 0usize;
    for (i, &(a_bal, t_bal, amount)) in [
        (1000i64, 10i64, 7u64),
        (5_000, 0, 1),
        (42, 42, 42),
        (1_000_000, 999, 500_000),
        (300, 250, 300),
    ]
    .iter()
    .enumerate()
    {
        let seed = 10 + i as u8 * 2;
        let agent = make_open_cell(seed, a_bal);
        let target = make_open_cell(seed + 1, t_bal);
        let (agent_id, target_id) = (agent.id(), target.id());
        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(target).unwrap();

        let executor = umem_executor();
        let turn = turn_with(
            agent_id,
            agent_id,
            0,
            vec![Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount,
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(r.is_committed(), "transfer corpus #{i} must commit: {r:?}");

        checked += assert_ledger_agrees(&ledger);
        assert_cell_planes_agree(ledger.get(&agent_id).unwrap());
        assert_cell_planes_agree(ledger.get(&target_id).unwrap());
    }
    assert!(
        checked >= 10,
        "the transfer corpus checked real after-cells"
    );
}

// ===========================================================================
// LANE 2 — set-field, REGISTER plane (slot < STATE_SLOTS): never part of
// `fields_root`, so the derived root stays the empty constant and agrees.
// ===========================================================================
#[test]
fn agree_gauntlet_set_field_register_corpus() {
    let mut checked = 0usize;
    for (i, &(slot, v)) in [(0usize, 1u8), (2, 7), (8, 13), (15, 200), (5, 99)]
        .iter()
        .enumerate()
    {
        assert!(slot < STATE_SLOTS, "register plane");
        let seed = 40 + i as u8;
        let agent = make_open_cell(seed, 100);
        let agent_id = agent.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();

        let executor = umem_executor();
        let turn = turn_with(
            agent_id,
            agent_id,
            0,
            vec![Effect::SetField {
                cell: agent_id,
                index: slot,
                value: bytes(v),
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(r.is_committed(), "set-field(reg) #{i} must commit: {r:?}");

        checked += assert_ledger_agrees(&ledger);
        let after = ledger.get(&agent_id).unwrap();
        assert_cell_planes_agree(after);
        // register write does NOT move fields_root.
        assert_eq!(
            after.state.fields_root,
            dregg_cell::state::empty_fields_root(),
            "a register-plane (slot<16) write leaves fields_root empty"
        );
    }
    assert!(checked >= 5);
}

// ===========================================================================
// LANE 3 — set-field, OVERFLOW plane (slot >= STATE_SLOTS): the openable
// `fields_map`. The write MOVES `fields_root`; the projection reproduces it.
// ===========================================================================
#[test]
fn agree_gauntlet_set_field_overflow_corpus() {
    let mut checked = 0usize;
    for (i, &(slot, v)) in [(16usize, 5u8), (42, 9), (99, 17), (16, 200), (1000, 3)]
        .iter()
        .enumerate()
    {
        assert!(slot >= STATE_SLOTS, "overflow plane");
        let seed = 60 + i as u8;
        let agent = make_open_cell(seed, 100);
        let agent_id = agent.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();

        let executor = umem_executor();
        let turn = turn_with(
            agent_id,
            agent_id,
            0,
            vec![Effect::SetField {
                cell: agent_id,
                index: slot,
                value: bytes(v),
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(
            r.is_committed(),
            "set-field(overflow) #{i} must commit: {r:?}"
        );

        checked += assert_ledger_agrees(&ledger);
        let after = ledger.get(&agent_id).unwrap();
        assert_eq!(
            after.state.get_field_ext(slot as u64),
            Some(bytes(v)),
            "overflow write landed in fields_map"
        );
        // the overflow write MOVED fields_root off the empty constant, and the
        // projection's derived root reproduces the committed one.
        assert_ne!(
            after.state.fields_root,
            dregg_cell::state::empty_fields_root(),
            "an overflow write moves fields_root"
        );
        assert_cell_planes_agree(after);
    }
    assert!(checked >= 5);
}

// ===========================================================================
// LANE 4 — set-heap (the openable `heap_map` plane / `heap_root`). No deployed
// effect writes `heap_map`, so the corpus exercises the plane by seeding genuine
// heap state on a cell that a real turn then commits — the after-cell carries a
// non-trivial `heap_map`, and its projected `Heap` plane must re-derive the
// committed `heap_root`.
// ===========================================================================
#[test]
fn agree_gauntlet_set_heap_corpus() {
    let mut checked = 0usize;
    let corpus: &[&[(u32, u32, u8)]] = &[
        &[(3, 5, 11)],
        &[(3, 5, 11), (3, 9, 12), (7, 1, 13)],
        &[(0, 0, 1), (0, 1, 2), (1, 0, 3), (1, 1, 4)],
        &[(42, 7, 99), (42, 8, 100)],
    ];
    for (i, entries) in corpus.iter().enumerate() {
        let seed = 80 + i as u8;
        let mut agent = make_open_cell(seed, 500);
        for &(c, k, v) in entries.iter() {
            agent.state.set_heap(c, k, bytes(v));
        }
        assert_ne!(
            agent.state.heap_root,
            dregg_cell::state::empty_heap_root(),
            "seeded heap moved heap_root"
        );
        let agent_id = agent.id();
        let target = make_open_cell(seed.wrapping_add(128), 0);
        let target_id = target.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(target).unwrap();

        // a real turn that commits the heap-bearing cell (a transfer touching it).
        let executor = umem_executor();
        let turn = turn_with(
            agent_id,
            agent_id,
            0,
            vec![Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 1,
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(
            r.is_committed(),
            "heap-bearing turn #{i} must commit: {r:?}"
        );

        checked += assert_ledger_agrees(&ledger);
        let after = ledger.get(&agent_id).unwrap();
        assert_eq!(after.state.heap_map.len(), entries.len(), "heap survived");
        // the projected Heap plane re-derives the committed heap_root.
        assert_cell_planes_agree(after);
    }
    assert!(checked >= 8);
}

// ===========================================================================
// LANE 5 — grant (Effect::GrantCapability, self-grant): a fresh LIVE cap lands
// in the `CapSlot` plane; the canonical `cap_root` MOVES and the projection
// reproduces it. Self-grants stay contiguous-from-0 (the faithful, tombstone-
// free class).
// ===========================================================================
#[test]
fn agree_gauntlet_grant_corpus() {
    let mut checked = 0usize;
    for (i, perm) in [
        AuthRequired::None,
        AuthRequired::Signature,
        AuthRequired::Either,
    ]
    .into_iter()
    .enumerate()
    {
        let seed = 100 + i as u8;
        let agent = make_open_cell(seed, 1000);
        let agent_id = agent.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();

        let before_root = dregg_cell::compute_canonical_capability_root_felt(
            &ledger.get(&agent_id).unwrap().capabilities,
        );

        let executor = umem_executor();
        // self-grant: from == to == cap.target == agent (authorized by the signed
        // action; no c-list lookup, always-faithful attenuation of the implicit
        // self-cap).
        let cap = CapabilityRef {
            target: agent_id,
            slot: 0, // executor reassigns to the live next_slot.
            permissions: perm,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let turn = turn_with(
            agent_id,
            agent_id,
            0,
            vec![Effect::GrantCapability {
                from: agent_id,
                to: agent_id,
                cap,
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(r.is_committed(), "grant #{i} must commit: {r:?}");

        checked += assert_ledger_agrees(&ledger);
        let after = ledger.get(&agent_id).unwrap();
        assert!(
            !after.capabilities.iter().next().is_none(),
            "a live cap landed"
        );
        let after_root = dregg_cell::compute_canonical_capability_root_felt(&after.capabilities);
        assert_ne!(after_root, before_root, "the grant moved cap_root");
        assert_cell_planes_agree(after);
    }
    assert!(checked >= 3);
}

// ===========================================================================
// LANE 6 — attenuate (Effect::AttenuateCapability): the guarded narrow write
// rewrites a live `CapSlot` in place; the canonical `cap_root` MOVES and the
// projection reproduces it (no tombstone — attenuation narrows, never revokes).
// ===========================================================================
#[test]
fn agree_gauntlet_attenuate_corpus() {
    let mut checked = 0usize;
    // Every case is a GENUINE narrowing (Either -> Signature, with a varying
    // tighter expiry) so the canonical cap_root provably moves — an identity
    // narrowing (e.g. Either -> Either) is a no-op on the root and would not
    // exercise the "moved cap_root" tooth.
    for (i, expiry) in [None, Some(100u64), Some(1u64)].into_iter().enumerate() {
        let seed = 120 + i as u8;
        let actor = make_open_cell(seed, 1000);
        let target = make_open_cell(seed + 1, 0);
        let (actor_id, target_id) = (actor.id(), target.id());

        let mut actor_with_cap = actor;
        let slot = actor_with_cap
            .capabilities
            .grant(target_id, AuthRequired::Either)
            .unwrap();
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor_with_cap).unwrap();
        ledger.insert_cell(target).unwrap();

        let before_root = dregg_cell::compute_canonical_capability_root_felt(
            &ledger.get(&actor_id).unwrap().capabilities,
        );

        let executor = umem_executor();
        let turn = turn_with(
            actor_id,
            actor_id,
            0,
            vec![Effect::AttenuateCapability {
                cell: actor_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: expiry,
            }],
        );
        let r = executor.execute(&turn, &mut ledger);
        assert!(r.is_committed(), "attenuate #{i} must commit: {r:?}");

        checked += assert_ledger_agrees(&ledger);
        let after = ledger.get(&actor_id).unwrap();
        let after_root = dregg_cell::compute_canonical_capability_root_felt(&after.capabilities);
        assert_ne!(after_root, before_root, "attenuation moved cap_root");
        // no tombstone: the live cap count is unchanged (narrowed in place).
        assert_eq!(after.capabilities.iter().count(), 1, "narrowed in place");
        assert_cell_planes_agree(after);
    }
    assert!(checked >= 3);
}

// ===========================================================================
// THE COMBINED LANE — a multi-verb turn touching every cohort plane at once
// (transfer + overflow set-field + heap-bearing cell + attenuate): the whole
// after-ledger agrees. The flag-day's worst case is a turn that moves
// fields_root AND cap_root on the same cell while balances flow — the projection
// reproduces all of them.
// ===========================================================================
#[test]
fn agree_gauntlet_combined_multi_verb() {
    let mut actor = make_open_cell(200, 1000);
    actor.state.set_heap(9, 1, bytes(50)); // pre-seeded heap plane.
    let target = make_open_cell(201, 10);
    let (actor_id, target_id) = (actor.id(), target.id());
    let slot = actor
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    let turn = turn_with(
        actor_id,
        actor_id,
        0,
        vec![
            Effect::Transfer {
                from: actor_id,
                to: target_id,
                amount: 7,
            },
            Effect::SetField {
                cell: actor_id,
                index: 50, // overflow → fields_root.
                value: bytes(42),
            },
            Effect::AttenuateCapability {
                cell: actor_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
    );
    let r = executor.execute(&turn, &mut ledger);
    assert!(
        r.is_committed(),
        "combined multi-verb turn must commit: {r:?}"
    );

    let checked = assert_ledger_agrees(&ledger);
    assert!(checked >= 2);

    let after = ledger.get(&actor_id).unwrap();
    // every moved plane reproduces: fields_root (overflow write), heap_root
    // (seeded), cap_root (attenuation).
    assert_ne!(
        after.state.fields_root,
        dregg_cell::state::empty_fields_root()
    );
    assert_ne!(after.state.heap_root, dregg_cell::state::empty_heap_root());
    assert_cell_planes_agree(after);
}
