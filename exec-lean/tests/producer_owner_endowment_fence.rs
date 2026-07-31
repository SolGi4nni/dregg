//! ⚑ THE OWNER-ENDOWMENT FENCE — the `GrantCapability` shape the verified kernel gets WRONG.
//!
//! ## The disagreeing turn
//!
//! `Effect::GrantCapability { from: A, to: B, cap: CapabilityRef { target: A, .. } }` where `A`'s
//! c-list is EMPTY — which is every cell's FIRST grant, because `Cell::new`/`Cell::with_balance`
//! mint a cell with no capabilities.
//!
//! * **dregg1 COMMITS.** `apply_grant_capability` (`turn/src/executor/apply.rs:760`) short-circuits
//!   a self-grant: `if cap.target == *from { /* skip c-list lookup */ }`. Authority is the action's
//!   own authorization against `from`, enforced upstream in `execute_tree`. A cell is the ORIGIN of
//!   authority over itself.
//! * **The verified kernel REJECTS.** The wire projects the effect to `WireAction::Delegate`, which
//!   routes to `recKDelegate` (`metatheory/Dregg2/Exec/AuthTurn.lean:174`), gated SOLELY on
//!   `(k.caps delegator).any (fun cap => confersEdgeTo t cap) = true`.
//!
//! ## Which decider is right: the KERNEL is over-refusing
//!
//! Not a preference — an argument:
//!
//! 1. The kernel's own SIBLING gate has the disjunct. `authorizedB` (`Dregg2/Exec/Kernel.lean:54`)
//!    is `(turn.actor == turn.src) || (caps …).any …`, and `stateAuthB` routes through it. So the
//!    same kernel lets a cell write its own fields and move its own balance from an empty c-list,
//!    and refuses to let it delegate any of that. That is an internal inconsistency, not a boundary.
//! 2. `caps = fun _ => []` is a FIXPOINT of the modelled authority calculus. `recKDelegate`,
//!    `recKDelegateAtten` and `introduceA` each require a pre-existing edge; `recKRevokeTarget` only
//!    removes. No Lean rule creates a first edge, so the modelled cap graph can never acquire one.
//!    That is Granovetter with its base cases (initial conditions / parenthood / self-reference)
//!    deleted, not the Granovetter property.
//! 3. Nothing is amplified. The granted authority is over `from` ITSELF, and `from`'s own
//!    authorization gate already ran. There is no authority the granter lacks.
//!
//! **The repair is a LEAN change** to `recKDelegate`'s guard in `metatheory/Dregg2/Exec/AuthTurn.lean`
//! — the owner disjunct its sibling already has. Until that lands, the honest classification is that
//! the owner-endowment shape is OUTSIDE the swap-safe covered set (the treatment `Mint` got on
//! 2026-07-30 for a MODEL divergence), so it is FENCED with a named reason rather than letting the
//! covered path install a wrong kernel REJECT as authoritative.
//!
//! ## What this file pins — both poles, by VARIANT
//!
//! * `owner_endowment_is_fenced_and_commits` — the fenced pole: the exact `deos_host_e2e` turn now
//!   resolves to `Fallback { RootGap { kind: AUTHORITY_ORIGIN_GAP } }` (asserted by variant AND by
//!   the exact kind string, never `is_err()`), the turn COMMITS, and the cap actually lands.
//! * `cross_cell_grant_without_a_held_edge_is_still_the_verified_kernels_refusal` — **the other
//!   decider still refuses what it should.** The amplification-relevant half (a cross-cell grant
//!   with no held edge) stays on the VERIFIED path — `LeanAuthoritative { committed: false }`, NOT
//!   a fallback — so the fence did not buy the green by taking the dangerous shape off the kernel.
//! * `the_fence_predicate_discriminates_shape` — the fence can go red: the predicate is `Some` for
//!   the endowment shape and `None` for delegation, so it is not a blanket opt-out of the effect.
//! * `kernel_still_refuses_the_owner_endowment_BURNDOWN` — the burn-down tooth. It drives the LIVE
//!   FFI and asserts the kernel STILL refuses. When the Lean repair lands this test FAILS, with a
//!   message telling the next reader to DELETE the fence. A fence whose premise silently becomes
//!   false is a permanent detour.

use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{
    ExtractError, ProducerOutcome, execute_via_lean, produce_via_lean,
};
use dregg_exec_lean::lean_shadow::{
    self, AUTHORITY_ORIGIN_GAP, ShadowHostCtx, first_unmodelled_authority_origin_effect,
};
use dregg_turn::{ActionBuilder, ComputronCosts, Effect, TurnBuilder, TurnExecutor};

fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    let mut cell = Cell::with_balance(public_key, [2u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn cap_over(target: CellId) -> CapabilityRef {
    CapabilityRef {
        target,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance: [0u8; 32],
    }
}

/// A one-effect turn whose agent AND action target are `agent` (so the agent-reach fence passes and
/// the shape under test is the only thing deciding coverage).
fn grant_turn(agent: CellId, effect: Effect) -> dregg_turn::Turn {
    let action = ActionBuilder::new_unchecked_for_tests(agent, "grant", agent)
        .effect(effect)
        .build();
    let mut builder = TurnBuilder::new(agent, 0);
    builder.add_action(action);
    builder.valid_until(1_000).build()
}

/// The `deos_host_e2e` shape: an EMPTY-c-list cell self-grants a cap over itself to another cell.
fn owner_endowment_fixture() -> (Ledger, CellId, CellId, dregg_turn::Turn) {
    let door = open_cell(1, 1_000_000);
    let door_id = door.id();
    let player = open_cell(2, 1_000_000);
    let player_id = player.id();
    assert!(
        door.capabilities.iter().next().is_none(),
        "PRECONDITION: a freshly minted cell holds NO capabilities — this is why the kernel's \
         missing owner disjunct refuses every cell's FIRST grant, not a corner case"
    );
    let mut ledger = Ledger::new();
    ledger.insert_cell(door).unwrap();
    ledger.insert_cell(player).unwrap();
    let turn = grant_turn(
        door_id,
        Effect::GrantCapability {
            from: door_id,
            to: player_id,
            cap: cap_over(door_id),
        },
    );
    (ledger, door_id, player_id, turn)
}

/// POLE 1 (the fenced pole). The owner-endowment self-grant is OUTSIDE the covered set, is fenced
/// with the NAMED reason, and COMMITS — instead of being vetoed by `TurnError::LeanShadowVeto`.
#[test]
fn owner_endowment_is_fenced_and_commits() {
    let (mut ledger, door_id, player_id, turn) = owner_endowment_fixture();

    assert!(
        !lean_shadow::forest_is_root_agreeing(&turn),
        "the owner-endowment shape must be OUTSIDE the swap-safe covered set; while it was inside, \
         the covered path installed the kernel's (wrong) REJECT as authoritative"
    );
    assert!(
        lean_shadow::forest_is_marshallable(&turn),
        "the turn is still MARSHALLABLE — the fence is a coverage judgement, not a wire gap; if \
         this flips, the fallback reason below stops being RootGap and the test asserts the wrong \
         thing"
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    // BY VARIANT, and by the exact kind string — never `is_err()`. A `RootGap` naming some OTHER
    // effect, or the `"unknown"` nothing-named fallback, must not satisfy this.
    match &outcome {
        ProducerOutcome::Fallback {
            reason: ExtractError::RootGap { kind },
        } => assert_eq!(
            *kind, AUTHORITY_ORIGIN_GAP,
            "the fence must NAME the owner-endowment shape; a fallback that names nothing is the \
             silent skip `produce_via_lean` exists to prevent"
        ),
        other => panic!(
            "owner-endowment must be FENCED as a named RootGap, got {other:?} — if this is \
             LeanAuthoritative the fence was removed and the kernel's wrong REJECT is \
             authoritative again (dregg-node::deos_host_e2e dies on LeanShadowVeto)"
        ),
    }

    match &result {
        dregg_turn::TurnResult::Committed { .. } => {}
        dregg_turn::TurnResult::Rejected { reason, .. } => panic!(
            "a cell endowing a capability over ITSELF must COMMIT (dregg1 grants it from \
             ownership); got {reason:?}"
        ),
        other => panic!("expected Committed, got {other:?}"),
    }

    let granted = ledger
        .get(&player_id)
        .expect("grantee present")
        .capabilities
        .iter()
        .any(|c| c.target == door_id);
    assert!(
        granted,
        "the endowed capability must actually land in the grantee's c-list — a commit bit with no \
         cap is not the effect being tested"
    );
}

/// POLE 2 — **THE OTHER DECIDER STILL REFUSES WHAT IT SHOULD.** The fence is a SHAPE fence, so the
/// amplification-relevant half of `GrantCapability` (a cross-cell grant where the granter holds no
/// edge to the target) is still decided by the VERIFIED kernel, and still REFUSED. If this ever
/// reports `Fallback`, the fence widened from a shape to the whole effect and the verified gate
/// stopped deciding the case that can actually amplify authority.
#[test]
fn cross_cell_grant_without_a_held_edge_is_still_the_verified_kernels_refusal() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment fence: the verified-refusal pole)",
    ) {
        return;
    }
    let a = open_cell(1, 100);
    let a_id = a.id();
    let b = open_cell(2, 5);
    let b_id = b.id();
    let c = open_cell(3, 5);
    let c_id = c.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(b).unwrap();
    ledger.insert_cell(c).unwrap();

    // A grants B a cap over C. A holds NO edge to C, and `cap.target != from`, so this is the
    // DELEGATION half — the one the verified kernel genuinely models.
    let turn = grant_turn(
        a_id,
        Effect::GrantCapability {
            from: a_id,
            to: b_id,
            cap: cap_over(c_id),
        },
    );

    assert_eq!(
        first_unmodelled_authority_origin_effect(&turn),
        None,
        "a CROSS-CELL grant is not the owner-endowment shape and must not be fenced"
    );
    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "the delegation half must STAY in the covered set — the verified kernel is what should \
         refuse an edgeless cross-cell grant"
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let pre_root = ledger.root();
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    match &outcome {
        ProducerOutcome::LeanAuthoritative { committed, .. } => assert!(
            !committed,
            "the VERIFIED kernel must REFUSE a grant whose delegator holds no edge to the cap \
             target — this is the non-amplification leg"
        ),
        other => panic!(
            "the edgeless cross-cell grant must be decided by the VERIFIED producer \
             (LeanAuthoritative), not fenced onto Rust — got {other:?}"
        ),
    }
    match &result {
        dregg_turn::TurnResult::Rejected { .. } => {}
        other => panic!("an edgeless cross-cell grant must be REJECTED, got {other:?}"),
    }
    assert_eq!(
        ledger.root(),
        pre_root,
        "a refused grant is NO state edit — no fabricated cap_root"
    );
}

/// The fence DISCRIMINATES: `Some` for the endowment shape, `None` for delegation. A predicate that
/// answered `Some` for every `GrantCapability` would take the whole effect off the verified path
/// while looking exactly like this fix.
#[test]
fn the_fence_predicate_discriminates_shape() {
    let (_ledger, door_id, player_id, endowment) = owner_endowment_fixture();
    assert_eq!(
        first_unmodelled_authority_origin_effect(&endowment),
        Some(AUTHORITY_ORIGIN_GAP),
        "cap.target == from is the owner-endowment shape"
    );

    let delegation = grant_turn(
        door_id,
        Effect::GrantCapability {
            from: door_id,
            to: player_id,
            cap: cap_over(player_id), // target != from
        },
    );
    assert_eq!(
        first_unmodelled_authority_origin_effect(&delegation),
        None,
        "cap.target != from is DELEGATION and stays on the verified path"
    );

    let unrelated = grant_turn(
        door_id,
        Effect::SetField {
            cell: door_id,
            index: 0,
            value: [0u8; 32],
        },
    );
    assert_eq!(
        first_unmodelled_authority_origin_effect(&unrelated),
        None,
        "the fence must not fire on effects it has nothing to do with"
    );
}

/// ⚑ BURN-DOWN TOOTH. The fence exists ONLY because the verified kernel refuses the owner
/// endowment. This drives the LIVE FFI and asserts that premise is STILL TRUE. When
/// `recKDelegate` gains its owner disjunct in `metatheory/Dregg2/Exec/AuthTurn.lean`, this test
/// goes RED and tells the reader to delete the fence — so the detour cannot outlive its reason.
#[test]
fn kernel_still_refuses_the_owner_endowment_burndown() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment burn-down tooth)",
    ) {
        return;
    }
    let (ledger, _door_id, _player_id, turn) = owner_endowment_fixture();

    // Rust's verdict on the SAME turn, from the same pre-state.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = ledger.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "dregg1 grants an owner endowment from ownership — if THIS flipped, the divergence moved \
         to the Rust side and this whole diagnosis needs redoing"
    );

    // The kernel's verdict, straight through the FFI (bypassing the coverage gate, which now
    // fences this shape — so the premise is measured, not inferred from the fence).
    let host = ShadowHostCtx::diag();
    let (_lean_ledger, lean_committed) =
        execute_via_lean(&turn, &ledger, &host).expect("the owner-endowment turn is marshallable");
    assert!(
        !lean_committed,
        "THE KERNEL WAS REPAIRED — `recKDelegate` now admits the owner endowment. DELETE the \
         owner-endowment fence: remove `first_unmodelled_authority_origin_effect` and its call \
         sites in `lean_shadow::forest_is_root_agreeing` / `first_root_gap_kind`, put the shape \
         back on the verified path, and delete this file. Leaving the fence in place would keep \
         the primordial mint on the unverified Rust producer for no remaining reason."
    );
}
