//! ⚑ THE OWNER-ENDOWMENT CUTOVER — the `GrantCapability` shape the verified kernel used to refuse.
//!
//! ## The turn
//!
//! `Effect::GrantCapability { from: A, to: B, cap: CapabilityRef { target: A, .. } }` where `A`'s
//! c-list is EMPTY — which is every cell's FIRST grant, because `Cell::new`/`Cell::with_balance`
//! mint a cell with no capabilities.
//!
//! * **dregg1 COMMITS.** `apply_grant_capability` (`turn/src/executor/apply.rs:760`) short-circuits
//!   a self-grant: `if cap.target == *from { /* skip c-list lookup */ }`. A cell is the ORIGIN of
//!   authority over itself.
//! * **The verified kernel COMMITS TOO, as of 2026-07-31.** `recKDelegate`
//!   (`metatheory/Dregg2/Exec/AuthTurn.lean`) gates on
//!   `t = delegator ∨ (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true`. The left
//!   disjunct is the base case; abstractly it is `Spec.Origin` (`Dregg2/Spec/Authority.lean`), the
//!   self-reference arm of the capability dynamics, confined by `Origin.over_self` to caps
//!   targeting the originator.
//!
//! ## What this file replaced
//!
//! `producer_owner_endowment_fence.rs`. Until the kernel carried the disjunct, `caps = fun _ => []`
//! was a FIXPOINT of the modelled authority calculus — no rule created a first edge — so the
//! verified gate refused the first grant every cell ever makes, and the shape was FENCED out of the
//! swap-safe covered set (`lean_shadow::first_unmodelled_authority_origin_effect`, reason
//! `AUTHORITY_ORIGIN_GAP`). That fence, its predicate and its named reason are **DELETED**: a fence
//! whose premise has become false is a permanent detour, not a safeguard.
//!
//! ## What this file pins — both poles, by VARIANT, over the LIVE FFI
//!
//! * `owner_endowment_is_verified_and_commits` — the endowment is back INSIDE the covered set
//!   (`forest_is_root_agreeing`), is decided by the VERIFIED kernel (`LeanAuthoritative`, asserted
//!   by variant, never `is_ok()`), commits, and the cap actually lands.
//! * `cross_cell_grant_without_a_held_edge_is_still_the_verified_kernels_refusal` — ⚑ **the
//!   load-bearing pole.** The amplification-relevant half — a cross-cell grant where the granter
//!   holds NO edge to the target — is still `LeanAuthoritative { committed: false }`. A cutover
//!   that admitted the owner AND the forger would be worse than no cutover.
//! * `ffi_admits_the_owner_and_refuses_the_forger_by_variant` — both poles in ONE test over ONE
//!   pre-state, driving `execute_via_lean` (the real kernel, not the coverage gate): same cap
//!   target, same recipient shape, same empty c-lists, **only `from` varies**. This is the Rust
//!   witness of `owner_admitted_forger_refused_same_target` in `AuthTurn.lean`.
//! * `endowment_is_no_longer_fenced_out_of_the_covered_set` — the flipped burn-down. The old file's
//!   tooth asserted the kernel STILL refuses; this asserts it no longer does, so a silent
//!   regression of the kernel gate (or a re-introduced fence) goes red here.

use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{ProducerOutcome, execute_via_lean, produce_via_lean};
use dregg_exec_lean::lean_shadow::{self, ShadowHostCtx};
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
        "PRECONDITION: a freshly minted cell holds NO capabilities — this is why the owner \
         disjunct decides every cell's FIRST grant, not a corner case"
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

/// POLE 1. The owner-endowment self-grant is INSIDE the covered set, is decided by the VERIFIED
/// kernel, commits, and the cap lands. Before the cutover this same turn produced
/// `Fallback { RootGap { kind: "GrantCapability/owner-endowment" } }`.
#[test]
fn owner_endowment_is_verified_and_commits() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment cutover: the admitted pole)",
    ) {
        return;
    }
    let (mut ledger, door_id, player_id, turn) = owner_endowment_fixture();

    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "the owner-endowment shape must be INSIDE the swap-safe covered set now that the kernel \
         models it; if this is false a fence was re-introduced somewhere"
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    // BY VARIANT — never `is_ok()`. A `Fallback` (of any reason) must not satisfy this.
    match &outcome {
        ProducerOutcome::LeanAuthoritative { committed, .. } => assert!(
            *committed,
            "the VERIFIED kernel must COMMIT a cell's endowment of a capability over ITSELF — this \
             is `recKDelegate`'s owner disjunct, abstractly `Spec.Origin`"
        ),
        other => panic!(
            "owner-endowment must be decided by the VERIFIED producer (LeanAuthoritative), not \
             fenced onto Rust — got {other:?}"
        ),
    }

    match &result {
        dregg_turn::TurnResult::Committed { .. } => {}
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            panic!("a cell endowing a capability over ITSELF must COMMIT; got {reason:?}")
        }
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

/// POLE 2 — ⚑ **THE LOAD-BEARING POLE.** The amplification-relevant half of `GrantCapability` (a
/// cross-cell grant where the granter holds no edge to the target) is still decided by the VERIFIED
/// kernel, and still REFUSED. The Lean counterpart is `recKDelegate_cross_gated` /
/// `recKDelegate_refuses_unbacked_nonowner`: off the diagonal `t = delegator` the completed gate is
/// the edge-only gate, as a function equality (`recKDelegate_cross_eq`).
#[test]
fn cross_cell_grant_without_a_held_edge_is_still_the_verified_kernels_refusal() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment cutover: the verified-refusal pole)",
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
    // DELEGATION half — the one the self disjunct provably did not touch.
    let turn = grant_turn(
        a_id,
        Effect::GrantCapability {
            from: a_id,
            to: b_id,
            cap: cap_over(c_id),
        },
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
             target — this is the non-amplification leg, and the cutover must not have widened it"
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

/// ⚑ **BOTH POLES BY VARIANT, OVER THE LIVE FFI.** One pre-state, both cells with EMPTY c-lists,
/// the SAME cap target (the door) and the SAME recipient — **only `from` varies**:
///
///   * `from = door` (the OWNER of the cap target) — the kernel ADMITS;
///   * `from = player` (a NON-owner holding nothing) — the kernel REFUSES.
///
/// This drives `execute_via_lean` directly, so it measures the KERNEL, not the coverage gate. It is
/// the Rust witness of `owner_admitted_forger_refused_same_target` in `AuthTurn.lean`. A cutover
/// that admitted the owner AND the forger would pass every other test in this file and fail here.
#[test]
fn ffi_admits_the_owner_and_refuses_the_forger_by_variant() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment cutover: both poles by variant)",
    ) {
        return;
    }
    let door = open_cell(1, 1_000_000);
    let door_id = door.id();
    let player = open_cell(2, 1_000_000);
    let player_id = player.id();
    let bystander = open_cell(3, 1_000_000);
    let bystander_id = bystander.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(door).unwrap();
    ledger.insert_cell(player).unwrap();
    ledger.insert_cell(bystander).unwrap();
    for id in [door_id, player_id, bystander_id] {
        assert!(
            ledger
                .get(&id)
                .unwrap()
                .capabilities
                .iter()
                .next()
                .is_none(),
            "PRECONDITION: every cap slot is empty, so the ONLY thing separating the two turns \
             below is who is granting"
        );
    }

    let host = ShadowHostCtx::diag();

    // OWNER: the door grants a cap over the DOOR. `cap.target == from` — admitted.
    let owner_turn = grant_turn(
        door_id,
        Effect::GrantCapability {
            from: door_id,
            to: player_id,
            cap: cap_over(door_id),
        },
    );
    let (_l, owner_committed) = execute_via_lean(&owner_turn, &ledger, &host)
        .expect("the owner-endowment turn is marshallable");

    // FORGER: the PLAYER grants a cap over the DOOR — same target, same shape, holding nothing.
    let forger_turn = grant_turn(
        player_id,
        Effect::GrantCapability {
            from: player_id,
            to: bystander_id,
            cap: cap_over(door_id),
        },
    );
    let (_l2, forger_committed) =
        execute_via_lean(&forger_turn, &ledger, &host).expect("the forgery turn is marshallable");

    assert!(
        owner_committed,
        "THE OWNER POLE: a cell endowing a capability over ITSELF must be ADMITTED by the verified \
         kernel — `recKDelegate`'s `t = delegator` disjunct"
    );
    assert!(
        !forger_committed,
        "⚑ THE FORGERY POLE: a NON-owner granting the identically-shaped capability over the SAME \
         target, from the SAME empty c-list, must still be REFUSED. If this commits, the cutover \
         admitted the owner AND the forger and the owner disjunct is being read as a blanket \
         admission of the shape `grant over cell X` (`recKDelegate_cross_gated` is the Lean pole)"
    );
}

/// The flipped burn-down. The old `producer_owner_endowment_fence.rs` carried a tooth asserting the
/// kernel STILL refuses the endowment, so the fence could not outlive its reason. This is the same
/// tooth pointed the other way: the kernel now ADMITS, and the shape is no longer fenced. A silent
/// regression of the Lean gate — or a re-introduced fence — goes red here rather than quietly
/// pushing the primordial mint back onto the unverified Rust producer.
#[test]
fn endowment_is_no_longer_fenced_out_of_the_covered_set() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (owner-endowment cutover: the flipped burn-down)",
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

    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "the owner-endowment shape must be in the covered set; a fence here is the detour the \
         cutover deleted"
    );

    let host = ShadowHostCtx::diag();
    let (_lean_ledger, lean_committed) =
        execute_via_lean(&turn, &ledger, &host).expect("the owner-endowment turn is marshallable");
    assert!(
        lean_committed,
        "THE KERNEL REGRESSED — `recKDelegate` is refusing the owner endowment again. Both \
         deciders must agree on this turn: dregg1 commits it from ownership, and the verified \
         kernel's owner disjunct (`t = delegator`, abstractly `Spec.Origin`) admits it. Do NOT \
         re-fence the shape; fix the gate in `metatheory/Dregg2/Exec/AuthTurn.lean`."
    );
}
