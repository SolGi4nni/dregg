//! Property-based tests for turn crate invariants.
//!
//! Property 1: Capability confinement -- no cell ever holds a capability it wasn't
//!   explicitly granted, and no cell's capabilities are WIDER than what the granter
//!   held. Driven through `TurnExecutor::execute` on real `Effect::GrantCapability` /
//!   `Effect::Introduce` / `Effect::RevokeCapability`; asserted against the
//!   executor's committed output, never against a harness-side model of it.
//!
//! Property 2: Balance conservation -- sum of all cell balances == initial total
//!   minus fees for successful turns. No cell has negative balance.
//!
//! Property 4: Receipt chain integrity -- monotonically increasing nonces, state hash
//!   continuity, and verify_receipt_chain passes on valid chains / fails on tampered ones.
//!
//! Property 5: Delegation snapshot correctness -- after SpawnWithDelegation + random ops
//!   + RefreshDelegation, the child's snapshot matches the parent's current c-list.

use proptest::prelude::*;

use dregg_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, EFFECT_ALL, EFFECT_GRANT_CAPABILITY,
    EFFECT_SET_FIELD, EFFECT_TRANSFER, EffectMask, Ledger, Permissions, capability::is_attenuation,
    is_facet_attenuation,
};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor, TurnReceipt, TurnResult, turn::Turn, verify::verify_receipt_chain,
};

// ============================================================================
// Helpers for generating random ledgers and operations
// ============================================================================

/// Create a cell with a specific seed (deterministic public key).
fn make_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    let token_id = [0u8; 32]; // same token domain
    Cell::with_balance(pk, token_id, balance)
}

/// Create a ledger with N cells, each having the given starting balance.
fn setup_ledger(n: u8, balance_each: i64) -> (Ledger, Vec<CellId>) {
    // signed-wells (ac01f9b7b): i64 balances
    let mut ledger = Ledger::new();
    let mut ids = Vec::new();
    for i in 0..n {
        let cell = make_cell(i, balance_each);
        let id = cell.id();
        ledger.insert_cell(cell).unwrap();
        ids.push(id);
    }
    (ledger, ids)
}

/// Operations that can be applied to a ledger to test capability confinement.
///
/// Each variant lowers to a REAL `Effect` submitted to `TurnExecutor::execute`
/// via `execute_effect`. Nothing here mutates a `Ledger`'s c-list directly.
#[derive(Clone, Debug)]
enum CapOp {
    /// Grant a capability from cell[from_idx] to cell[to_idx] targeting cell[target_idx].
    ///
    /// Lowers to `Effect::GrantCapability`, whose executor arm
    /// (`executor/apply.rs::apply_grant_capability`) gates THREE independent
    /// non-amplification axes: the `AuthRequired` lattice, the facet submask,
    /// and expiry-monotonicity. `mask` and `expires_at` exist so axes 2 and 3
    /// are actually reachable — the old model checked only axis 1.
    Grant {
        from_idx: usize,
        to_idx: usize,
        target_idx: usize,
        perm: AuthRequired,
        mask: Option<EffectMask>,
        expires_at: Option<u64>,
    },
    /// Revoke slot N from cell[cell_idx]. Lowers to `Effect::RevokeCapability`.
    Revoke { cell_idx: usize, slot: u32 },
    /// Introduce: cell[intro_idx] introduces cell[target_idx] to cell[recipient_idx].
    /// Lowers to `Effect::Introduce` (`apply.rs::apply_introduce`).
    Introduce {
        intro_idx: usize,
        recipient_idx: usize,
        target_idx: usize,
        perm: AuthRequired,
    },
}

/// Strategy for a random AuthRequired value.
///
/// `AuthRequired::None` is the TOP of the lattice (`permissions.rs:58` —
/// `(_, AuthRequired::None) => true`, i.e. every perm is narrower-or-equal to
/// it). Generating it is what makes AMPLIFICATION reachable: every bootstrap
/// cap below is deliberately granted at a NON-top perm, so a requested `None`
/// is a widening the executor must refuse.
fn arb_auth_required() -> impl Strategy<Value = AuthRequired> {
    prop_oneof![
        Just(AuthRequired::None),
        Just(AuthRequired::Signature),
        Just(AuthRequired::Proof),
        Just(AuthRequired::Either),
        Just(AuthRequired::Impossible),
    ]
}

/// Strategy for a requested facet mask. `None` decodes as `EFFECT_ALL`
/// (`apply.rs:671`), so it is a widening request against any faceted held cap.
fn arb_mask() -> impl Strategy<Value = Option<EffectMask>> {
    prop_oneof![
        Just(None),
        Just(Some(EFFECT_ALL)),
        Just(Some(EFFECT_TRANSFER)),
        Just(Some(EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY)),
        Just(Some(EFFECT_SET_FIELD)),
    ]
}

/// Strategy for a requested expiry. `None` is unbounded (⊤ on the expiry
/// lattice) and must be refused from a height-bounded held cap.
fn arb_expiry() -> impl Strategy<Value = Option<u64>> {
    prop_oneof![
        Just(None),
        Just(Some(10u64)),
        Just(Some(500)),
        Just(Some(5000))
    ]
}

/// Strategy for a random `Grant` op.
fn arb_grant_op(n_cells: usize) -> impl Strategy<Value = CapOp> {
    let n = n_cells;
    (
        0..n,
        0..n,
        0..n,
        arb_auth_required(),
        arb_mask(),
        arb_expiry(),
    )
        .prop_map(|(f, t, tgt, p, m, e)| CapOp::Grant {
            from_idx: f,
            to_idx: t,
            target_idx: tgt,
            perm: p,
            mask: m,
            expires_at: e,
        })
}

/// Strategy for a random capability operation.
fn arb_cap_op(n_cells: usize) -> impl Strategy<Value = CapOp> {
    let n = n_cells;
    prop_oneof![
        3 => arb_grant_op(n),
        1 => (0..n, 0..10u32).prop_map(|(c, s)| CapOp::Revoke {
            cell_idx: c,
            slot: s
        }),
        2 => (0..n, 0..n, 0..n, arb_auth_required()).prop_map(|(i, r, t, p)| CapOp::Introduce {
            intro_idx: i,
            recipient_idx: r,
            target_idx: t,
            perm: p,
        }),
    ]
}

/// Strategy for a sequence of capability operations, guaranteed to contain at
/// least one `Grant`.
///
/// The guarantee is what keeps the NON-VACUITY FLOOR meaningful rather than
/// flaky: since the bootstrap gives every ordered cell pair a held cap, a
/// `Grant` op ALWAYS reaches the non-amplification gate and is always either
/// committed (honest) or refused (amplifying). A case of nothing but `Revoke`s
/// would exercise the tooth zero times — proptest duly generated exactly that
/// and the floor caught it.
fn arb_cap_ops(n_cells: usize, max_ops: usize) -> impl Strategy<Value = Vec<CapOp>> {
    (
        arb_grant_op(n_cells),
        proptest::collection::vec(arb_cap_op(n_cells), 0..max_ops),
    )
        .prop_map(|(first, rest)| {
            let mut ops = vec![first];
            ops.extend(rest);
            ops
        })
}

// ============================================================================
// Property 1: Capability Confinement — DRIVEN THROUGH `TurnExecutor::execute`
// ============================================================================
//
// ⚑ WHY THIS LOOKS THE WAY IT DOES (the vacuity that was here before).
//
// The previous version of this property never called `TurnExecutor`. It mutated
// the `Ledger` directly, performed the attenuation check ITSELF as a GUARD, and
// on success pushed a `GrantRecord` carrying the very permission it had just
// granted. The final assertion then asked
// `is_attenuation(&g.perm, &cap.permissions)` — comparing a permission against
// ITSELF. `is_attenuation` is reflexive (`cell/src/permissions.rs:69`,
// `(a, b) => a == b`), so `was_granted` was true BY CONSTRUCTION for all 150
// cases. It was a 40-line model testing itself: `dregg-turn` could have
// amplified every capability in the ledger and this stayed green.
//
// It was doubly vacuous. The bootstrap granted every cap at `AuthRequired::None`
// — the TOP of the lattice — so every perm the strategy could generate was an
// attenuation of it. Even a version that DID call the executor could not have
// constructed an amplifying witness from that setup.
//
// The rewrite inverts exactly one thing, and it is the whole point: the
// attenuation predicate moved out of the GUARD (where it decided what the
// harness did, then congratulated itself) and into the ASSERTION (where it
// judges what the EXECUTOR did). Every op is lowered to a real `Effect` and run
// through `TurnExecutor::execute`; grants are recorded only from `Committed`
// results carrying a matching `DerivationRecord` in the receipt. The bootstrap
// installs NON-top perms + faceted + expiry-bounded caps, so the strategy
// genuinely constructs amplifying witnesses on all three axes the executor
// gates, and the executor is required to refuse them WITH A NAMED REASON.
//
// Mutation canary (S1): deleting the axis-1 `is_attenuation` gate at
// `executor/apply.rs:655` reds this test. See `MUTATION CANARY` note below.

/// A capability install the EXECUTOR committed.
///
/// Recorded ONLY when `TurnExecutor::execute` returns `Committed` and the
/// receipt carries a matching `DerivationRecord` — never from this harness's
/// opinion about whether the grant ought to have been legitimate.
#[derive(Clone, Debug)]
struct CommittedGrant {
    to: CellId,
    target: CellId,
    /// The permission the executor is expected to have INSTALLED (not merely
    /// the one requested): compared for EXACT equality against the c-list, so
    /// the reflexive-`is_attenuation` trick that made the old version vacuous
    /// cannot reappear.
    perm: AuthRequired,
    /// Expected installed facet mask. `GrantCapability` installs faithfully
    /// (`grant_ref_provenanced`); `Introduce` installs `None` unconditionally.
    mask: Option<EffectMask>,
}

/// Is `granted` an attenuation of `held` on the expiry lattice?
///
/// Mirrors `apply.rs:687-709`: `None` held = unbounded = ⊤ (anything goes);
/// a bounded held cap admits only a bounded, no-later grant.
fn expiry_attenuates(held: Option<u64>, granted: Option<u64>) -> bool {
    match held {
        None => true,
        Some(h) => match granted {
            None => false,
            Some(g) => g <= h,
        },
    }
}

/// Build a single-effect turn targeting `agent` and run it through the real
/// executor. `agent` is the action target, so the `from != action_target`
/// cross-cell `Delegate` check is not the subject here — the non-amplification
/// gate is.
///
/// The turn is chained on the agent's CURRENT head, read back from the executor
/// (`get_last_receipt_hash`) rather than tracked here: the executor enforces
/// per-agent receipt-chain continuity (`TurnError::ReceiptChainMismatch`), and
/// an unchained turn is refused before the capability gate is ever consulted.
/// Modelling the head in the harness would be the same mistake this rewrite
/// exists to undo.
fn execute_effect(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    effect: Effect,
) -> TurnResult {
    let nonce = ledger.get(&agent).unwrap().state.nonce();
    let previous_receipt_hash = executor.get_last_receipt_hash(&agent);
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
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
    };
    executor.execute(&turn, ledger)
}

/// Bootstrap the cap graph: every cell holds a cap to every other cell at a
/// deliberately NON-top perm, with a facet mask and expiry on some edges.
///
/// This is the genesis authority the whole property is relative to. It is
/// installed directly (there is no earlier turn to grant it) and recorded as
/// the authorized origin of each edge.
fn bootstrap_cap_graph(ledger: &mut Ledger, ids: &[CellId]) -> Vec<CommittedGrant> {
    // NON-top perms only: `AuthRequired::None` would make every requested perm
    // an attenuation and disarm axis 1 (the old bug).
    const BOOT_PERMS: [AuthRequired; 3] = [
        AuthRequired::Either,
        AuthRequired::Signature,
        AuthRequired::Proof,
    ];
    let mut origins = Vec::new();
    for (i, holder) in ids.iter().enumerate() {
        for (j, target) in ids.iter().enumerate() {
            if i == j {
                continue;
            }
            let perm = BOOT_PERMS[(i + j) % 3].clone();
            // Facet + expiry bounds on a subset of edges so axes 2 and 3 have
            // a real ⊤-below held value to be widened against.
            let mask = if (i + j) % 2 == 0 {
                Some(EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY)
            } else {
                None
            };
            let expires_at = if (i + j) % 3 == 0 { Some(1000) } else { None };
            let cell = ledger.get_mut(holder).unwrap();
            cell.capabilities
                .grant_provenanced(
                    *target,
                    perm.clone(),
                    None,
                    expires_at,
                    mask,
                    None,
                    dregg_cell::derivation::mint_provenance(),
                    [0u8; 32],
                )
                .expect("bootstrap grant must not overflow slots");
            origins.push(CommittedGrant {
                to: *holder,
                target: *target,
                perm,
                mask,
            });
        }
    }
    origins
}

/// Assert the standing confinement invariant against the EXECUTOR'S ledger:
/// every capability any cell holds traces to genesis authority or to a grant
/// the executor actually committed, with EXACT field equality.
///
/// Exact equality (not `is_attenuation`) is deliberate. It additionally gates
/// install-time widening — the B2 laxity hole `apply.rs:713-720` records, where
/// the old install path silently widened every grant to
/// `allowed_effects: None, expires_at: None` even when the wire grant was
/// properly attenuated.
fn assert_confinement_invariant(
    ledger: &Ledger,
    ids: &[CellId],
    committed: &[CommittedGrant],
) -> Result<(), TestCaseError> {
    for id in ids {
        let cell = ledger.get(id).unwrap();
        for cap in cell.capabilities.iter() {
            let traced = committed.iter().any(|g| {
                g.to == *id
                    && g.target == cap.target
                    && g.perm == cap.permissions
                    && g.mask == cap.allowed_effects
            });
            prop_assert!(
                traced,
                "CONFINEMENT VIOLATED: cell {:?} holds a capability to {:?} with perm {:?} / mask \
                 {:?} that the executor never committed a matching grant for (a cap from nowhere, \
                 or widened at install)",
                id,
                cap.target,
                cap.permissions,
                cap.allowed_effects
            );
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    /// ⚑ THE HEADLINE INVARIANT, gated against the real accept path.
    ///
    /// Every op is lowered to a real `Effect` and driven through
    /// `TurnExecutor::execute`. For each op the harness:
    ///
    ///  1. OBSERVES what the granter holds (`lookup_by_target` — the same entry
    ///     `apply_grant_capability` consults), before executing;
    ///  2. runs the turn through the executor;
    ///  3. on `Committed`, asserts the grant was an attenuation on every axis
    ///     the executor claims to gate — THE TOOTH. This is the assertion a
    ///     capability-amplification bug fails;
    ///  4. on `Rejected`, asserts the honest pole (an attenuating grant must
    ///     NOT be refused — else the tooth is vacuous) and the TYPED reason,
    ///     matched to the axis that should have fired. Never `Err(_)`.
    #[test]
    fn proptest_capability_confinement_holds(ops in arb_cap_ops(5, 50)) {
        let (mut ledger, ids) = setup_ledger(5, 1000);

        // Permissions wide open: this property is about CAPABILITY confinement,
        // so the cell-permission auth layer must not mask the cap gate. Any
        // reject observed below is therefore attributable to the cap gate.
        for id in &ids {
            ledger.get_mut(id).unwrap().permissions = Permissions {
                send: AuthRequired::None,
                receive: AuthRequired::None,
                set_state: AuthRequired::None,
                set_permissions: AuthRequired::None,
                set_verification_key: AuthRequired::None,
                increment_nonce: AuthRequired::None,
                delegate: AuthRequired::None,
                access: AuthRequired::None,
            };
        }

        let mut committed: Vec<CommittedGrant> = bootstrap_cap_graph(&mut ledger, &ids);
        let executor = TurnExecutor::new(ComputronCosts::zero());

        // NON-VACUITY LEDGER (S1): the tooth "committed => attenuating" holds
        // trivially if the executor never commits anything. Count what actually
        // landed and require both poles to be exercised.
        let mut honest_grants_committed = 0usize;
        let mut amplifying_grants_refused = 0usize;

        for op in &ops {
            match op {
                CapOp::Grant { from_idx, to_idx, target_idx, perm, mask, expires_at } => {
                    let from_id = ids[*from_idx];
                    let to_id = ids[*to_idx];
                    let target_id = ids[*target_idx];

                    // (1) OBSERVE the held cap the executor will consult.
                    let held = ledger
                        .get(&from_id)
                        .unwrap()
                        .capabilities
                        .lookup_by_target(&target_id)
                        .cloned();

                    let cap = CapabilityRef {
                        target: target_id,
                        slot: held.as_ref().map(|h| h.slot).unwrap_or(0),
                        permissions: perm.clone(),
                        breadstuff: None,
                        expires_at: *expires_at,
                        allowed_effects: *mask,
                        stored_epoch: None,
                        provenance: held
                            .as_ref()
                            .map(|h| h.provenance)
                            .unwrap_or([0u8; 32]),
                    };

                    // The executor's own rules, read off `apply_grant_capability`.
                    // A cell implicitly holds ⊤ over ITSELF (`apply.rs:632`), so a
                    // self-targeted grant is authorized by the signed action.
                    let self_grant = target_id == from_id;
                    let perm_ok = self_grant
                        || held.as_ref().is_some_and(|h| is_attenuation(&h.permissions, perm));
                    let mask_ok = self_grant
                        || held.as_ref().is_some_and(|h| {
                            is_facet_attenuation(
                                h.allowed_effects.unwrap_or(EFFECT_ALL),
                                mask.unwrap_or(EFFECT_ALL),
                            )
                        });
                    let expiry_ok = self_grant
                        || held.as_ref().is_some_and(|h| expiry_attenuates(h.expires_at, *expires_at));
                    let should_commit =
                        (self_grant || held.is_some()) && perm_ok && mask_ok && expiry_ok;

                    // (2) DRIVE THE REAL EXECUTOR.
                    let result = execute_effect(
                        &executor,
                        &mut ledger,
                        from_id,
                        Effect::GrantCapability { from: from_id, to: to_id, cap: cap.clone() },
                    );

                    match result {
                        TurnResult::Committed { receipt, .. } => {
                            // (3) ⚑ THE TOOTH. The executor committed a grant; it
                            // MUST have been an attenuation of what the granter
                            // held, on every axis. `should_commit` is computed from
                            // the OBSERVED held cap, independently of the executor.
                            prop_assert!(
                                perm_ok,
                                "CAPABILITY AMPLIFICATION: executor COMMITTED a grant of perm {:?} \
                                 from {:?} which holds only {:?} over target {:?} — axis 1 \
                                 (AuthRequired lattice, apply.rs:655) did not fire",
                                perm, from_id, held.as_ref().map(|h| &h.permissions), target_id
                            );
                            prop_assert!(
                                mask_ok,
                                "FACET AMPLIFICATION: executor COMMITTED a grant of mask {:?} from \
                                 {:?} which holds only mask {:?} over target {:?} — axis 2 (facet \
                                 submask, apply.rs:672) did not fire",
                                mask, from_id, held.as_ref().map(|h| h.allowed_effects), target_id
                            );
                            prop_assert!(
                                expiry_ok,
                                "EXPIRY AMPLIFICATION: executor COMMITTED a grant expiring {:?} \
                                 from {:?} which holds a cap expiring {:?} over target {:?} — axis \
                                 3 (expiry-monotone, apply.rs:687) did not fire",
                                expires_at, from_id, held.as_ref().map(|h| h.expires_at), target_id
                            );
                            prop_assert!(
                                should_commit,
                                "executor COMMITTED a grant it holds no authority for at all \
                                 (from {:?} holds nothing over target {:?})",
                                from_id, target_id
                            );

                            // The receipt must WITNESS the grant: record it only
                            // on the executor's own derivation edge.
                            let has_record = receipt.derivation_records.iter().any(|r| {
                                r.target_cell == to_id
                                    && r.edge.source_cell == from_id
                                    && r.edge.derivation_type == dregg_cell::DerivationType::Grant
                            });
                            prop_assert!(
                                has_record,
                                "executor committed a GrantCapability with no matching \
                                 DerivationRecord in the receipt (to={:?}, from={:?})",
                                to_id, from_id
                            );

                            committed.push(CommittedGrant {
                                to: to_id,
                                target: target_id,
                                perm: perm.clone(),
                                mask: *mask,
                            });
                            honest_grants_committed += 1;
                        }
                        TurnResult::Rejected { ref reason, .. } => {
                            // (4) THE HONEST POLE. If this grant was a genuine
                            // attenuation the executor must NOT have refused it —
                            // otherwise the tooth above is satisfied by a gate that
                            // simply rejects everything.
                            prop_assert!(
                                !should_commit,
                                "HONEST POLE BROKEN: executor REJECTED a properly attenuating \
                                 grant (perm {:?} / mask {:?} / expiry {:?} from a cap {:?}) with \
                                 {:?} — the confinement tooth is vacuous if honest grants do not \
                                 commit",
                                perm, mask, expires_at, held, reason
                            );
                            // TYPED reject, matched to the axis. Not `Err(_)`.
                            if held.is_none() && !self_grant {
                                prop_assert!(
                                    matches!(reason, TurnError::CapabilityNotHeld { .. }),
                                    "wrong refusal for an unheld target: expected \
                                     CapabilityNotHeld, got {:?}",
                                    reason
                                );
                            } else {
                                prop_assert!(
                                    matches!(reason, TurnError::DelegationDenied { .. }),
                                    "wrong refusal for an amplifying grant: expected \
                                     DelegationDenied, got {:?}",
                                    reason
                                );
                                amplifying_grants_refused += 1;
                            }
                        }
                        other => prop_assert!(
                            false,
                            "GrantCapability turn neither committed nor rejected: {:?}",
                            other
                        ),
                    }
                }

                CapOp::Revoke { cell_idx, slot } => {
                    let cell_id = ids[*cell_idx];
                    let held_slot = ledger
                        .get(&cell_id)
                        .unwrap()
                        .capabilities
                        .iter()
                        .any(|c| c.slot == *slot);
                    let result = execute_effect(
                        &executor,
                        &mut ledger,
                        cell_id,
                        Effect::RevokeCapability { cell: cell_id, slot: *slot },
                    );
                    if result.is_committed() && held_slot {
                        // A revoke REMOVES authority; confinement can only shrink.
                        prop_assert!(
                            !ledger
                                .get(&cell_id)
                                .unwrap()
                                .capabilities
                                .iter()
                                .any(|c| c.slot == *slot),
                            "executor committed a RevokeCapability but slot {} is still live in \
                             {:?}'s c-list",
                            slot, cell_id
                        );
                    }
                }

                CapOp::Introduce { intro_idx, recipient_idx, target_idx, perm } => {
                    let intro_id = ids[*intro_idx];
                    let recipient_id = ids[*recipient_idx];
                    let target_id = ids[*target_idx];

                    let intro_caps = &ledger.get(&intro_id).unwrap().capabilities;
                    let has_recipient = intro_caps.has_access(&recipient_id);
                    let held = intro_caps.lookup_by_target(&target_id).cloned();
                    // Mirrors `apply_introduce` (apply.rs:2263-2340): access to the
                    // recipient, a live (unexpired) held cap over the target, and
                    // perm attenuation.
                    //
                    // ⚠ NAMED SEAM — FACET AMPLIFICATION VIA `Introduce` (confirmed
                    // live at HEAD, not a hypothetical). `apply_introduce` gates the
                    // AuthRequired axis ONLY: it never reads `held_cap.allowed_effects`
                    // and installs the recipient's cap with `allowed_effects: None`
                    // (= `EFFECT_ALL`) at apply.rs:2374. So an introducer holding a
                    // TRANSFER-only facet over `target` can hand a recipient an
                    // ALL-EFFECTS cap over it — exactly the axis-2 hole
                    // `apply_grant_capability` closed for `GrantCapability`
                    // (apply.rs:665-680, "a holder of a TRANSFER-only facet could grant
                    // an all-effects cap"), still open on this path. Reproduced: held
                    // mask `Some(EFFECT_TRANSFER)` → committed → recipient holds
                    // mask `None`.
                    //
                    // This tooth therefore asserts the perm axis only. Closing the
                    // facet axis is an executor-semantics change (it must land with
                    // the Phase-B2 circuit + the Lean differential, not as a drive-by
                    // in a test lane) and is reported as its own lane rather than
                    // silently encoded here as if intended.
                    let held_live = held
                        .as_ref()
                        .is_some_and(|h| h.expires_at.is_none_or(|e| executor.block_height <= e));
                    let perm_ok = held
                        .as_ref()
                        .is_some_and(|h| is_attenuation(&h.permissions, perm));
                    let should_commit = has_recipient && held.is_some() && held_live && perm_ok;

                    let result = execute_effect(
                        &executor,
                        &mut ledger,
                        intro_id,
                        Effect::Introduce {
                            introducer: intro_id,
                            recipient: recipient_id,
                            target: target_id,
                            permissions: perm.clone(),
                        },
                    );

                    match result {
                        TurnResult::Committed { .. } => {
                            // ⚑ THE TOOTH, introduce edge.
                            prop_assert!(
                                perm_ok,
                                "CAPABILITY AMPLIFICATION via Introduce: executor COMMITTED an \
                                 introduction granting {:?} over {:?} while the introducer {:?} \
                                 holds only {:?}",
                                perm, target_id, intro_id, held.as_ref().map(|h| &h.permissions)
                            );
                            prop_assert!(
                                should_commit,
                                "executor COMMITTED an introduction it had no authority for \
                                 (has_recipient={}, held={:?})",
                                has_recipient, held
                            );
                            committed.push(CommittedGrant {
                                to: recipient_id,
                                target: target_id,
                                perm: perm.clone(),
                                // `apply_introduce` installs an UNFACETED cap.
                                mask: None,
                            });
                        }
                        TurnResult::Rejected { ref reason, .. } => {
                            prop_assert!(
                                !should_commit,
                                "HONEST POLE BROKEN: executor REJECTED a legitimate introduction \
                                 ({:?} over {:?} from held {:?}) with {:?}",
                                perm, target_id, held, reason
                            );
                            prop_assert!(
                                matches!(reason, TurnError::IntroductionDenied { .. }),
                                "wrong refusal for a denied introduction: expected \
                                 IntroductionDenied, got {:?}",
                                reason
                            );
                        }
                        other => prop_assert!(
                            false,
                            "Introduce turn neither committed nor rejected: {:?}",
                            other
                        ),
                    }
                }
            }
        }

        // The standing invariant, against the executor's own ledger.
        assert_confinement_invariant(&ledger, &ids, &committed)?;

        // ⚑ NON-VACUITY FLOOR. A run in which the executor committed nothing
        // (or refused nothing) would satisfy every assertion above while
        // proving nothing. Require the property to have actually been at risk.
        prop_assert!(
            honest_grants_committed + amplifying_grants_refused > 0,
            "vacuous case: the executor neither committed an honest grant nor refused an \
             amplifying one across {} ops — the tooth was never exercised",
            ops.len()
        );
    }
}

/// ⚑ S1 DETERMINISTIC CANARY for the property above.
///
/// The proptest is the general gate; this is the specific forged witness, so a
/// regression names itself without waiting for a shrink. It re-asserts the
/// honest pole FIRST — without that, a gate that refuses everything would pass
/// the amplification leg and the canary would be vacuous.
#[test]
fn executor_refuses_a_specific_amplifying_grant_and_admits_its_honest_twin() {
    let (mut ledger, ids) = setup_ledger(3, 1_000);
    for id in &ids {
        ledger.get_mut(id).unwrap().permissions.delegate = AuthRequired::None;
    }
    let (granter, holder, target) = (ids[0], ids[1], ids[2]);
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Genesis: `granter` holds a SIGNATURE-gated cap over `target`.
    let held_slot = ledger
        .get_mut(&granter)
        .unwrap()
        .capabilities
        .grant(target, AuthRequired::Signature)
        .expect("bootstrap grant");
    let provenance = ledger
        .get(&granter)
        .unwrap()
        .capabilities
        .lookup(held_slot)
        .unwrap()
        .provenance;

    let cap_at = |permissions: AuthRequired| CapabilityRef {
        target,
        slot: held_slot,
        permissions,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance,
    };

    // HONEST POLE FIRST: Signature ⊑ Signature must COMMIT. Without this leg the
    // refusal below proves nothing (a gate that rejects everything would pass).
    let honest = execute_effect(
        &executor,
        &mut ledger,
        granter,
        Effect::GrantCapability {
            from: granter,
            to: holder,
            cap: cap_at(AuthRequired::Signature),
        },
    );
    assert!(
        honest.is_committed(),
        "honest witness must be accepted — else the canary is vacuous: {honest:?}"
    );
    assert_eq!(
        ledger
            .get(&holder)
            .unwrap()
            .capabilities
            .lookup_by_target(&target)
            .expect("holder must hold the honestly granted cap")
            .permissions,
        AuthRequired::Signature,
        "the executor must install the granted perm FAITHFULLY"
    );

    // THE FORGERY: `None` is ⊤ on the lattice (`permissions.rs:58`). Granting it
    // from a Signature-gated cap is a strict widening — the holder could then
    // exercise the cap with no signature at all.
    let forged = execute_effect(
        &executor,
        &mut ledger,
        granter,
        Effect::GrantCapability {
            from: granter,
            to: holder,
            cap: cap_at(AuthRequired::None),
        },
    );

    // Assert WHY it refused — a typed variant, not any `Err`/panic.
    match forged {
        TurnResult::Rejected { ref reason, .. } => assert!(
            matches!(
                reason,
                TurnError::DelegationDenied { parent, child_target }
                    if *parent == granter && *child_target == holder
            ),
            "expected DelegationDenied naming the amplifying grant, got {reason:?}"
        ),
        other => panic!(
            "CAPABILITY AMPLIFICATION IS OPEN: granting AuthRequired::None from a \
             Signature-gated cap was not refused: {other:?}"
        ),
    }

    // And the forgery left NO trace: the holder still holds only the honest cap.
    let holder_caps: Vec<AuthRequired> = ledger
        .get(&holder)
        .unwrap()
        .capabilities
        .iter()
        .filter(|c| c.target == target)
        .map(|c| c.permissions.clone())
        .collect();
    assert_eq!(
        holder_caps,
        vec![AuthRequired::Signature],
        "the refused grant must not have been installed"
    );
}

// ============================================================================
// Property 2: Balance Conservation
// ============================================================================

/// Operations for balance testing via the executor.
#[derive(Clone, Debug)]
enum BalanceOp {
    /// Transfer amount from cell[from_idx] to cell[to_idx].
    Transfer {
        from_idx: usize,
        to_idx: usize,
        amount: u64,
    },
}

fn arb_balance_op(n_cells: usize) -> impl Strategy<Value = BalanceOp> {
    (0..n_cells, 0..n_cells, 1u64..500u64).prop_map(|(f, t, a)| BalanceOp::Transfer {
        from_idx: f,
        to_idx: t,
        amount: a,
    })
}

fn arb_balance_ops(n_cells: usize, max_ops: usize) -> impl Strategy<Value = Vec<BalanceOp>> {
    proptest::collection::vec(arb_balance_op(n_cells), 1..=max_ops)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    #[test]
    fn proptest_balance_conservation_holds(ops in arb_balance_ops(4, 30)) {
        let initial_balance = 10_000u64;
        let n_cells = 4u8;
        // signed-wells (ac01f9b7b): cell balances are i64; these are ordinary
        // (non-negative) cells, so the conservation arithmetic stays in u64
        // and the i64 balances cross back via checked conversions below.
        let (mut ledger, ids) = setup_ledger(n_cells, initial_balance as i64);
        let initial_total = initial_balance * (n_cells as u64);

        // Give each cell capabilities to all others (for transfers) and set
        // permissions to allow sends without signature (for testing conservation).
        for i in 0..ids.len() {
            let cell = ledger.get_mut(&ids[i]).unwrap();
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
            for j in 0..ids.len() {
                if i != j {
                    cell.capabilities.grant(ids[j], AuthRequired::None);
                }
            }
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let mut total_fees = 0u64;

        for op in &ops {
            match op {
                BalanceOp::Transfer { from_idx, to_idx, amount } => {
                    let from_id = ids[*from_idx];
                    let to_id = ids[*to_idx];
                    if from_id == to_id {
                        continue; // self-transfer is a no-op
                    }

                    let nonce = ledger.get(&from_id).unwrap().state.nonce();
                    let fee = 0u64; // zero-cost for conservation testing

                    let mut forest = CallForest::new();
                    let action = Action {
                        target: from_id,
                        method: [0u8; 32],
                        args: vec![],
                        authorization: Authorization::Unchecked,
                        preconditions: Default::default(),
                        effects: vec![Effect::Transfer {
                            from: from_id,
                            to: to_id,
                            amount: *amount,
                        }],
                        may_delegate: DelegationMode::None,
                        commitment_mode: Default::default(),
                        balance_change: None,
                        witness_blobs: vec![],
                    };
                    forest.add_root(action);

                    let turn = Turn {
                        agent: from_id,
                        nonce,
                        call_forest: forest,
                        fee,
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
                    };

                    let result = executor.execute(&turn, &mut ledger);
                    if result.is_committed() {
                        total_fees += fee;
                    }
                    // If rejected (e.g. insufficient balance), that's fine.
                }
            }
        }

        // INVARIANT: sum of all balances == initial_total - total_fees
        let current_total: u64 = ids
            .iter()
            .map(|id| u64::try_from(ledger.get(id).unwrap().state.balance()).unwrap())
            .sum();
        prop_assert_eq!(current_total, initial_total - total_fees,
            "Balance conservation violated: initial={}, fees={}, current={}",
            initial_total, total_fees, current_total);

        // INVARIANT: no cell has "negative" balance (u64 can't be negative, but
        // we verify no underflow panic occurred by reaching this point).
        for id in &ids {
            // signed-wells (ac01f9b7b): balance() is i64; ordinary cell → u64.
            let balance = u64::try_from(ledger.get(id).unwrap().state.balance()).unwrap();
            // This is trivially true for u64, but documents the invariant.
            prop_assert!(balance <= initial_total,
                "Cell balance {} exceeds initial total {}", balance, initial_total);
        }
    }
}

// ============================================================================
// Property 4: Receipt Chain Integrity
// ============================================================================

/// Build a valid receipt chain of length N for a given agent in a ledger.
fn build_receipt_chain(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    n: usize,
) -> Vec<TurnReceipt> {
    let mut chain = Vec::new();

    for i in 0..n {
        let nonce = ledger.get(&agent).unwrap().state.nonce();
        let fee = 0u64;

        // Simple no-op action (targets self, no effects that need auth).
        let mut forest = CallForest::new();
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        forest.add_root(action);

        let previous_receipt_hash = chain.last().map(|r: &TurnReceipt| r.receipt_hash());

        let turn = Turn {
            agent,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
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
        };

        let result = executor.execute(&turn, ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                chain.push(receipt);
            }
            other => {
                panic!("Expected committed turn at index {i}, got: {other:?}");
            }
        }
    }

    chain
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn proptest_receipt_chain_integrity(chain_len in 2usize..15) {
        let (mut ledger, ids) = setup_ledger(1, 100_000);
        let agent = ids[0];

        // Set permissions to allow no-auth actions.
        {
            let cell = ledger.get_mut(&agent).unwrap();
            cell.permissions.access = AuthRequired::None;
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_receipt_chain(&executor, &mut ledger, agent, chain_len);

        // INVARIANT: verify_receipt_chain passes on the full chain.
        prop_assert!(verify_receipt_chain(&chain).is_ok(),
            "Valid chain should pass verification");

        // INVARIANT: Monotonically increasing nonces (implied by executor nonce check).
        // We verify via the state hash chain instead -- each receipt links to previous.

        // INVARIANT: Each receipt's pre_state_hash == previous receipt's post_state_hash.
        for i in 1..chain.len() {
            prop_assert_eq!(chain[i].pre_state_hash, chain[i - 1].post_state_hash,
                "State chain broken at index {}", i);
        }

        // INVARIANT: Removing any receipt from the middle breaks verification.
        if chain.len() >= 3 {
            for remove_idx in 1..chain.len() - 1 {
                let mut broken_chain = chain.clone();
                broken_chain.remove(remove_idx);
                prop_assert!(verify_receipt_chain(&broken_chain).is_err(),
                    "Removing receipt at index {} should break verification", remove_idx);
            }
        }
    }

    /// Swapping two adjacent receipts should also break the chain.
    #[test]
    fn proptest_receipt_chain_swap_breaks(chain_len in 3usize..10) {
        let (mut ledger, ids) = setup_ledger(1, 100_000);
        let agent = ids[0];
        {
            let cell = ledger.get_mut(&agent).unwrap();
            cell.permissions.access = AuthRequired::None;
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_receipt_chain(&executor, &mut ledger, agent, chain_len);

        // Swap receipts at positions 1 and 2.
        let mut swapped = chain.clone();
        swapped.swap(1, 2);
        prop_assert!(verify_receipt_chain(&swapped).is_err(),
            "Swapping receipts should break verification");
    }
}

// ============================================================================
// Property 5: Delegation Snapshot Correctness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn proptest_delegation_snapshot_correctness(
        extra_caps in 0u8..5,
        revoke_before_refresh in proptest::bool::ANY,
    ) {
        let (mut ledger, ids) = setup_ledger(3, 10_000);
        let parent_id = ids[0];
        let target_a = ids[1];
        let target_b = ids[2];

        // Set all permissions to None for easy testing.
        for id in &ids {
            let cell = ledger.get_mut(id).unwrap();
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
        }

        // Give parent capabilities.
        {
            let parent = ledger.get_mut(&parent_id).unwrap();
            parent.capabilities.grant(target_a, AuthRequired::Signature);
            parent.capabilities.grant(target_b, AuthRequired::None);
        }

        // Spawn a child with delegation from the parent.
        let child_pk = [42u8; 32];
        let child_token = [0u8; 32];
        let child_id = CellId::derive_raw(&child_pk, &child_token);

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // SpawnWithDelegation turn.
        let spawn_receipt_hash = {
            let nonce = ledger.get(&parent_id).unwrap().state.nonce();
            let mut forest = CallForest::new();
            let action = Action {
                target: parent_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![Effect::SpawnWithDelegation {
                    child_public_key: child_pk,
                    child_token_id: child_token,
                    max_staleness: 3600,
                }],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
                witness_blobs: vec![],
            };
            forest.add_root(action);

            let turn = Turn {
                agent: parent_id,
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
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "SpawnWithDelegation should succeed");
            result.unwrap_committed().1.receipt_hash()
        };

        // Verify initial delegation snapshot matches parent's c-list at spawn time.
        {
            let child = ledger.get(&child_id).unwrap();
            let delegation = child.delegation.as_ref().unwrap();
            // At spawn time parent had 2 capabilities (target_a, target_b).
            prop_assert_eq!(delegation.snapshot.len(), 2,
                "Initial snapshot should have 2 capabilities");
        }

        // Modify parent's capabilities (add more).
        for i in 0..extra_caps {
            let new_target_cell = make_cell(100 + i, 1000);
            let new_target_id = new_target_cell.id();
            ledger.insert_cell(new_target_cell).unwrap();
            // Set permissions to None on new cell.
            ledger.get_mut(&new_target_id).unwrap().permissions = Permissions {
                send: AuthRequired::None,
                receive: AuthRequired::None,
                set_state: AuthRequired::None,
                set_permissions: AuthRequired::None,
                set_verification_key: AuthRequired::None,
                increment_nonce: AuthRequired::None,
                delegate: AuthRequired::None,
                access: AuthRequired::None,
            };
            let parent = ledger.get_mut(&parent_id).unwrap();
            parent.capabilities.grant(new_target_id, AuthRequired::None);
        }

        if revoke_before_refresh {
            // Revoke the delegation from the parent's side.
            let nonce = ledger.get(&parent_id).unwrap().state.nonce();
            let mut forest = CallForest::new();
            let action = Action {
                target: parent_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![Effect::RevokeDelegation { child: child_id }],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
                witness_blobs: vec![],
            };
            forest.add_root(action);

            let turn = Turn {
                agent: parent_id,
                nonce,
                call_forest: forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: Some(spawn_receipt_hash),
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
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "RevokeDelegation should succeed: {:?}", result);

            // INVARIANT: After RevokeDelegation, child's delegation is None.
            let child = ledger.get(&child_id).unwrap();
            prop_assert!(child.delegation.is_none(),
                "After revocation, child delegation should be None");
        } else {
            // RefreshDelegation: child picks up parent's current c-list.
            // Need to give child permission for access.
            {
                let child_cell = ledger.get_mut(&child_id).unwrap();
                child_cell.permissions = Permissions {
                    send: AuthRequired::None,
                    receive: AuthRequired::None,
                    set_state: AuthRequired::None,
                    set_permissions: AuthRequired::None,
                    set_verification_key: AuthRequired::None,
                    increment_nonce: AuthRequired::None,
                    delegate: AuthRequired::None,
                    access: AuthRequired::None,
                };
            }

            let nonce = ledger.get(&child_id).unwrap().state.nonce();
            // The genuine refreshed snapshot: the commitment over the parent's
            // live capabilities (what the executor re-arms from); the effect
            // declares it and the executor refuses a mismatch.
            let refresh_snapshot = {
                let parent = ledger.get(&parent_id).unwrap();
                let snap: Vec<CapabilityRef> = parent.capabilities.iter().cloned().collect();
                let bytes = postcard::to_allocvec(&snap).unwrap_or_default();
                dregg_cell::DelegatedRef::compute_clist_commitment(&bytes)
            };
            let mut forest = CallForest::new();
            let action = Action {
                target: child_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![Effect::RefreshDelegation {
                    child: child_id,
                    snapshot: refresh_snapshot,
                }],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
                witness_blobs: vec![],
            };
            forest.add_root(action);

            let turn = Turn {
                agent: child_id,
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
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "RefreshDelegation should succeed");

            // INVARIANT: After refresh, child's snapshot matches parent's CURRENT c-list.
            let parent_caps: Vec<CapabilityRef> = ledger
                .get(&parent_id)
                .unwrap()
                .capabilities
                .iter()
                .cloned()
                .collect();
            let child = ledger.get(&child_id).unwrap();
            let delegation = child.delegation.as_ref().unwrap();

            prop_assert_eq!(delegation.snapshot.len(), parent_caps.len(),
                "After refresh, snapshot length should match parent's c-list length");

            // Each capability in the snapshot should match what the parent holds.
            for (snap_cap, parent_cap) in delegation.snapshot.iter().zip(parent_caps.iter()) {
                prop_assert_eq!(snap_cap.target, parent_cap.target,
                    "Snapshot target mismatch");
                prop_assert_eq!(&snap_cap.permissions, &parent_cap.permissions,
                    "Snapshot permissions mismatch");
            }

            // INVARIANT: Child can never exercise capabilities wider than parent holds.
            for snap_cap in &delegation.snapshot {
                let parent_held = ledger
                    .get(&parent_id)
                    .unwrap()
                    .capabilities
                    .lookup_by_target(&snap_cap.target);
                prop_assert!(parent_held.is_some(),
                    "Child has capability to {:?} which parent doesn't hold", snap_cap.target);
                let parent_cap = parent_held.unwrap();
                prop_assert!(is_attenuation(&parent_cap.permissions, &snap_cap.permissions),
                    "Child capability {:?} is wider than parent's {:?}",
                    snap_cap.permissions, parent_cap.permissions);
            }
        }
    }
}
