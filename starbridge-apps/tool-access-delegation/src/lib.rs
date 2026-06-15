//! # starbridge-tool-access-delegation
//!
//! **Verifiable tool / MCP-access delegation** — the object-capability model serving AI delegation.
//!
//! An AI agent (the GRANTOR) hands another agent (the WORKER) a NARROWLY-ATTENUATED, RATE-LIMITED,
//! TIME-BOUNDED, REVOCABLE capability to invoke a tool / MCP on its behalf. The grantor does NOT hand
//! over its keys; it mints a *mandate cell* whose slot-caveats are checked BY THE VERIFIED EXECUTOR on
//! every tool invocation, so the worker can NEVER invoke the tool beyond the granted rate, scope, or
//! deadline — and the grant can be revoked.
//!
//! This crate is the Rust mirror of the verified Lean
//! `metatheory/Dregg2/Apps/ToolAccessDelegation.lean`. The Lean side proves, against
//! `Dregg2.Apps.VerificationToolkit.app_commit_iff_admit`, that the production caveat-gated executor
//! (`execFullA (.setFieldA worker cell "calls_made" (c+1))`, definitionally `stateStepGuarded`) COMMITS
//! a tool invocation IFF the delegated policy admits it — and REJECTS (`= none`) any over-rate /
//! past-deadline / out-of-scope invocation (the teeth `tool_invocation_*_rejected`).
//!
//! ## The two enforcement surfaces (both REAL, both in the verified kernel)
//!
//!   1. **Capability attenuation** — WHO may delegate, with WHICH rights — is the agent-mandate
//!      attenuation theory already in `intent/src/agent_mandate.rs` (`Mandate::sub_delegate` strictly
//!      narrows keep/budget/caveat; `materialize_grant = recKDelegateAtten`; `materialize_revoke`).
//!      The agent-facing biscuit credential gating the executor on the live `execFullForestG` path is
//!      `StarbridgeGated.mkAuthToken` (`metatheory/Dregg2/Exec/GatedForestCfg.lean §A2`). We REUSE
//!      those surfaces; we do not re-implement them.
//!
//!   2. **Per-invocation consumption budget** — HOW MANY times, UNTIL WHEN, on WHICH tool. THIS is what
//!      `agent_mandate.rs` does NOT enforce: the rate-limit counter, the expiry deadline, and the tool
//!      allowlist, checked on EVERY tool call as a SLOT-CAVEAT-gated `SetField`. That is THIS crate's
//!      contribution, mirroring the Lean `delegAdmit` / `mandateSpec`.
//!
//! ## The mandate cell (slot ↦ meaning, mirroring the Lean `mandateSpec` slots)
//!
//!   * `calls_made`  (the RATE COUNTER) — incremented `c → c+1` on each invocation; `Monotonic` so it
//!     can never roll back to forge head-room, and the admit-table requires `c+1 ≤ rate_limit`.
//!   * `rate_limit`  (the granted N) — `WriteOnce`: bound once by the grant turn (from zero on the
//!     factory-born cell), frozen thereafter — the ceiling is never raised.
//!   * `deadline`    (the EXPIRY) — `WriteOnce`: the grantor sets it once at grant; thereafter frozen.
//!   * `tool_id`     (the SCOPE) — `WriteOnce`: the single allowlisted tool/MCP id, bound at grant
//!     and frozen.
//!
//! ## Differential pinning
//!
//! [`deleg_admit`] is the byte-for-byte mirror of the Lean `delegAdmit`. [`deleg_corpus`] enumerates
//! the FULL `(old, new)` grid for a grant and emits the admission decision vector — the EXACT vector the
//! Lean `AppDiffPinned (mandateSpec demoGrant 50 77 5)` `#guard` pins. The test
//! `tests/lean_differential.rs` asserts the Rust corpus equals that pinned literal; drift on either side
//! fails.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CapabilityRef, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, canonical_program_vk,
    field_from_u64, hex_encode_32, symbol,
};

pub use dregg_app_framework::{FieldElement, field_from_bytes};

// =============================================================================
// Slot layout (mandate cell) — mirrors the Lean `*Slot` names.
// =============================================================================

/// Slot 0 — `calls_made`. The rate counter, advanced `c → c+1` on each invocation (`Monotonic`).
pub const CALLS_MADE_SLOT: u8 = 0;
/// Slot 1 — `rate_limit`. The granted invocation ceiling N (`Immutable`).
pub const RATE_LIMIT_SLOT: u8 = 1;
/// Slot 2 — `deadline`. The expiry height (`WriteOnce`).
pub const DEADLINE_SLOT: u8 = 2;
/// Slot 3 — `tool_id`. The single allowlisted tool / MCP id (`Immutable` — the SCOPE).
pub const TOOL_ID_SLOT: u8 = 3;

// =============================================================================
// The grant + folded admission predicate (the Lean `Grant` / `delegAdmit` mirror).
// =============================================================================

/// The grantor's pinned delegation parameters — the Rust mirror of the Lean `Grant`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Grant {
    /// The single allowlisted tool / MCP id the worker is scoped to (the SCOPE).
    pub tool_id: i64,
    /// The granted invocation ceiling N: at most N tool calls under this mandate (the RATE).
    pub rate_limit: i64,
    /// The expiry height: invocations presented at `now > deadline` are refused (the DEADLINE).
    pub deadline: i64,
}

/// **`deleg_admit`** — the byte-for-byte mirror of the Lean `delegAdmit g now tool old new`. Does the
/// delegated policy admit advancing the rate counter `old → new`, presented at height `now` for tool
/// `tool`, under grant `g`?  Every conjunct fail-closed:
///
///   * SCOPE:    `tool == g.tool_id`;
///   * DEADLINE: `now <= g.deadline`;
///   * single-step increment `new == old + 1` and sane prior `0 <= old`;
///   * RATE:     `new <= g.rate_limit`.
pub fn deleg_admit(g: &Grant, now: i64, tool: i64, old: i64, new: i64) -> bool {
    tool == g.tool_id && now <= g.deadline && new == old + 1 && 0 <= old && new <= g.rate_limit
}

/// The old-value grid for a grant of `N` calls: the counter ranges over `0..=N` (the Lean `oldGrid`).
pub fn old_grid(n: i64) -> Vec<i64> {
    (0..=n).collect()
}

/// The new-value grid for a grant of `N` calls: `1..=N+1` (the Lean `newGrid`).
pub fn new_grid(n: i64) -> Vec<i64> {
    (0..=n).map(|i| i + 1).collect()
}

/// **`deleg_corpus`** — the full-grid admission decision vector, row-major over `old_grid × new_grid`,
/// the EXACT vector the Lean `AppDiffPinned (mandateSpec g now tool _)` pins. A Rust mirror change or a
/// Lean `delegAdmit` change makes the two diverge ⇒ the differential test fails.
pub fn deleg_corpus(g: &Grant, now: i64, tool: i64) -> Vec<bool> {
    let mut v = Vec::new();
    for old in old_grid(g.rate_limit) {
        for new in new_grid(g.rate_limit) {
            v.push(deleg_admit(g, now, tool, old, new));
        }
    }
    v
}

/// The admitted `(old, new)` transition table the executor's `Cases` allow-list enforces (the Rust
/// mirror of the Lean `mandateSpec.admitTable`): exactly the diagonal advances `(c, c+1)` with
/// `c+1 <= rate_limit`, present iff `tool == g.tool_id` and `now <= g.deadline`.
pub fn admit_table(g: &Grant, now: i64, tool: i64) -> Vec<(i64, i64)> {
    let mut t = Vec::new();
    for old in old_grid(g.rate_limit) {
        for new in new_grid(g.rate_limit) {
            if deleg_admit(g, now, tool, old, new) {
                t.push((old, new));
            }
        }
    }
    t
}

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK we publish for the tool-access-delegation mandate factory.
pub const TAD_FACTORY_VK: [u8; 32] = *b"starbridge-tool-access-deleg-fac";

/// Default per-epoch creation budget.
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Hash a tool / MCP id string to its field value (the executor stores the SCOPE as this scalar).
pub fn tool_id_field(tool: &str) -> FieldElement {
    field_from_bytes(tool.as_bytes())
}

/// The mandate cell program: the rate / expiry / scope caveats the executor checks on every `SetField`
/// — the Rust transcription of the Lean mandate's slot caveats.
///
///   * `calls_made` is `Monotonic` (the counter never rolls back) AND `FieldLte rate_limit` (the
///     granted ceiling) — together the RATE bound `c+1 <= rate_limit` checked on every invocation;
///   * `rate_limit` and `tool_id` are `WriteOnce` — a factory-born mandate is empty, so the ceiling
///     and the SCOPE are bound once by the grant turn (from zero) and frozen thereafter, the
///     birth-compatible form of "fixed at grant" (`Immutable` would freeze the born-empty slots AT
///     ZERO and refuse the grant turn itself — mirror privacy-voting/bounty-board);
///   * `deadline` is `WriteOnce` (set once at grant; thereafter frozen);
///   * `calls_made` mutation is gated by `FieldLteHeight deadline` (the executor refuses an invocation
///     presented after the granted deadline — the time bound).
pub fn tad_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            // ALWAYS: the structural invariants the mandate carries for its whole life.
            guard: TransitionGuard::Always,
            constraints: vec![
                // SCOPE + ceiling are bound once at grant (from zero), then pinned forever.
                StateConstraint::WriteOnce {
                    index: RATE_LIMIT_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: TOOL_ID_SLOT,
                },
                // The expiry is set once, then frozen.
                StateConstraint::WriteOnce {
                    index: DEADLINE_SLOT,
                },
                // RATE: the metered counter can never exceed the granted ceiling.
                StateConstraint::FieldLteField {
                    left_index: CALLS_MADE_SLOT,
                    right_index: RATE_LIMIT_SLOT,
                },
            ],
        },
        TransitionCase {
            // The metered tool invocation: advancing `calls_made`.
            guard: TransitionGuard::MethodIs {
                method: symbol("invoke_tool"),
            },
            constraints: vec![
                // The counter only advances (never rolls back to forge head-room).
                StateConstraint::Monotonic {
                    index: CALLS_MADE_SLOT,
                },
                // DEADLINE: the invocation must be presented within the granted window.
                StateConstraint::FieldLteHeight {
                    index: DEADLINE_SLOT,
                    offset: 0,
                },
            ],
        },
    ])
}

/// Canonical child program VK.
pub fn tad_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&tad_cell_program())
}

/// Build the `FactoryDescriptor` for tool-access-delegation mandate cells.
pub fn tad_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: TAD_FACTORY_VK,
        child_program_vk: Some(tad_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(tad_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The worker holds an attenuatable SelfCell cap — the ocap handle to invoke under the
            // mandate. Sub-delegation narrows it (see `intent/src/agent_mandate.rs`).
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a factory-born mandate cell is
        // born empty and the GRANT turn binds `TOOL_ID` + `RATE_LIMIT` +
        // `DEADLINE` (`WriteOnce`, frozen after) before any invocation. The
        // previous birth `NonZero`s validated against `params.initial_fields`
        // (a `Vec<(u32, u64)>` written little-endian into the LOW bytes of the
        // slot), which (a) cannot carry the real 32-byte `tool_id_field` hash
        // and (b) makes an LE-encoded `rate_limit` read as an astronomically
        // large big-endian operand of `FieldLteField` — a vacuous ceiling.
        // Mirror privacy-voting/bounty-board: born empty, bound by the grant
        // turn under `WriteOnce`.
        field_constraints: vec![],
        state_constraints: vec![
            // SCOPE + ceiling + expiry: bound once by the grant turn (from
            // zero), frozen thereafter. (`Immutable` would freeze the
            // born-empty slots AT ZERO and refuse the grant turn itself.)
            StateConstraint::WriteOnce {
                index: TOOL_ID_SLOT,
            },
            StateConstraint::WriteOnce {
                index: RATE_LIMIT_SLOT,
            },
            StateConstraint::WriteOnce {
                index: DEADLINE_SLOT,
            },
            StateConstraint::Monotonic {
                index: CALLS_MADE_SLOT,
            },
            StateConstraint::FieldLteField {
                left_index: CALLS_MADE_SLOT,
                right_index: RATE_LIMIT_SLOT,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![tad_factory_descriptor()]
}

// =============================================================================
// Turn builders — GRANT / INVOKE / REVOKE.
// =============================================================================

/// **GRANT** — the grantor mints the mandate by pinning the SCOPE (`tool_id`), the RATE ceiling
/// (`rate_limit`), and the EXPIRY (`deadline`), with the counter born at 0. (Effects mirror the Lean
/// mandate cell's initial fields.)
pub fn build_grant_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    tool: &str,
    rate_limit: u64,
    deadline: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: TOOL_ID_SLOT as usize,
            value: tool_id_field(tool),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: RATE_LIMIT_SLOT as usize,
            value: field_from_u64(rate_limit),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: DEADLINE_SLOT as usize,
            value: field_from_u64(deadline),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("tool-access-granted"),
                vec![
                    tool_id_field(tool),
                    field_from_u64(rate_limit),
                    field_from_u64(deadline),
                ],
            ),
        },
    ];
    cipherclerk.make_action(mandate_cell, "grant_tool_access", effects)
}

/// **INVOKE** — the worker meters one tool invocation: advance `calls_made` from `prev` to `prev + 1`.
/// The executor's caveat gate admits this IFF `prev+1 <= rate_limit`, the height is within `deadline`,
/// and (by the immutable `tool_id`) the mandate is the scoped one — exactly the Lean
/// `tool_invocation_commit_iff_admit`.
pub fn build_invoke_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    prev_calls_made: u64,
    invocation_payload: FieldElement,
) -> Action {
    let new_count = prev_calls_made + 1;
    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new_count),
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("tool-invoked"),
                vec![field_from_u64(new_count), invocation_payload],
            ),
        },
    ];
    cipherclerk.make_action(mandate_cell, "invoke_tool", effects)
}

/// **REVOKE** — the grantor revokes the whole mandate (single-machine immediate revocation). Mirrors
/// the Lean `invocation_revoked_rejected`: the credential's nullifier enters the committed revocation
/// registry, and thereafter every invocation under this mandate rolls back. Emits the real
/// `Effect::RevokeDelegation` (the same effect `intent/src/agent_mandate.rs::materialize_revoke` emits).
pub fn build_revoke_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    worker: CellId,
) -> Action {
    let effects = vec![
        Effect::RevokeDelegation { child: worker },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(symbol("tool-access-revoked"), vec![]),
        },
    ];
    cipherclerk.make_action(mandate_cell, "revoke_tool_access", effects)
}

// =============================================================================
// The deos-native surface — the MANDATE as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: tool-access-delegation, re-expressed as a
// composed deos app and PROMOTED into `src/`. The same operations are ONE [`DeosApp`]
// ([`tad_app`] below); the framework wires the rest — per-viewer projection, web-of-cells
// publish (the MANDATE cell IS a `dregg://` sturdyref), the rehydratable frustum-snapshot,
// the generated `<dregg-affordance-surface>` component, and the manifest — none of which
// the floor's factory/turn-builders had.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror subscription's Cases-floor promotion).
// The state-mutating operation (`invoke`) is a [`GatedAffordance`] carrying a live-state
// PRECONDITION ([`budget_remaining_precondition`]: `calls < rate`); the FULL mandate
// program ([`tad_cell_program`], the `Cases` floor carrying the `invoke_tool` method
// symbol) is INSTALLED on the seeded mandate cell ([`seed_mandate`]) and RE-ENFORCED by
// the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_invoke`] then submits the FULL counter-advancing turn ([`invoke_effects`],
//      reading the LIVE `calls_made`), and the executor RE-ENFORCES the installed
//      `Cases` program on the produced transition — so the RATE bound
//      `FieldLteField(CALLS_MADE <= RATE_LIMIT)` (an over-budget invocation), the
//      `Monotonic(CALLS_MADE)` (a counter rewind to forge head-room), and the
//      `FieldLteHeight(DEADLINE)` (a past-deadline invocation — height-aware, so it
//      CANNOT be read by the deos precondition) are all REAL executor refusals in the
//      SUBMISSION path — the half the floor's `evaluate`-only tests never exercised
//      through a real signed turn (see `tests/deos_seam.rs`).
//
// Both gates are genuine (`is_attenuation` + `CellProgram::evaluate`). `grant` carries the
// REAL [`Effect::GrantCapability`] (the cap-graph half — an attenuated mandate-cell slice
// to a worker cell) as a cap-only affordance.

/// The tool-access rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the
/// floor crate's cap-graph enforces (one mandate-cap holder, sub-delegated to a worker):
///
///   - a WORKER (the delegated agent currently holding the mandate) holds
///     [`AuthRequired::Either`] — it can `invoke` (meter one tool call) AND `view_grant`;
///   - the GRANTOR (the agent that minted the mandate) holds [`AuthRequired::None`]/root —
///     it can `grant` (hand the mandate's invoke cap FORWARD, narrowed) on top of
///     everything a worker can do.
///
/// So `Either ⊂ None` IS the worker ⊂ grantor ladder (the narrow worker tier is strictly
/// contained in the grantor's root authority).
pub const WORKER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The grantor rights tier (root — mint/grant the invoke cap + all). See [`WORKER_RIGHTS`].
pub const GRANTOR_RIGHTS: AuthRequired = AuthRequired::None;

/// The permissions a mandate's invoke capability carries (a `SelfCell` cap a worker holds;
/// handed forward NARROWED, never widened — the `derive_no_amplify` shape). Matches the
/// factory's `allowed_cap_templates` ceiling.
pub const INVOKE_CAP_PERMISSIONS: AuthRequired = AuthRequired::Signature;

/// **`grant` effect** — the grantor's real cap handoff: an [`Effect::GrantCapability`] of
/// the mandate's invoke cap to a worker cell, at the SAME (`Signature`) permissions —
/// narrowed, never widened (the `derive_no_amplify` cap-graph half of attenuated
/// delegation, the same shape `intent/src/agent_mandate.rs::materialize_grant` emits). This
/// is the deos affordance's effect-template for `grant`, NOT a scaffold stand-in.
pub fn grant_invoke_effect(mandate: CellId, worker: CellId) -> Effect {
    Effect::GrantCapability {
        from: mandate,
        to: worker,
        cap: CapabilityRef {
            target: mandate,
            slot: CALLS_MADE_SLOT as u32,
            permissions: INVOKE_CAP_PERMISSIONS,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// The `invoke` **live-state precondition** — the mandate must have BUDGET REMAINING
/// (`calls_made < rate_limit`, i.e. `calls_made <= rate_limit - 1`). A real [`CellProgram`]
/// read against the cell's current state, so an `invoke` button is LIT while budget remains
/// and goes DARK the instant the counter reaches the ceiling (the htmx tooth). This gates
/// "may `invoke` fire now"; the RATE INVARIANT (`FieldLteField(CALLS_MADE <= RATE_LIMIT)`)
/// is the installed [`tad_cell_program`] the executor re-enforces on the produced
/// transition.
///
/// Note: this CANNOT read the DEADLINE — `FieldLteHeight(DEADLINE)` is height-aware (it
/// depends on the block height the turn is presented at, which a `(state, state)`
/// precondition read does not see). The deadline tooth bites in the EXECUTOR on the
/// submitted turn (see [`fire_invoke`] / `tests/deos_seam.rs`), not in this precondition.
pub fn budget_remaining_precondition() -> CellProgram {
    // `calls < rate` ≡ `calls <= rate - 1` ≡ `FieldLteOther { calls, rate, delta: -1 }`.
    CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: CALLS_MADE_SLOT,
        other: RATE_LIMIT_SLOT,
        delta: -1,
    }])
}

/// **The tool-access MANDATE as a composed [`DeosApp`]** — the whole interaction surface,
/// on the deos bones. The mandate cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Three operations on the MANDATE cell, on the worker ⊂ grantor rights ladder:
///
///   - `view_grant` — a cap-only affordance (a WORKER reads the mandate's terms):
///     `Either`, an `EmitEvent`;
///   - `grant` — a cap-only affordance carrying the REAL [`Effect::GrantCapability`] (the
///     grantor hands the invoke cap forward NARROWED — the cap-graph half): `None`/root;
///   - `invoke` — a [`GatedAffordance`] (a WORKER meters one tool call): `Either`, a
///     live-state PRECONDITION (budget remains, `calls < rate`); the real fire
///     ([`fire_invoke`]) submits the FULL counter-advancing turn (reading the live
///     `calls_made`), re-enforced by the executor's installed `Cases` program (the
///     `FieldLteField` rate ceiling + `Monotonic` counter + `FieldLteHeight` deadline
///     caveats BITE on the produced transition).
///
/// The mandate cell is published into the web-of-cells at the worker tier (a delegated
/// agent on another federation reacquires the mandate across the membrane) and is
/// discoverable under `tools` / `delegation`.
///
/// Seed the cell's program + grant state with [`seed_mandate`] so the gated fires have a
/// live state and the executor re-enforces the caveats.
pub fn tad_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let mandate = cipherclerk.cell_id();

    // `view_grant` — a worker reads the mandate's terms. Cap-only.
    let view = CellAffordance::new(
        "view_grant",
        WORKER_RIGHTS,
        Effect::EmitEvent {
            cell: mandate,
            event: Event::new(symbol("tool-access-viewed"), vec![]),
        },
    );
    // `grant` — the grantor hands the invoke cap forward NARROWED. A real
    // `Effect::GrantCapability`, cap-only (the cap-graph half — no state mutation).
    let grant = CellAffordance::new(
        "grant",
        GRANTOR_RIGHTS,
        grant_invoke_effect(mandate, CellId::from_bytes([0xAA; 32])),
    );
    // `invoke` — a WORKER meters one tool call. The GatedAffordance carries the DECISIVE
    // effect (the `calls_made` counter advance) as its surface representative AND a
    // live-state PRECONDITION ([`budget_remaining_precondition`]: `calls < rate`) — so the
    // button is lit while budget remains and dark once the ceiling is reached (the htmx
    // tooth), and the cap∧state gate decides its verdict in-band. The actual fire
    // ([`fire_invoke`]) submits the FULL counter-advancing turn ([`invoke_effects`], reading
    // the LIVE `calls_made`), which the executor re-enforces the installed `Cases` program
    // on — so `FieldLteField(CALLS_MADE <= RATE_LIMIT)` BITES: an over-budget invocation is
    // REFUSED.
    let invoke = GatedAffordance::new(
        CellAffordance::new(
            "invoke",
            WORKER_RIGHTS,
            Effect::SetField {
                cell: mandate,
                index: CALLS_MADE_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        budget_remaining_precondition(),
    );

    DeosApp::builder(
        "tool-access-delegation",
        cipherclerk.clone(),
        executor.clone(),
    )
    .discoverable(vec!["tools".into(), "delegation".into()])
    .cell(
        DeosCell::new(mandate, "mandate")
            .affordance(view)
            .affordance(grant)
            .gated(invoke)
            // Published at the WORKER tier (`Either`) — the narrowest role that holds
            // the mandate, and the narrowest cap-only affordance (`view_grant`, Either)
            // on the surface. A snapshot's lineage caps the per-viewer rehydration meet
            // (`held ∧ lineage`); publishing BELOW the worker tier (e.g. `Signature`)
            // would cap every rehydration below `view_grant`'s `Either` tier, so the
            // worker could never reacquire its own read across the membrane. The worker
            // tier is the correct lineage (the delegated agent reacquires the mandate).
            .publish(WORKER_RIGHTS),
    )
    .build()
}

/// **`invoke` effects** — the state-parameterized metered-invocation body: advance
/// `calls_made` to `new_calls` (the executor's installed `Monotonic` + `FieldLteField`
/// caveats re-enforce that it only steps forward and never exceeds `rate_limit`), and emit
/// `tool-invoked`. This is the ONE coherent transition the installed `Cases` program
/// admits on the `invoke_tool` method. THIS is the turn [`fire_invoke`] submits (computed
/// from the cell's LIVE `calls_made`).
pub fn invoke_effects(mandate: CellId, new_calls: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: mandate,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new_calls),
        },
        Effect::EmitEvent {
            cell: mandate,
            event: Event::new(symbol("tool-invoked"), vec![field_from_u64(new_calls)]),
        },
    ]
}

/// **Seed the MANDATE cell** so the gated fires have live state + the caveats bite: install
/// the full mandate [`tad_cell_program`] (the `Cases` floor) on the seeded mandate cell (so
/// the executor re-enforces it on every touching turn), then bind the grant terms directly
/// into the embedded ledger — `RATE_LIMIT` / `TOOL_ID` / `DEADLINE` (`WriteOnce`, frozen
/// after) and `CALLS_MADE = 0`.
///
/// The `invoke_tool` case carries `FieldLteHeight(DEADLINE, offset: 0)` — the executor admits
/// an invocation only while `DEADLINE <= block_height`. The embedded executor runs at
/// `block_height == 0` (it advances only when a host sets it to model block progression), so
/// an honest invoke clears the deadline tooth iff `DEADLINE == 0`; [`register_deos`] seeds
/// `DEADLINE = 0` (no-expiry at the embedded height). A mandate seeded with `DEADLINE >
/// block_height` has its invoke REFUSED by the executor's `FieldLteHeight(DEADLINE)` — the
/// height-aware tooth the deos precondition cannot read (see [`fire_invoke`] /
/// `tests/deos_seam.rs`). After seeding, the mandate is granted with the counter at 0 — a real
/// `(old, new)` baseline against which `invoke` advances the counter (up to `rate_limit`).
pub fn seed_mandate(executor: &EmbeddedExecutor, tool: &str, rate_limit: u64, deadline: u64) {
    let mandate = executor.cell_id();
    executor.install_program(mandate, tad_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&mandate) {
            cell.state
                .set_field(RATE_LIMIT_SLOT as usize, field_from_u64(rate_limit));
            cell.state
                .set_field(TOOL_ID_SLOT as usize, tool_id_field(tool));
            cell.state
                .set_field(DEADLINE_SLOT as usize, field_from_u64(deadline));
            cell.state
                .set_field(CALLS_MADE_SLOT as usize, field_from_u64(0));
        }
    });
}

/// **Fire `invoke`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then the
/// FULL counter-advancing turn the executor re-enforces the mandate program on. The
/// two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ Either AND
/// budget remains, `calls < rate`) WITHOUT touching the executor; on both passing, the
/// complete `invoke_tool` turn ([`invoke_effects`] reading the LIVE counter) is submitted to
/// the executor, and the executor's re-enforcement of
/// the installed `Cases` program ([`tad_cell_program`]) is the SECOND, verified gate — the
/// `FieldLteField(CALLS_MADE <= RATE_LIMIT)` rate ceiling, the `Monotonic(CALLS_MADE)`
/// no-rewind, and the height-aware `FieldLteHeight(DEADLINE)` all bite on the produced
/// transition. Anti-ghost both ways: a precondition miss never submits; a program violation
/// is a real executor refusal.
///
/// The counter is read from the cell's live state (`calls_made ⇒ calls_made + 1`), so the
/// caller threads nothing. Use [`seed_mandate`] first.
///
/// The submitted turn carries the `invoke_tool` METHOD SYMBOL (not the `invoke` surface
/// name): the installed `Cases` program's `invoke_tool` dispatch case must match the turn's
/// method for the operation-scoped `Monotonic(CALLS_MADE)` + `FieldLteHeight(DEADLINE)`
/// caveats to fire (and to satisfy the Cav-Codex Block 4 default-deny: a `Cases` program with
/// dispatch cases REJECTS a turn whose method matches none of them). So the gate is the
/// `invoke` affordance (the published cap∧state button) while the wire turn is the
/// `invoke_tool` method the floor's program scopes.
pub fn fire_invoke(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::FireExecuteError> {
    use dregg_app_framework::{FireError, FireExecuteError};
    let cell = &app.cells()[0];
    let mandate = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on a miss
    // (the cap-gate AND the live-state `budget_remaining` precondition the gated affordance
    // carries). A miss is distinguished (cap vs state) for a precise refusal.
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "invoke")
    {
        let ga = cell
            .gated_surface()
            .get("invoke")
            .expect("invoke is a gated affordance");
        let state = executor.cell_state(mandate).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "invoke".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(mandate, held, &state, &state).unwrap_err(),
        ));
    }
    // Both teeth bit: read the LIVE counter and submit the FULL `invoke_tool` turn (the method
    // symbol the installed `Cases` program's dispatch case scopes), which the executor
    // re-enforces the program on (the rate ceiling, the counter Monotonic, the deadline).
    let live = executor.cell_state(mandate).expect("checked above");
    let new_calls = field_to_u64(&live.fields[CALLS_MADE_SLOT as usize]) + 1;
    let action =
        cipherclerk.make_action(mandate, "invoke_tool", invoke_effects(mandate, new_calls));
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the `calls_made` counter the mandate stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("tool-access-delegation")
        .slot("CALLS_MADE_SLOT", CALLS_MADE_SLOT as u64)
        .slot("RATE_LIMIT_SLOT", RATE_LIMIT_SLOT as u64)
        .slot("DEADLINE_SLOT", DEADLINE_SLOT as u64)
        .slot("TOOL_ID_SLOT", TOOL_ID_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&TAD_FACTORY_VK))
        .topic("GRANTED", "tool-access-granted")
        .topic("INVOKED", "tool-invoked")
        .topic("REVOKED", "tool-access-revoked")
        .topic("VIEWED", "tool-access-viewed")
}

/// **Register the tool-access-delegation starbridge-app** on a shared context — the FLOOR
/// (the executor-truth layer: the factory descriptor whose `state_constraints` ARE the rate
/// / expiry / scope mandate policy, installed on every born mandate cell) AND the
/// deos-native composition surface (the [`DeosApp`], folded into the context's affordance
/// registry — so the same `register(ctx)` mounts BOTH).
///
/// The factory + inspector are where SOUNDNESS lives (an over-rate / past-deadline / rewind
/// invocation is a real executor refusal on the born cell). The deos surface is the
/// composition skin: per-viewer projection, the cap∧state gated fire, the `dregg://`
/// publish, the rehydratable snapshot, the generated component, the manifest.
/// [`register_deos`] folds the surface; this returns the factory VK (the floor's identity)
/// as before so the floor's callers are unchanged.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(tad_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "tad-mandate".into(),
        descriptor: serde_json::json!({
            "component": "dregg-tad-mandate",
            "module": "/starbridge-apps/tool-access-delegation/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["calls_made", "rate_limit", "deadline", "tool_id"],
            "slot_layout": {
                "calls_made": CALLS_MADE_SLOT,
                "rate_limit": RATE_LIMIT_SLOT,
                "deadline": DEADLINE_SLOT,
                "tool_id": TOOL_ID_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&tad_child_program_vk()),
            "methods": ["grant_tool_access", "invoke_tool", "revoke_tool_access"],
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context.
    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`tad_app`]) on a shared context: build the composed
/// [`DeosApp`] from the context's cipherclerk + executor, seed the mandate cell's program +
/// grant state (so the gated `invoke` fire bites), and fold the app into the context's
/// affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so a host can
/// also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the web-of-cells).
/// This is the census PROMOTION: the deos surface now ships from `src/`, not from a
/// side-proof in `tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = tad_app(ctx.cipherclerk(), ctx.executor());
    // Seed the mandate cell so the gated `invoke` fire has a live `(old, new)` and the full
    // mandate program (installed here) is re-enforced by the executor on every touching turn.
    // `DEADLINE = 0` clears `FieldLteHeight(DEADLINE)` at the embedded executor's
    // `block_height == 0` (no-expiry at this height; see [`seed_mandate`]).
    seed_mandate(ctx.executor(), "search-mcp", 8, 0);
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([5u8; 32])
    }

    /// The Lean `demoGrant`: tool 77, rate 3, deadline 100.
    const DEMO: Grant = Grant {
        tool_id: 77,
        rate_limit: 3,
        deadline: 100,
    };

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            tad_factory_descriptor().hash(),
            tad_factory_descriptor().hash()
        );
    }

    #[test]
    fn deleg_admit_matches_lean_demo() {
        // Lean `#guard delegAdmit demoGrant …` witnesses.
        assert!(deleg_admit(&DEMO, 50, 77, 0, 1)); // invocation 1 admitted
        assert!(deleg_admit(&DEMO, 50, 77, 1, 2)); // invocation 2
        assert!(deleg_admit(&DEMO, 50, 77, 2, 3)); // invocation 3 (the last)
        assert!(!deleg_admit(&DEMO, 50, 77, 3, 4)); // over-rate (4 > 3) — RATE TOOTH
        assert!(!deleg_admit(&DEMO, 50, 99, 0, 1)); // out-of-scope tool — SCOPE TOOTH
        assert!(!deleg_admit(&DEMO, 101, 77, 0, 1)); // past-deadline — DEADLINE TOOTH
    }

    #[test]
    fn admit_table_holds_exactly_three_legal_advances() {
        // Lean: `mandateSpec demoGrant 50 77 5 |>.admitTable.length == 3`, contains (0,1),(1,2),(2,3).
        let t = admit_table(&DEMO, 50, 77);
        assert_eq!(t.len(), 3);
        assert!(t.contains(&(0, 1)));
        assert!(t.contains(&(1, 2)));
        assert!(t.contains(&(2, 3)));
        assert!(!t.contains(&(3, 4))); // over-rate advance ABSENT (TOOTH)
        // Out-of-scope / past-deadline bake an EMPTY table.
        assert_eq!(admit_table(&DEMO, 50, 99).len(), 0);
        assert_eq!(admit_table(&DEMO, 101, 77).len(), 0);
    }

    #[test]
    fn corpus_matches_lean_pinned_vector() {
        // The EXACT vector the Lean `AppDiffPinned (mandateSpec demoGrant 50 77 5)` `#guard` pins.
        // Row-major over old {0,1,2,3} × new {1,2,3,4}; 16 cells; exactly the 3 diagonal advances true.
        let expected = vec![
            // old = 0:  →1 true,  →2,→3,→4 false
            true, false, false, false, //
            // old = 1:  →2 true
            false, true, false, false, //
            // old = 2:  →3 true
            false, false, true, false, //
            // old = 3:  none (3→4 is over-rate)
            false, false, false, false,
        ];
        assert_eq!(deleg_corpus(&DEMO, 50, 77), expected);
    }

    #[test]
    fn grant_action_pins_scope_rate_deadline() {
        let cipherclerk = test_cipherclerk();
        let action = build_grant_action(&cipherclerk, test_cell(), "search-mcp", 3, 100);
        // tool_id, rate_limit, deadline, calls_made(=0), + event.
        assert_eq!(action.effects.len(), 5);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == TOOL_ID_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == RATE_LIMIT_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == DEADLINE_SLOT as usize
        ));
    }

    #[test]
    fn invoke_action_advances_counter_by_one() {
        let cipherclerk = test_cipherclerk();
        let action = build_invoke_action(&cipherclerk, test_cell(), 2, field_from_u64(0xabc));
        // calls_made := 3, + event.
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, CALLS_MADE_SLOT as usize);
                assert_eq!(*value, field_from_u64(3));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
    }

    #[test]
    fn revoke_action_emits_real_revoke_delegation() {
        let cipherclerk = test_cipherclerk();
        let worker = CellId::from_bytes([9u8; 32]);
        let action = build_revoke_action(&cipherclerk, test_cell(), worker);
        match &action.effects[0] {
            Effect::RevokeDelegation { child } => assert_eq!(*child, worker),
            other => panic!("expected RevokeDelegation, got {other:?}"),
        }
    }

    #[test]
    fn invoke_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let action = build_invoke_action(&cipherclerk, test_cell(), 0, field_from_u64(1));
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, TAD_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("tad-mandate").is_some());
        // `register` now ALSO mounts the deos surface (the census promotion): the composed
        // DeosApp is folded into the context's affordance registry on the same call.
        assert_eq!(
            ctx.affordance_registry().len(),
            1,
            "register mounts the deos surface on the same context"
        );
    }

    // ── the deos surface composition (the cap-only set vs the gated set) ──────

    #[test]
    fn the_mandate_app_composes_the_three_operations() {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        let app = tad_app(&cipherclerk, &executor);

        assert_eq!(app.name(), "tool-access-delegation");
        assert_eq!(app.cells().len(), 1);
        let mandate = &app.cells()[0];

        // The cap-only surface carries the read + the (cap-graph) invoke grant.
        let mut cap_only = mandate.surface().all_names();
        cap_only.sort();
        assert_eq!(
            cap_only,
            vec!["grant".to_string(), "view_grant".to_string()]
        );

        // The gated surface carries the single state-mutating, cap∧state operation.
        let gated: Vec<String> = mandate
            .gated_surface()
            .affordances
            .iter()
            .map(|g| g.name().to_string())
            .collect();
        assert_eq!(gated, vec!["invoke".to_string()]);

        // The mandate cell is the agent's own; published at the worker (Either) tier — the
        // narrowest role that holds the mandate AND the narrowest cap-only affordance tier
        // (`view_grant`, Either), so a snapshot is reacquirable by the worker.
        assert_eq!(mandate.cell(), cipherclerk.cell_id());
        assert_eq!(mandate.published_authority(), Some(&WORKER_RIGHTS));
    }

    #[test]
    fn seed_mandate_installs_the_cases_program_and_zero_counter() {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        seed_mandate(&executor, "search-mcp", 8, 0);

        // The seeded mandate cell carries the FULL `Cases` floor program (the seam's
        // enforcement layer the executor re-enforces on every touching turn).
        let installed = executor.with_ledger_mut(|ledger| {
            ledger
                .get(&cipherclerk.cell_id())
                .map(|c| c.program.clone())
        });
        assert_eq!(installed, Some(tad_cell_program()));

        // ...and the counter is born at 0, with the rate ceiling bound.
        let state = executor
            .cell_state(cipherclerk.cell_id())
            .expect("seeded cell exists");
        assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
        assert_eq!(state.fields[RATE_LIMIT_SLOT as usize], field_from_u64(8));
    }

    #[test]
    fn register_deos_mounts_the_seeded_surface() {
        let ctx = test_context();
        let app = register_deos(&ctx);
        assert_eq!(app.name(), "tool-access-delegation");
        assert_eq!(ctx.affordance_registry().len(), 1);

        // The seeded mandate is granted with budget remaining, so a worker can meter a call
        // through the mounted surface immediately (the seam is closed + live).
        let receipt = fire_invoke(
            &app,
            &AuthRequired::Either,
            ctx.cipherclerk(),
            ctx.executor(),
        )
        .expect("the mounted, seeded surface meters an invocation (the promotion is live)");
        assert_ne!(receipt.turn_hash, [0u8; 32]);
    }
}
