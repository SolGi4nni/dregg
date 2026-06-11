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
//!   * `rate_limit`  (the granted N) — `Immutable`: the ceiling fixed at grant, never raised.
//!   * `deadline`    (the EXPIRY) — `WriteOnce`: the grantor sets it once at grant; thereafter frozen.
//!   * `tool_id`     (the SCOPE) — `Immutable`: the single allowlisted tool/MCP id.
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
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldConstraint,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard,
    canonical_program_vk, field_from_u64, hex_encode_32, symbol,
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
///   * `rate_limit` and `tool_id` are `Immutable` (the ceiling and the SCOPE are fixed at grant);
///   * `deadline` is `WriteOnce` (set once at grant; thereafter frozen);
///   * `calls_made` mutation is gated by `FieldLteHeight deadline` (the executor refuses an invocation
///     presented after the granted deadline — the time bound).
pub fn tad_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            // ALWAYS: the structural invariants the mandate carries for its whole life.
            guard: TransitionGuard::Always,
            constraints: vec![
                // SCOPE + ceiling are pinned forever.
                StateConstraint::Immutable {
                    index: RATE_LIMIT_SLOT,
                },
                StateConstraint::Immutable {
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
        field_constraints: vec![
            // A grant must pin a non-zero rate ceiling and tool id (a zero grant is malformed).
            FieldConstraint::NonZero {
                field_index: RATE_LIMIT_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: TOOL_ID_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: TOOL_ID_SLOT,
            },
            StateConstraint::Immutable {
                index: RATE_LIMIT_SLOT,
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
}

/// Register the tool-access-delegation starbridge-app on a shared context.
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

    factory_vk
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
    }
}
