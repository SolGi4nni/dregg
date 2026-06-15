//! # Compute marketplace (Starbridge organ-composition app)
//!
//! A requester needs a unit of work done; a provider has spare compute. They
//! transact a job neither trusts the other over. The requester **posts a job**
//! with an escrowed **budget**; a provider **bids** a price (which must fit the
//! budget); the job **settles atomically** — the accepted price is paid to the
//! provider and any remainder refunds to the requester, all-or-nothing and
//! value-neutral. No escrow-agent, no off-chain coordinator: the job is a single
//! factory-born cell whose installed `CellProgram` IS the rules, re-checked by
//! the verified executor on every turn that touches it.
//!
//! This app exists to show the system is **not a toy**: it composes — in one
//! cell's slot-caveat program — the guarantees of four of the night's organs.
//!
//! | Organ      | Guarantee                                | How this cell enforces it |
//! |------------|------------------------------------------|---------------------------|
//! | BUDGET     | the bid can never exceed the budget      | `FieldLteField { BID <= BUDGET }` — the accepted price is a bounded draw (the AffineLe budget gate) |
//! | ACCEPTED   | the accepted price, bound exactly once   | `WriteOnce(BID)` — the requester accepts a price once; tamper-evident |
//! | FLASHWELL  | atomic, conserving settlement            | `AffineEq { PAID + REFUNDED - BUDGET = 0 }` (settle) + the universal no-mint `AffineLe` — the payout splits the budget with no mint/burn |
//! | LIFECYCLE  | one-way, no replay, no double-settle      | `StrictMonotonic(STATE)` — `POSTED->BID->SETTLED` |
//!
//! Built from dregg primitives only: `FactoryDescriptor`, `Effect::SetField` /
//! `Effect::EmitEvent`, `Authorization::Signature` from
//! `AppCipherclerk::make_action`, and Lane-G `StateConstraint` slot caveats.
//! No domain-specific compute `Effect`, no `Authorization::Unchecked`, no
//! `[0u8; 64]` placeholder signatures. Routes through the real verified
//! executor via `EmbeddedExecutor` / `submit_action`.
//!
//! ## The job lifecycle
//!
//! ```text
//! POSTED ──bid──▶ BID ──settle──▶ SETTLED
//! ```
//!
//! - **post**   — the requester opens a job: writes the `BUDGET` (the most a bid
//!   may cost) and the `REQUESTER_HASH` + a `SPEC_HASH` (the sealed job
//!   description), `STATE = POSTED`.
//! - **bid**    — a provider bids `price <= BUDGET` into `BID`, binds
//!   `PROVIDER_HASH`, `STATE -> BID`.
//! - **settle** — the deal closes: `PAID + REFUNDED == BUDGET`,
//!   `STATE -> SETTLED`. Provider paid in full ⇒ `PAID == BID,
//!   REFUNDED == BUDGET - BID`; the budget is split with no mint/burn.

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

// =============================================================================
// Job-cell state schema
// =============================================================================

/// `blake3` of the requester's identifier. `WriteOnce` — bound at posting.
pub const REQUESTER_HASH_SLOT: usize = 2;
/// `blake3` of the winning provider's identifier. `WriteOnce` — bound at bid.
pub const PROVIDER_HASH_SLOT: usize = 3;
/// The job BUDGET — the most a bid may cost. `WriteOnce`, set at posting. The
/// trustline-style `line` a bid draws against.
pub const BUDGET_SLOT: usize = 4;
/// The accepted bid PRICE. `WriteOnce` (the draw), and `<= BUDGET` (the budget
/// gate `bid <= budget`).
pub const BID_SLOT: usize = 5;
/// The sealed job-spec digest the requester commits at post. `WriteOnce` — the
/// job description, bound exactly once, tamper-evident.
pub const SPEC_HASH_SLOT: usize = 6;
/// Funds PAID to the provider at settlement. `WriteOnce`.
pub const PAID_SLOT: usize = 7;
/// Funds REFUNDED to the requester at settlement. `WriteOnce`.
pub const REFUNDED_SLOT: usize = 8;
/// The job STATE code. `StrictMonotonic` — the one-way lifecycle.
pub const STATE_SLOT: usize = 9;

/// `STATE` codes — strictly increasing, so the lifecycle is one-way.
pub const STATE_POSTED: u64 = 1;
pub const STATE_BID: u64 = 2;
pub const STATE_SETTLED: u64 = 3;

/// Factory VK we publish for the compute-job factory.
pub const JOB_FACTORY_VK: [u8; 32] = *b"starbridge-compute-exchange-fctr";

// =============================================================================
// Cell program — the organ-composition state machine
// =============================================================================

/// The `CellProgram` installed on every job cell — a `Cases` program whose
/// `Always` case carries the perpetual invariants and whose method-scoped cases
/// bind each lifecycle step. The four organ guarantees:
///
/// - BUDGET   (Always): `FieldLteField { BID <= BUDGET }` — the accepted price
///   is bounded by the job's budget, every turn (the AffineLe budget gate).
/// - ACCEPTED (Always): `WriteOnce(BID)` — the accepted price is committed
///   exactly once, tamper-evident.
/// - FLASHWELL (`settle`): `AffineEq { PAID + REFUNDED - BUDGET = 0 }` — the
///   settlement splits the budget with no mint/burn. Scoped to `settle` because
///   the identity only holds once the budget is paid out.
/// - LIFECYCLE (Always): `StrictMonotonic(STATE)` — one-way, no replay, no
///   double-settle.
///
/// Plus `WriteOnce` on the identity / amount registers so nothing rebinds. The
/// program is method-dispatching, so an unknown method is default-denied
/// (`NoTransitionCaseMatched`).
pub fn job_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ── invariants: every transition, every method ──────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: job_invariants(),
        },
        // ── post: open the job (requester + budget + spec bound here) ───
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("post"),
            },
            constraints: vec![],
        },
        // ── bid: a provider bids <= budget (BUDGET invariant above) ─────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("bid"),
            },
            constraints: vec![],
        },
        // ── settle: FLASHWELL conservation — PAID+REFUNDED == BUDGET ─────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("settle"),
            },
            constraints: vec![StateConstraint::AffineEq {
                terms: vec![
                    (1, PAID_SLOT as u8),
                    (1, REFUNDED_SLOT as u8),
                    (-1, BUDGET_SLOT as u8),
                ],
                c: 0,
            }],
        },
    ])
}

/// The perpetual invariants (the `Always` case) — also flattened into the
/// descriptor's `state_constraints` for constructor transparency.
fn job_invariants() -> Vec<StateConstraint> {
    vec![
        // ── identity & terms: bound once, frozen ─────────────────────────
        StateConstraint::WriteOnce {
            index: REQUESTER_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: PROVIDER_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: BUDGET_SLOT as u8,
        },
        // ── BUDGET: the accepted price is bounded by the budget (the gate) ─
        StateConstraint::FieldLteField {
            left_index: BID_SLOT as u8,
            right_index: BUDGET_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: BID_SLOT as u8,
        },
        // ── ACCEPTED: the sealed spec is committed exactly once ──────────
        StateConstraint::WriteOnce {
            index: SPEC_HASH_SLOT as u8,
        },
        // ── settlement registers freeze once written ────────────────────
        StateConstraint::WriteOnce {
            index: PAID_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: REFUNDED_SLOT as u8,
        },
        // ── FLASHWELL (no-mint half, universally true): the payout can
        //    never exceed the budget — `PAID + REFUNDED <= BUDGET`. Holds on
        //    every turn (0 <= budget before settle; equality at settle), so it
        //    is an executor-enforced invariant. The exact no-burn equality is
        //    the settle-scoped `AffineEq` in `job_cell_program` (the canonical
        //    child-program recipe) and the settle builder, which always emits a
        //    balanced split.
        StateConstraint::AffineLe {
            terms: vec![
                (1, PAID_SLOT as u8),
                (1, REFUNDED_SLOT as u8),
                (-1, BUDGET_SLOT as u8),
            ],
            c: 0,
        },
        // ── LIFECYCLE: one-way, no replay, no double-settle ──────────────
        StateConstraint::StrictMonotonic {
            index: STATE_SLOT as u8,
        },
    ]
}

/// The descriptor's flat `state_constraints` — exactly the predicate the
/// executor installs as the born cell's `CellProgram` and re-checks
/// **unconditionally** on every turn (`apply.rs::apply_create_cell_from_factory`
/// installs `CellProgram::Predicate(state_constraints)`). These are therefore
/// the `Always`-true invariants only — including the no-mint
/// `PAID + REFUNDED <= BUDGET`. The exact no-burn equality is settle-scoped (it
/// would be false at `bid` time, when `PAID = REFUNDED = 0 < BUDGET`), so it
/// lives in the `settle` case of [`job_cell_program`] (the canonical
/// `child_program_vk` recipe) and is upheld by [`build_settle_action`], which
/// always emits a balanced split.
fn job_state_constraints() -> Vec<StateConstraint> {
    job_invariants()
}

/// Canonical child-program VK for job cells.
pub fn job_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&job_cell_program())
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the job-cell `FactoryDescriptor`. The cell is born empty; the posting
/// turn writes the budget, requester, and spec; bidding writes the accepted
/// price; settle splits the budget — every step gated by the perpetual
/// `state_constraints` installed here for life.
pub fn job_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: JOB_FACTORY_VK,
        child_program_vk: Some(job_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(job_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: job_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![job_factory_descriptor()]
}

// =============================================================================
// Turn-builders — each carries a real Ed25519 signature
// =============================================================================

/// **post** — the requester opens a job: write `BUDGET`, `REQUESTER_HASH`,
/// `SPEC_HASH`, `STATE = POSTED`. The budget is the `line` a bid may draw
/// against; it is frozen by `WriteOnce` thereafter.
pub fn build_post_action(
    cclerk: &AppCipherclerk,
    job_cell: CellId,
    requester: &str,
    budget: u64,
    spec: &FieldElement,
) -> Action {
    let requester_h = field_from_bytes(requester.as_bytes());
    let budget_f = field_from_u64(budget);
    let effects = vec![
        Effect::SetField {
            cell: job_cell,
            index: REQUESTER_HASH_SLOT,
            value: requester_h,
        },
        Effect::SetField {
            cell: job_cell,
            index: BUDGET_SLOT,
            value: budget_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: SPEC_HASH_SLOT,
            value: *spec,
        },
        Effect::SetField {
            cell: job_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_POSTED),
        },
        Effect::EmitEvent {
            cell: job_cell,
            event: Event::new(symbol("job-posted"), vec![requester_h, budget_f]),
        },
    ];
    cclerk.make_action(job_cell, "post", effects)
}

/// **bid** — a provider bids `price` (must be `<= BUDGET`, the budget gate),
/// binds `PROVIDER_HASH`, advances `STATE -> BID`.
pub fn build_bid_action(
    cclerk: &AppCipherclerk,
    job_cell: CellId,
    provider: &str,
    price: u64,
) -> Action {
    let provider_h = field_from_bytes(provider.as_bytes());
    let price_f = field_from_u64(price);
    let effects = vec![
        Effect::SetField {
            cell: job_cell,
            index: PROVIDER_HASH_SLOT,
            value: provider_h,
        },
        Effect::SetField {
            cell: job_cell,
            index: BID_SLOT,
            value: price_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_BID),
        },
        Effect::EmitEvent {
            cell: job_cell,
            event: Event::new(symbol("job-bid"), vec![provider_h, price_f]),
        },
    ];
    cclerk.make_action(job_cell, "bid", effects)
}

/// **settle** — close the deal: `paid` to the provider, `refunded` to the
/// requester, advancing `STATE -> SETTLED`. The flashwell conservation caveat
/// (`paid + refunded == budget`) makes this atomic and value-neutral: a split
/// that does not balance is refused by the executor, never committed.
///
/// - Provider paid in full: `build_settle_action(.., bid, budget - bid)`.
/// - Full refund (job cancelled): `build_settle_action(.., 0, budget)`.
pub fn build_settle_action(
    cclerk: &AppCipherclerk,
    job_cell: CellId,
    paid: u64,
    refunded: u64,
) -> Action {
    let paid_f = field_from_u64(paid);
    let refunded_f = field_from_u64(refunded);
    let effects = vec![
        Effect::SetField {
            cell: job_cell,
            index: PAID_SLOT,
            value: paid_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: REFUNDED_SLOT,
            value: refunded_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SETTLED),
        },
        Effect::EmitEvent {
            cell: job_cell,
            event: Event::new(symbol("job-settled"), vec![paid_f, refunded_f]),
        },
    ];
    cclerk.make_action(job_cell, "settle", effects)
}

// =============================================================================
// Convenience encoders (mirror what the executor + CLI see)
// =============================================================================

/// `blake3(party)` — the value written into `REQUESTER_HASH_SLOT` /
/// `PROVIDER_HASH_SLOT`.
pub fn party_hash(party: &str) -> FieldElement {
    field_from_bytes(party.as_bytes())
}

/// The big-endian-padded amount field written into the value slots.
pub fn amount_field(amount: u64) -> FieldElement {
    field_from_u64(amount)
}

/// The state code field written into `STATE_SLOT`.
pub fn state_field(state: u64) -> FieldElement {
    field_from_u64(state)
}

/// `blake3` of the sealed job spec — the digest the requester commits at post.
/// Here we accept any payload and derive a stable 32-byte commitment.
pub fn spec_digest(payload: &[u8]) -> FieldElement {
    let mut h = blake3::Hasher::new_derive_key("dregg-compute-exchange job-spec v1");
    h.update(payload);
    let mut out = [0u8; 32];
    h.finalize_xof().fill(&mut out);
    out
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("compute-exchange")
        .slot("REQUESTER_HASH_SLOT", REQUESTER_HASH_SLOT as u64)
        .slot("PROVIDER_HASH_SLOT", PROVIDER_HASH_SLOT as u64)
        .slot("BUDGET_SLOT", BUDGET_SLOT as u64)
        .slot("BID_SLOT", BID_SLOT as u64)
        .slot("SPEC_HASH_SLOT", SPEC_HASH_SLOT as u64)
        .slot("PAID_SLOT", PAID_SLOT as u64)
        .slot("REFUNDED_SLOT", REFUNDED_SLOT as u64)
        .slot("STATE_SLOT", STATE_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&JOB_FACTORY_VK))
        .topic("POSTED", "job-posted")
        .topic("BID", "job-bid")
        .topic("SETTLED", "job-settled")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`]. Installs the job
/// factory descriptor and the job inspector. Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(job_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "compute-job".into(),
        descriptor: serde_json::json!({
            "component": "dregg-compute-job",
            "module": "/starbridge-apps/compute-exchange/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["requester_hash", "provider_hash", "budget", "bid", "spec_hash", "paid", "refunded", "state"],
            "slot_layout": {
                "requester_hash": REQUESTER_HASH_SLOT,
                "provider_hash":  PROVIDER_HASH_SLOT,
                "budget":         BUDGET_SLOT,
                "bid":            BID_SLOT,
                "spec_hash":      SPEC_HASH_SLOT,
                "paid":           PAID_SLOT,
                "refunded":       REFUNDED_SLOT,
                "state":          STATE_SLOT,
            },
            "state_codes": {
                "posted":  STATE_POSTED,
                "bid":     STATE_BID,
                "settled": STATE_SETTLED,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&job_child_program_vk()),
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context.
    // The factory + inspector are where SOUNDNESS lives (an over-budget bid / a
    // value-conjuring settle / a no-advance state are real executor refusals on the
    // seeded cell); the deos surface is the composition skin (per-viewer projection,
    // the cap∧state gated fires, the `dregg://` publish, the rehydratable snapshot,
    // the manifest).
    register_deos(ctx);

    factory_vk
}

// =============================================================================
// The deos-native surface — the COMPUTE JOB as a composed `DeosApp`.
// =============================================================================
//
// The lifecycle operations are ONE [`DeosApp`] ([`job_app`] below); the framework
// wires the rest — per-viewer projection, web-of-cells publish (the JOB cell IS a
// `dregg://` sturdyref), per-viewer rehydration, the generated
// `<dregg-affordance-surface>` component, and the manifest.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror escrow-market / supply-chain).
// The two state-advancing operations (`bid`, `settle`) are [`GatedAffordance`]s
// carrying a live-state PRECONDITION (a STATE check: `bid` needs POSTED, `settle`
// needs BID); the FULL job program ([`job_cell_program`], a method-dispatched
// `Cases` carrying BUDGET `FieldLteField(BID <= BUDGET)`, ACCEPTED `WriteOnce(BID)`,
// FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)` on settle + the universal
// `AffineLe(<= BUDGET)`, and LIFECYCLE `StrictMonotonic(STATE)`) is INSTALLED on the
// seeded job cell ([`seed_job`]) and RE-ENFORCED by the executor on every touching
// turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_bid`] / [`fire_settle`] then submit the FULL multi-effect turn (built
//      from the cell's LIVE state), and the executor RE-ENFORCES the installed
//      program — so an OVER-BUDGET bid (`FieldLteField`), a value-conjuring settle
//      (`AffineEq`/`AffineLe`), and a non-advancing/rewinding STATE (`StrictMonotonic`)
//      are REAL executor refusals in the SUBMISSION path — the half the floor's
//      `evaluate`-only tests never exercised through a real signed turn (see
//      `tests/deos_seam.rs`).

/// The compute-job rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the
/// roles the floor crate's cap-graph enforces:
///
///   - an OBSERVER (the public / an auditor watching the marketplace) holds
///     [`AuthRequired::Signature`] — the narrow read tier: `view_job` and nothing
///     else;
///   - a PROVIDER (the party offering compute) holds [`AuthRequired::Either`] — it
///     can `bid` (offer a price `<= BUDGET`) AND view;
///   - the REQUESTER (the party posting + settling) holds [`AuthRequired::None`]/root
///     — it can `settle` (split the budget) on top of everything a provider can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the observer ⊂ provider ⊂ requester ladder.
pub const OBSERVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The provider rights tier (sig-or-proof — bid + view). See [`OBSERVER_RIGHTS`].
pub const PROVIDER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The requester rights tier (root — settle + all). See [`OBSERVER_RIGHTS`].
pub const REQUESTER_RIGHTS: AuthRequired = AuthRequired::None;

/// The **life-of-cell job program** the executor re-enforces on every touching turn
/// — the canonical method-dispatched [`job_cell_program`] (`Always`-case
/// BUDGET/ACCEPTED/LIFECYCLE invariants + the settle-scoped FLASHWELL `AffineEq`).
/// This is the SAME program a factory-born job cell carries FOR LIFE (the one
/// `tests/factory_birth.rs` proves bites on the executor); installed by [`seed_job`]
/// so the gated fires re-enforce it.
pub fn job_program() -> CellProgram {
    job_cell_program()
}

/// The `bid` **live-state precondition** — the job must be POSTED (`STATE ==
/// POSTED`). A real [`CellProgram`] read against the cell's current state, so a
/// `bid` button is DARK on a not-yet-posted (or already-bid) job and LIT exactly
/// when the job is open for bids (the htmx tooth). This gates "may `bid` fire now";
/// the BUDGET bound (`FieldLteField(BID <= BUDGET)`) and the LIFECYCLE advance
/// (`StrictMonotonic(STATE)`) are the installed [`job_program`] the executor
/// re-enforces on the produced transition.
pub fn posted_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT as u8,
        value: field_from_u64(STATE_POSTED),
    }])
}

/// The `settle` **live-state precondition** — the job must be BID (`STATE == BID`).
/// So the `settle` button is DARK until a provider bids and LIT once bid (the htmx
/// tooth). The executor's installed FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)`
/// (the settlement conserves the budget) and `StrictMonotonic(STATE)` are the second
/// guard.
pub fn bid_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT as u8,
        value: field_from_u64(STATE_BID),
    }])
}

/// **The COMPUTE JOB as a composed [`DeosApp`]** — the whole interaction surface, on
/// the deos bones. The job cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Three operations on the JOB cell, on the observer ⊂ provider ⊂ requester rights
/// ladder:
///
///   - `view_job` — a cap-only affordance (an OBSERVER reads the job state):
///     `Signature`, an `EmitEvent`;
///   - `bid` — a [`GatedAffordance`] (the PROVIDER offers a price): `Either`, a
///     live-state PRECONDITION (the job is POSTED); the real fire ([`fire_bid`])
///     submits the FULL bid turn (PROVIDER_HASH + BID + STATE->BID), re-enforced by
///     the executor's installed BUDGET `FieldLteField(BID <= BUDGET)`;
///   - `settle` — a [`GatedAffordance`] (the REQUESTER splits the budget): `None`, a
///     live-state PRECONDITION (the job is BID); the real fire ([`fire_settle`]) reads
///     live `BID` + `BUDGET` and pays the provider IN FULL (PAID := BID, REFUNDED :=
///     BUDGET - BID, STATE->SETTLED), so the executor's installed FLASHWELL
///     `AffineEq(PAID + REFUNDED == BUDGET)` holds on the honest path.
///
/// The job cell is published into the web-of-cells at the observer tier and is
/// discoverable under `compute` / `marketplace`.
///
/// Seed the cell's program + posted state with [`seed_job`] so the gated fires have a
/// live state and the executor re-enforces the program.
pub fn job_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `view_job` — an observer reads the job state. Cap-only.
    let view = CellAffordance::new(
        "view_job",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-read"), vec![]),
        },
    );
    // `bid` — the PROVIDER offers a price. The GatedAffordance carries the DECISIVE
    // effect (the STATE->BID advance) as its surface representative AND a live-state
    // PRECONDITION ([`posted_precondition`]: the job is POSTED) — so the button is
    // dark before posting / after a bid and lit exactly while open. The actual fire
    // ([`fire_bid`]) submits the FULL bid turn ([`bid_effects`]: provider + price +
    // state + event), which the executor re-enforces the installed BUDGET on — so
    // `FieldLteField(BID <= BUDGET)` BITES: an over-budget bid is REFUSED.
    let bid = GatedAffordance::new(
        CellAffordance::new(
            "bid",
            PROVIDER_RIGHTS,
            Effect::SetField {
                cell,
                index: STATE_SLOT,
                value: field_from_u64(STATE_BID),
            },
        ),
        posted_precondition(),
    );
    // `settle` — the REQUESTER splits the budget. The decisive effect advances
    // STATE->SETTLED; gated on the BID precondition ([`bid_precondition`]). The
    // executor re-enforces the installed FLASHWELL `AffineEq(PAID + REFUNDED ==
    // BUDGET)` (a value-conjuring split is refused).
    let settle = GatedAffordance::new(
        CellAffordance::new(
            "settle",
            REQUESTER_RIGHTS,
            Effect::SetField {
                cell,
                index: STATE_SLOT,
                value: field_from_u64(STATE_SETTLED),
            },
        ),
        bid_precondition(),
    );

    DeosApp::builder("compute-exchange", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["compute".into(), "marketplace".into()])
        .cell(
            DeosCell::new(cell, "compute")
                .affordance(view)
                .gated(bid)
                .gated(settle)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the JOB cell** so the gated fires have live state + the program bites:
/// install the full [`job_program`] on the seeded job cell (so the executor
/// re-enforces it on every touching turn), then bind the posting genesis state
/// directly into the embedded ledger — bind `REQUESTER_HASH`, `BUDGET`
/// (`WriteOnce`, frozen after), `SPEC_HASH`, set `STATE = POSTED`, `BID = 0` (so the
/// `Always`-case invariants — `FieldLteField(BID <= BUDGET)` and the no-mint
/// `AffineLe` — already hold at the seeded state).
///
/// After seeding, the job is POSTED with a budget bound — a real `(old, new)`
/// baseline against which `bid` advances. Returns the bound `BUDGET` value.
pub fn seed_job(executor: &EmbeddedExecutor, requester: &str, budget: u64) -> u64 {
    let cell = executor.cell_id();
    executor.install_program(cell, job_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(REQUESTER_HASH_SLOT, field_from_bytes(requester.as_bytes()));
            c.state.set_field(BUDGET_SLOT, field_from_u64(budget));
            c.state
                .set_field(SPEC_HASH_SLOT, spec_digest(b"render-frame-batch"));
            c.state.set_field(BID_SLOT, field_from_u64(0));
            c.state.set_field(STATE_SLOT, field_from_u64(STATE_POSTED));
        }
    });
    budget
}

/// **`bid` effects** — the multi-effect bidding body: bind `PROVIDER_HASH`, write
/// `BID := price` (the budget draw, `<= BUDGET`), advance `STATE -> BID`, and emit
/// `job-bid`. This is the ONE coherent transition the installed invariants admit
/// (bid bounded by budget, state advancing). The deos `bid` gated affordance is the
/// cap∧state PRECONDITION face; THIS is the turn [`fire_bid`] submits.
pub fn bid_effects(cell: CellId, provider: &str, price: u64) -> Vec<Effect> {
    let provider_h = field_from_bytes(provider.as_bytes());
    let price_f = field_from_u64(price);
    vec![
        Effect::SetField {
            cell,
            index: PROVIDER_HASH_SLOT,
            value: provider_h,
        },
        Effect::SetField {
            cell,
            index: BID_SLOT,
            value: price_f,
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_BID),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-bid"), vec![provider_h, price_f]),
        },
    ]
}

/// **`settle` effects** — the multi-effect settle body: write `PAID := paid`,
/// `REFUNDED := refunded`, advance `STATE -> SETTLED`, and emit `job-settled`. The
/// FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)` requires `paid + refunded ==
/// budget`; the honest [`fire_settle`] reads live `BID` + `BUDGET` and pays the
/// provider IN FULL (`paid = bid`, `refunded = budget - bid`). THIS is the turn
/// [`fire_settle`] submits.
pub fn settle_effects(cell: CellId, paid: u64, refunded: u64) -> Vec<Effect> {
    let paid_f = field_from_u64(paid);
    let refunded_f = field_from_u64(refunded);
    vec![
        Effect::SetField {
            cell,
            index: PAID_SLOT,
            value: paid_f,
        },
        Effect::SetField {
            cell,
            index: REFUNDED_SLOT,
            value: refunded_f,
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SETTLED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-settled"), vec![paid_f, refunded_f]),
        },
    ]
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the amount registers the job stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Fire `bid`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the job
/// is POSTED), then the FULL multi-effect bid turn ([`bid_effects`]) the executor
/// re-enforces the job program on (`FieldLteField(BID <= BUDGET)` BITES — an
/// over-budget bid is REFUSED). The `price` is the provider's offer; the executor
/// refuses it if it breaches the budget. Anti-ghost both ways: a precondition miss
/// never submits; a program violation is a real executor refusal. Use [`seed_job`]
/// first.
pub fn fire_bid(
    app: &DeosApp,
    held: &AuthRequired,
    provider: &str,
    price: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    let provider = provider.to_string();
    cell.fire_gated_through_executor_with("bid", held, cipherclerk, executor, move |_live| {
        bid_effects(target, &provider, price)
    })
}

/// **Fire `settle`** — the deos cap∧state PRECONDITION gate (cap ⊇ None AND the job
/// is BID), then the FULL settle turn the executor re-enforces the job program on.
/// The settle effects read live `BID` + `BUDGET` and pay the provider IN FULL
/// (`PAID := BID`, `REFUNDED := BUDGET - BID`), so the FLASHWELL `AffineEq(PAID +
/// REFUNDED == BUDGET)` holds on the honest path — the conservation is computed from
/// the cell's own state, never conjured. `StrictMonotonic(STATE)` re-enforces the
/// one-way advance. Use after a successful [`fire_bid`].
pub fn fire_settle(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("settle", held, cipherclerk, executor, move |live| {
        // Read the live budget + accepted bid and pay the provider IN FULL —
        // conservation by construction: paid + refunded == budget
        // (paid = bid, refunded = budget - bid).
        let budget = field_to_u64(&live.fields[BUDGET_SLOT]);
        let bid = field_to_u64(&live.fields[BID_SLOT]);
        let refunded = budget.saturating_sub(bid);
        settle_effects(target, bid, refunded)
    })
}

/// **Mount the deos-native surface** ([`job_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the job
/// cell's program + posted state (so the gated fires bite), and fold the app into the
/// context's affordance registry ([`DeosApp::register`]). Returns the live
/// [`DeosApp`] (so a host can also [`DeosApp::mount`] its axum router /
/// [`DeosApp::publish_all`] into the web-of-cells).
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = job_app(ctx.cipherclerk(), ctx.executor());
    // Seed the job cell so the gated `bid` / `settle` fires have a live `(old, new)`
    // and the full job program (installed here) is re-enforced by the executor on
    // every touching turn.
    seed_job(ctx.executor(), "requester-corp", 1000);
    app.register(ctx);
    app
}

// =============================================================================
// Tests — the cell program in isolation
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::program::TransitionMeta;
    use dregg_cell::state::CellState;

    /// Evaluate the `Cases` program for a specific method (the program is
    /// method-dispatching, so a bare `evaluate` would default-deny).
    fn eval_for(
        program: &CellProgram,
        method: &str,
        new: &CellState,
        old: Option<&CellState>,
    ) -> Result<(), dregg_cell::ProgramError> {
        program.evaluate_with_meta(new, old, None, &TransitionMeta::new(symbol(method), 0))
    }

    fn empty() -> CellState {
        CellState::new(0)
    }

    fn posted(budget: u64) -> CellState {
        let mut s = empty();
        s.fields[REQUESTER_HASH_SLOT] = party_hash("requester-corp");
        s.fields[BUDGET_SLOT] = amount_field(budget);
        s.fields[SPEC_HASH_SLOT] = spec_digest(b"render-frame-batch");
        s.fields[STATE_SLOT] = state_field(STATE_POSTED);
        s
    }

    fn bidded(budget: u64, bid: u64) -> CellState {
        let mut s = posted(budget);
        s.fields[PROVIDER_HASH_SLOT] = party_hash("provider-pat");
        s.fields[BID_SLOT] = amount_field(bid);
        s.fields[STATE_SLOT] = state_field(STATE_BID);
        s.set_nonce(1);
        s
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            job_factory_descriptor().hash(),
            job_factory_descriptor().hash()
        );
    }

    #[test]
    fn factory_bakes_the_four_organ_caveats() {
        let d = job_factory_descriptor();
        // BUDGET: BID <= BUDGET.
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == BID_SLOT as u8 && *right_index == BUDGET_SLOT as u8
            )),
            "budget-gate caveat missing"
        );
        // ACCEPTED: WriteOnce(BID).
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c, StateConstraint::WriteOnce { index } if *index == BID_SLOT as u8
            )),
            "accepted-bid write-once caveat missing"
        );
        // FLASHWELL no-mint (executor-enforced, every turn):
        //   PAID + REFUNDED - BUDGET <= 0.
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c, StateConstraint::AffineLe { terms, c: k }
                    if *k == 0
                        && terms.contains(&(1, PAID_SLOT as u8))
                        && terms.contains(&(1, REFUNDED_SLOT as u8))
                        && terms.contains(&(-1, BUDGET_SLOT as u8))
            )),
            "flashwell no-mint caveat missing from the flat descriptor"
        );
        // FLASHWELL no-burn (settle-scoped, in the canonical program recipe):
        //   PAID + REFUNDED - BUDGET == 0.
        let has_settle_eq = match job_cell_program() {
            CellProgram::Cases(cases) => cases.iter().any(|case| {
                matches!(case.guard, TransitionGuard::MethodIs { method } if method == symbol("settle"))
                    && case.constraints.iter().any(|c| matches!(
                        c, StateConstraint::AffineEq { c: k, .. } if *k == 0
                    ))
            }),
            _ => false,
        };
        assert!(
            has_settle_eq,
            "flashwell no-burn equality missing from the settle case"
        );
        // LIFECYCLE: StrictMonotonic(STATE).
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c, StateConstraint::StrictMonotonic { index } if *index == STATE_SLOT as u8
            )),
            "lifecycle caveat missing"
        );
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&job_cell_program());
        assert_eq!(job_child_program_vk(), expected);
        assert_eq!(job_factory_descriptor().child_program_vk, Some(expected));
    }

    #[test]
    fn legal_post_and_bid_within_budget_succeed() {
        let program = job_cell_program();
        // post from empty
        assert!(eval_for(&program, "post", &posted(1000), Some(&empty())).is_ok());
        // bid 800 <= budget 1000
        let old = posted(1000);
        assert!(eval_for(&program, "bid", &bidded(1000, 800), Some(&old)).is_ok());
    }

    #[test]
    fn unknown_method_is_default_denied() {
        let program = job_cell_program();
        let err = eval_for(&program, "drain_budget", &posted(1000), Some(&empty()))
            .expect_err("an unknown method must be default-denied");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::NoTransitionCaseMatched
        ));
    }

    #[test]
    fn bid_over_budget_is_rejected_budget_gate() {
        // The provider tries to bid 1500 against a 1000 budget.
        let program = job_cell_program();
        let old = posted(1000);
        let err = eval_for(&program, "bid", &bidded(1000, 1500), Some(&old))
            .expect_err("a bid over the budget must be rejected — the BUDGET gate");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::FieldLteField { .. },
                    ..
                }
            ),
            "expected FieldLteField (bid <= budget) violation, got {err:?}"
        );
    }

    #[test]
    fn settle_must_conserve_the_budget_flashwell() {
        let program = job_cell_program();
        let mut old = bidded(1000, 800);
        old.set_nonce(2);

        // Conserving settlement (pay 800, refund 200 == budget 1000) is accepted.
        let mut ok = old.clone();
        ok.fields[PAID_SLOT] = amount_field(800);
        ok.fields[REFUNDED_SLOT] = amount_field(200);
        ok.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        assert!(eval_for(&program, "settle", &ok, Some(&old)).is_ok());

        // A split that MINTS value (900 + 200 > 1000) is rejected — caught by the
        // universally-true no-mint `AffineLe` invariant.
        let mut mint = old.clone();
        mint.fields[PAID_SLOT] = amount_field(900);
        mint.fields[REFUNDED_SLOT] = amount_field(200);
        mint.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        let err = eval_for(&program, "settle", &mint, Some(&old))
            .expect_err("a value-minting settlement must be rejected — the no-mint bound");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::AffineLe { .. },
                    ..
                }
            ),
            "expected AffineLe no-mint violation, got {err:?}"
        );

        // A split that BURNS value (700 + 200 < 1000) passes the no-mint `AffineLe`
        // but is rejected by the settle-scoped no-burn `AffineEq` — the exact
        // conservation the settle case adds on top of the universal invariant.
        let mut burn = old.clone();
        burn.fields[PAID_SLOT] = amount_field(700);
        burn.fields[REFUNDED_SLOT] = amount_field(200);
        burn.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        let err = eval_for(&program, "settle", &burn, Some(&old))
            .expect_err("a value-burning settlement must be rejected — the no-burn equality");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::AffineEq { .. },
                    ..
                }
            ),
            "expected AffineEq no-burn violation, got {err:?}"
        );
    }

    #[test]
    fn state_cannot_regress_lifecycle() {
        let program = job_cell_program();
        let mut old = bidded(1000, 800);
        old.set_nonce(2);
        let mut back = old.clone();
        back.fields[STATE_SLOT] = state_field(STATE_POSTED); // regress
        let err = eval_for(&program, "settle", &back, Some(&old))
            .expect_err("state regression must be rejected — the LIFECYCLE bound");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { .. },
                ..
            }
        ));
    }

    #[test]
    fn accepted_bid_cannot_be_overwritten() {
        let program = job_cell_program();
        let old = bidded(1000, 800);
        // try to renegotiate the accepted bid downward after acceptance
        let mut tamper = old.clone();
        tamper.fields[BID_SLOT] = amount_field(500);
        tamper.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        tamper.fields[PAID_SLOT] = amount_field(500);
        tamper.fields[REFUNDED_SLOT] = amount_field(500);
        let err = eval_for(&program, "settle", &tamper, Some(&old))
            .expect_err("overwriting the accepted bid must be rejected — WriteOnce");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { .. },
                ..
            }
        ));
    }
}
