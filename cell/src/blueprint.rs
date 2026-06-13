//! # Settlement-cell blueprints — the LAND-BEFORE-KILL replacements for the
//! escrow / obligation / bridge kernel-verb families (dregg3 reduction, W2).
//!
//! Per `metatheory/Dregg2/Substrate/VerbRegistry.lean`, the `Effect` families
//!
//! * `CreateEscrow / ReleaseEscrow / RefundEscrow` (+ the `Committed` trio),
//! * `CreateObligation / FulfillObligation / SlashObligation`,
//! * `BridgeLock / BridgeFinalize / BridgeCancel`
//!
//! are classified `factory`: their kernel verb arms DISSOLVE into factory-born
//! cells whose [`CellProgram`]s enforce the same safety, settled with surviving
//! verbs only (`CreateCellFromFactory` + `Transfer` + `SetField`). This module
//! is the Rust-runtime half of that dissolution: per-deal [`FactoryDescriptor`]s
//! whose `state_constraints` ARE the verified Lean state machines.
//!
//! ## Lean provenance (read these as the spec)
//!
//! | Blueprint                     | Lean module (proved keystones)        |
//! |-------------------------------|---------------------------------------|
//! | [`escrow_factory_descriptor`] | `Dregg2.Apps.EscrowFactory`           |
//! | [`obligation_factory_descriptor`] | `Dregg2.Apps.ObligationFactory`   |
//! | [`bridge_factory_descriptor`] | `Dregg2.Apps.BridgeCell`              |
//!
//! The Lean factories publish a PER-DEAL `FactoryEntry` (e.g.
//! `escrowFactoryEntry amount depositor beneficiary cond asset`) whose caveats
//! are the deal-term immutables + the no-double-resolve `admitTable`. We mirror
//! that exactly: each deal gets its own content-addressed descriptor whose
//! constraints bake the deal terms as literals. The locked VALUE lives in the
//! minted cell's own `balance` (funding it is an ordinary `Transfer` IN, settling
//! an ordinary `Transfer` OUT) — NO side-table, so escrow/obligation/bridge
//! conservation is the ordinary kernel move law.
//!
//! ## The shared shape (one state machine, three skins)
//!
//! All three families are conditional-settlement cells over the same 16-slot
//! schema ([`STATE_SLOT`] … [`WITNESS_SLOT`]) and the same lifecycle:
//!
//! ```text
//!   UNINIT (0, factory birth)
//!     │ open: write the deal terms + STATE := OPEN  (terms pinned to the
//!     │       descriptor's literals from this point on)
//!     ▼
//!   OPEN (1) ──resolve-A (witness gate)──▶ RESOLVED_A (2)   [terminal, inert]
//!     │
//!     └──resolve-B (time gate)──────────▶ RESOLVED_B (3)   [terminal, inert]
//! ```
//!
//! | family     | OPEN(1)   | RESOLVED_A(2) — witness-gated | RESOLVED_B(3) — time-gated |
//! |------------|-----------|-------------------------------|----------------------------|
//! | escrow     | open      | released (→ beneficiary)      | refunded (→ depositor)     |
//! | obligation | open      | fulfilled (bond → obligor)    | slashed (bond → obligee)   |
//! | bridge     | locked    | finalized (→ pot)             | cancelled (→ originator)   |
//!
//! (The Lean modules use `0/1/2` for open/resolved-A/resolved-B; the runtime
//! shifts by one because a factory-born Rust cell starts with all-zero slots
//! before its deal terms are written — `UNINIT` is the pre-open birth state.
//! The TRANSITIONS are isomorphic; the terminal states are stricter here:
//! a resolved cell is fully inert, so value can never be stranded into it.)
//!
//! ## What the installed program enforces (the executor checks it on EVERY
//! turn that touches the cell — see `turn/src/executor/execute_tree.rs`)
//!
//! 1. **Deal-term integrity** — once out of `UNINIT`, every term slot must
//!    equal the descriptor's published literal (`AnyOf[state==UNINIT, slot==lit]`,
//!    the runtime mirror of the Lean `Immutable` caveats + `initialFields`).
//! 2. **No-double-resolve** — `AllowedTransitions` admits only
//!    `(UNINIT,UNINIT), (UNINIT,OPEN), (OPEN,OPEN), (OPEN,A), (OPEN,B)`;
//!    terminal states have no outgoing (or self) rows, so ANY touch of a
//!    resolved cell is rejected (Lean `no_double_resolve`).
//! 3. **Resolve-A requires the condition witness** — entering RESOLVED_A
//!    requires `WITNESS_SLOT == condition` in the same post-state (Lean
//!    `release_requires_condition` / `fulfil_requires_condition` /
//!    `finalize_requires_finality_witness`).
//! 4. **Resolve-B requires the deadline** — entering RESOLVED_B requires
//!    `block_height >= timeout` (escrow/bridge: only when a nonzero timeout
//!    is published; obligation: always — a zero deadline is rejected at
//!    descriptor build). The Lean obligation models the deadline as a witness
//!    equality (`slash_requires_deadline`); the runtime strengthens this to a
//!    real height gate, matching the verb-era `timeout_height` semantics.
//! 5. **Obligation only: no slash-with-condition** — entering SLASHED with
//!    `WITNESS_SLOT == condition` is rejected (Lean
//!    `slash_rejects_when_condition_met`).
//!
//! ## What the program CANNOT see (expressibility limits, by design honesty)
//!
//! * The cell `balance` is sealed (not one of the 16 slots), so "resolve drains
//!   the full balance" and "the payout goes to the published counterparty" are
//!   NOT program-enforced; they are enforced by the SDK builders
//!   (`dregg_sdk::factories`) constructing the only sensible turn, and by the
//!   kernel move law (a `Transfer` conserves and fail-closes). This mirrors the
//!   Lean contracts, where the settle target is an argument of
//!   `escrowRelease`/`obSettle` rather than a checked field.
//! * The committed-escrow knowledge gate (release on a HASH-PREIMAGE reveal)
//!   is now EXPRESSIBLE: `PreimageGate` is a `SimpleStateConstraint`
//!   (`docs/CELL-PROGRAM-LANGUAGE.md` §4), so `when_state(RESOLVED_A,
//!   PreimageGate { commitment_index: CONDITION_SLOT, .. })` composes — see
//!   `cell::program::tests::preimage_gate_composes_under_state_guard` and the
//!   Lean `committedRelease` twin (`Dregg2/Exec/Program.lean`). The cleartext
//!   witness-equality gate below remains the Lean `EscrowFactory` contract;
//!   a committed-deal blueprint is the natural next variant.
//! * The "resolve drains the full balance" tooth is likewise now expressible
//!   (`BalanceLte { max: 0 }` under the terminal-state guards — the
//!   `balance_atoms_see_own_balance` pin). The published settlement
//!   blueprints keep the Lean-twin constraint set verbatim; adding the drain
//!   tooth is a descriptor evolution to land together with its Lean keystone
//!   (one semantics, both sides — see `docs/CELL-PROGRAM-LANGUAGE.md` §9).

use crate::cell::CellMode;
use crate::factory::{CapTarget, CapTemplate, ChildVkStrategy, FactoryDescriptor};
use crate::permissions::AuthRequired;
use crate::program::{CellProgram, SimpleStateConstraint, StateConstraint, field_from_u64};
use crate::state::{FIELD_ZERO, FieldElement};

// =============================================================================
// Shared slot schema (all three settlement families)
// =============================================================================

/// Lifecycle state code slot (see the state table in the module docs).
pub const STATE_SLOT: u8 = 0;
/// The published value of the deal: escrow amount / obligation bond /
/// bridge-locked amount, big-endian u64 in the last 8 bytes
/// ([`field_from_u64`]). Term-pinned once OPEN.
pub const VALUE_SLOT: u8 = 1;
/// First party: escrow depositor / obligation obligor / bridge originator
/// (any 32-byte identity encoding — typically a `CellId` or a BLAKE3 hash).
/// Term-pinned once OPEN.
pub const PARTY_A_SLOT: u8 = 2;
/// Second party: escrow beneficiary / obligation obligee / bridge pot.
/// Term-pinned once OPEN.
pub const PARTY_B_SLOT: u8 = 3;
/// The resolve-A condition: escrow condition / obligation condition /
/// bridge finality witness. Must be nonzero (a zero condition would make the
/// untouched witness slot satisfy the gate). Term-pinned once OPEN.
pub const CONDITION_SLOT: u8 = 4;
/// The resolve-B height gate: escrow refund timeout / obligation slash
/// deadline / bridge cancel timeout (block height, big-endian u64).
/// `0` = no time gate (escrow/bridge only). Term-pinned once OPEN.
pub const DEADLINE_SLOT: u8 = 5;
/// Scratch witness slot: the resolving turn writes the condition witness here.
/// Unconstrained outside the resolve gates.
pub const WITNESS_SLOT: u8 = 6;

/// Birth state of a factory-born cell (all slots zero, terms not yet written).
pub const STATE_UNINIT: u64 = 0;
/// The deal is open/locked: terms pinned, value may be funded in.
pub const STATE_OPEN: u64 = 1;
/// Witness-gated terminal: released / fulfilled / finalized.
pub const STATE_RESOLVED_A: u64 = 2;
/// Time-gated terminal: refunded / slashed / cancelled.
pub const STATE_RESOLVED_B: u64 = 3;

// =============================================================================
// Errors
// =============================================================================

/// A deal-term set the blueprint refuses to publish (fail-closed at build).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlueprintError {
    /// The condition is the all-zero field element. A fresh cell's witness
    /// slot is zero, so a zero condition would let resolve-A commit without
    /// any witness being exhibited. Rejected at build (fail-closed).
    ZeroCondition,
    /// An obligation with `deadline == 0` would make the slash leg
    /// time-ungated; the Lean contract (`slash_requires_deadline`) requires a
    /// real deadline. Rejected at build (fail-closed).
    ZeroDeadline,
    /// A trustline with `line == 0` is undrawable and its all-zero terms are
    /// indistinguishable from an unborn cell. Rejected at build (fail-closed).
    ZeroLine,
    /// A trustline party identity is the all-zero field — settlement would
    /// target the zero cell. Rejected at build (fail-closed).
    ZeroParty,
    /// A channel group with a zero admin key would have NO governor: every
    /// membership/epoch/key write would refuse forever (`SenderIs` against
    /// the zero key never matches a real sender). Rejected at build.
    ZeroAdmin,
    /// A channel group tag of zero is indistinguishable from an unborn
    /// cell's empty slot. Rejected at build (fail-closed).
    ZeroTag,
}

impl std::fmt::Display for BlueprintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlueprintError::ZeroCondition => write!(
                f,
                "settlement condition must be nonzero (a zero condition is satisfied by the untouched witness slot)"
            ),
            BlueprintError::ZeroDeadline => {
                write!(f, "obligation deadline must be a nonzero block height")
            }
            BlueprintError::ZeroLine => {
                write!(f, "trustline line ceiling must be nonzero")
            }
            BlueprintError::ZeroParty => {
                write!(
                    f,
                    "trustline issuer/holder identities must be nonzero fields"
                )
            }
            BlueprintError::ZeroAdmin => {
                write!(f, "channel admin key must be a nonzero field")
            }
            BlueprintError::ZeroTag => {
                write!(f, "channel group tag must be nonzero")
            }
        }
    }
}

impl std::error::Error for BlueprintError {}

// =============================================================================
// The shared constraint generator
// =============================================================================

/// Internal: the family-specific knobs over the shared settlement machine.
struct SettlementSpec {
    /// Deal value (u64, stored big-endian in `VALUE_SLOT`).
    value: u64,
    /// Party A identity field (depositor / obligor / originator).
    party_a: FieldElement,
    /// Party B identity field (beneficiary / obligee / pot).
    party_b: FieldElement,
    /// The resolve-A condition (must be nonzero).
    condition: FieldElement,
    /// The resolve-B height gate. `None` = resolve-B is time-ungated
    /// (mirrors the Lean escrow/bridge, whose refund/cancel only require OPEN).
    deadline: Option<u64>,
    /// Obligation twist: resolve-B (slash) must NOT exhibit the condition
    /// witness (Lean `slash_rejects_when_condition_met`).
    resolve_b_rejects_condition: bool,
}

/// `state == code` as a [`SimpleStateConstraint`] (big-endian u64 encoding).
fn state_is(code: u64) -> SimpleStateConstraint {
    SimpleStateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(code),
    }
}

/// Pin `slot` to `lit` whenever the cell has left `UNINIT`:
/// `AnyOf[ state == UNINIT, slot == lit ]`. The runtime mirror of the Lean
/// per-deal `Immutable` caveat + published `initialFields` — once the deal is
/// open, the term can never differ from the descriptor's literal.
fn pin_term(slot: u8, lit: FieldElement) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            state_is(STATE_UNINIT),
            SimpleStateConstraint::FieldEquals {
                index: slot,
                value: lit,
            },
        ],
    }
}

/// `state == gate_state ⇒ consequent`, encoded as `AnyOf[¬(state==gate), consequent]`.
fn when_state(gate_state: u64, consequent: SimpleStateConstraint) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(state_is(gate_state))),
            consequent,
        ],
    }
}

/// The full settlement constraint set for one deal. See the module docs for
/// the five enforcement teeth; every constraint tolerates the all-zero birth
/// state (the factory mints with no `initial_fields`; the OPEN turn writes the
/// terms and the pins begin to bite in that same post-state).
fn settlement_constraints(spec: &SettlementSpec) -> Vec<StateConstraint> {
    let mut cs = vec![
        // ── 1. deal-term integrity (Lean: the five Immutable caveats) ──
        pin_term(VALUE_SLOT, field_from_u64(spec.value)),
        pin_term(PARTY_A_SLOT, spec.party_a),
        pin_term(PARTY_B_SLOT, spec.party_b),
        pin_term(CONDITION_SLOT, spec.condition),
        pin_term(DEADLINE_SLOT, field_from_u64(spec.deadline.unwrap_or(0))),
        // ── 2. the state machine (Lean: admitTable [(open,A),(open,B)]) ──
        // Terminal states have NO row: a resolved cell is inert (any touch,
        // including a second resolve or a transfer into it, is rejected) —
        // the no-double-resolve teeth.
        StateConstraint::AllowedTransitions {
            slot_index: STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_RESOLVED_A)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_RESOLVED_B)),
            ],
        },
        // ── 3. resolve-A requires the condition witness ──
        // (Lean: release_requires_condition / fulfil_requires_condition /
        //  finalize_requires_finality_witness — witness = condition equality.)
        when_state(
            STATE_RESOLVED_A,
            SimpleStateConstraint::FieldEquals {
                index: WITNESS_SLOT,
                value: spec.condition,
            },
        ),
    ];
    // ── 4. resolve-B height gate (when a deadline is published) ──
    if let Some(deadline) = spec.deadline {
        cs.push(when_state(
            STATE_RESOLVED_B,
            SimpleStateConstraint::TemporalGate {
                not_before: Some(deadline),
                not_after: None,
            },
        ));
    }
    // ── 5. obligation only: a slash that exhibits the condition is rejected ──
    if spec.resolve_b_rejects_condition {
        cs.push(when_state(
            STATE_RESOLVED_B,
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: WITNESS_SLOT,
                value: spec.condition,
            })),
        ));
    }
    cs
}

/// Build the per-deal descriptor around a constraint set. The factory VK is
/// content-addressed over the constraint set (which itself bakes every deal
/// term), so two distinct deals get distinct factories and the same deal is
/// re-derivable by any party — the runtime mirror of the Lean content-addressed
/// `escrowRegistry vk …` key. `creation_budget = 1`: a deal descriptor births
/// exactly ONE cell.
fn settlement_descriptor(domain_tag: &str, constraints: Vec<StateConstraint>) -> FactoryDescriptor {
    let program = CellProgram::Predicate(constraints.clone());
    let child_vk = crate::factory::canonical_program_vk(&program);
    let mut hasher = blake3::Hasher::new_derive_key(domain_tag);
    let encoded = postcard::to_allocvec(&constraints).unwrap_or_default();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
    let factory_vk = *hasher.finalize().as_bytes();
    FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(child_vk),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(child_vk))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: constraints,
        default_mode: CellMode::Hosted,
        creation_budget: Some(1),
    }
}

// =============================================================================
// Escrow — Dregg2.Apps.EscrowFactory
// =============================================================================

/// The published deal terms of one escrow (the Lean
/// `escrowFactoryEntry amount depositor beneficiary cond asset`; the runtime
/// has a single native asset — the cell balance — so there is no `asset` term).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EscrowTerms {
    /// Locked amount. Held in the escrow cell's own `balance` after funding.
    pub amount: u64,
    /// Depositor identity (refund target), 32-byte encoding.
    pub depositor: FieldElement,
    /// Beneficiary identity (release target), 32-byte encoding.
    pub beneficiary: FieldElement,
    /// Release condition: the value the releasing turn must exhibit in
    /// [`WITNESS_SLOT`]. Must be nonzero. (Lean keystone (c):
    /// `release_requires_condition`.)
    pub condition: FieldElement,
    /// Refund timeout (block height). `0` = refund-any-time-while-open, which
    /// is exactly the Lean `escrowRefund` (gated only on OPEN); nonzero
    /// mirrors the verb-era `CreateEscrow.timeout_height`.
    pub timeout_height: u64,
}

/// The escrow constraint set for one deal (see module docs teeth 1–4).
///
/// Safety contract (proved on the Lean twin `Dregg2.Apps.EscrowFactory`):
/// conservation (the value moves by ordinary `Transfer`, keystone a),
/// no-double-resolve (keystone b), release-requires-condition (keystone c),
/// open-escrow-settleable (keystone d, witnessed by the e2e tests).
pub fn escrow_state_constraints(
    terms: &EscrowTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.condition == FIELD_ZERO {
        return Err(BlueprintError::ZeroCondition);
    }
    Ok(settlement_constraints(&SettlementSpec {
        value: terms.amount,
        party_a: terms.depositor,
        party_b: terms.beneficiary,
        condition: terms.condition,
        deadline: (terms.timeout_height != 0).then_some(terms.timeout_height),
        resolve_b_rejects_condition: false,
    }))
}

/// The `CellProgram` installed on the escrow cell for its whole life.
pub fn escrow_cell_program(terms: &EscrowTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(escrow_state_constraints(terms)?))
}

/// **The escrow factory (per-deal, content-addressed)** — the land-before-kill
/// replacement for `Effect::{CreateEscrow, ReleaseEscrow, RefundEscrow}` (and
/// the `Committed` trio, modulo the preimage-gate gap noted in the module
/// docs). Lean twin: `Dregg2.Apps.EscrowFactory.escrowFactoryEntry`.
pub fn escrow_factory_descriptor(terms: &EscrowTerms) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:escrow-factory v1",
        escrow_state_constraints(terms)?,
    ))
}

// =============================================================================
// Obligation — Dregg2.Apps.ObligationFactory
// =============================================================================

/// The published deal terms of one bonded proof obligation (the Lean
/// `obligationFactory bond obligor obligee cond deadline`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObligationTerms {
    /// Bond amount, held in the obligation cell's own `balance` after posting.
    pub bond: u64,
    /// Obligor identity (the bonded party; fulfilment returns the bond here).
    pub obligor: FieldElement,
    /// Obligee identity (slashing forfeits the bond here).
    pub obligee: FieldElement,
    /// Discharge condition: the witness a fulfilling turn must exhibit in
    /// [`WITNESS_SLOT`]. Must be nonzero. (Lean `fulfil_requires_condition`.)
    pub condition: FieldElement,
    /// Slash deadline (block height, must be nonzero): slashing is admitted
    /// only at `height >= deadline`. (Strengthens the Lean witness-equality
    /// deadline `slash_requires_deadline` into a real height gate.)
    pub deadline_height: u64,
}

/// The obligation constraint set for one deal (module-docs teeth 1–5; tooth 5
/// is the Lean `slash_rejects_when_condition_met` anti-condition gate).
pub fn obligation_state_constraints(
    terms: &ObligationTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.condition == FIELD_ZERO {
        return Err(BlueprintError::ZeroCondition);
    }
    if terms.deadline_height == 0 {
        return Err(BlueprintError::ZeroDeadline);
    }
    Ok(settlement_constraints(&SettlementSpec {
        value: terms.bond,
        party_a: terms.obligor,
        party_b: terms.obligee,
        condition: terms.condition,
        deadline: Some(terms.deadline_height),
        resolve_b_rejects_condition: true,
    }))
}

/// The `CellProgram` installed on the obligation cell for its whole life.
pub fn obligation_cell_program(terms: &ObligationTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(obligation_state_constraints(terms)?))
}

/// **The obligation factory (per-deal, content-addressed)** — the
/// land-before-kill replacement for `Effect::{CreateObligation,
/// FulfillObligation, SlashObligation}`. Lean twin:
/// `Dregg2.Apps.ObligationFactory.obligationFactory`.
pub fn obligation_factory_descriptor(
    terms: &ObligationTerms,
) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:obligation-factory v1",
        obligation_state_constraints(terms)?,
    ))
}

// =============================================================================
// Bridge — Dregg2.Apps.BridgeCell
// =============================================================================

/// The published terms of one cross-domain bridge lock (the Lean
/// `bridgeFactoryEntry amount originator pot finalityWitness asset` — the
/// BridgeCell module instantiates the escrow shape with bridge readings:
/// locked/finalized/cancelled).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BridgeTerms {
    /// Locked amount, held in the bridge cell's own `balance` after locking.
    pub amount: u64,
    /// Originator identity (cancel refunds here).
    pub originator: FieldElement,
    /// Pot identity (finalize delivers here).
    pub pot: FieldElement,
    /// Finality witness the finalizing turn must exhibit in [`WITNESS_SLOT`].
    /// Must be nonzero. (Lean `finalize_requires_finality_witness`.)
    pub finality_witness: FieldElement,
    /// Cancel timeout (block height). `0` = cancel-any-time-while-locked
    /// (exactly the Lean `locked_cancellable`); nonzero mirrors the verb-era
    /// `BridgeLock.timeout_height`.
    pub timeout_height: u64,
}

/// The bridge-cell constraint set for one lock (module-docs teeth 1–4).
pub fn bridge_state_constraints(
    terms: &BridgeTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.finality_witness == FIELD_ZERO {
        return Err(BlueprintError::ZeroCondition);
    }
    Ok(settlement_constraints(&SettlementSpec {
        value: terms.amount,
        party_a: terms.originator,
        party_b: terms.pot,
        condition: terms.finality_witness,
        deadline: (terms.timeout_height != 0).then_some(terms.timeout_height),
        resolve_b_rejects_condition: false,
    }))
}

/// The `CellProgram` installed on the bridge cell for its whole life.
pub fn bridge_cell_program(terms: &BridgeTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(bridge_state_constraints(terms)?))
}

/// **The bridge-cell factory (per-deal, content-addressed)** — the
/// land-before-kill replacement for `Effect::{BridgeLock, BridgeFinalize,
/// BridgeCancel}` (`BridgeMint` SURVIVES as a shield verb and is untouched).
/// Lean twin: `Dregg2.Apps.BridgeCell.bridgeFactoryEntry`.
pub fn bridge_factory_descriptor(terms: &BridgeTerms) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:bridge-factory v1",
        bridge_state_constraints(terms)?,
    ))
}

// =============================================================================
// Trustline — Dregg2.Apps.Trustline (the ORGANS §1 weld)
// =============================================================================

/// Trustline slot 0 — lifecycle state ([`STATE_UNINIT`] → [`STATE_OPEN`] →
/// [`TL_STATE_CLOSED`]).
pub const TL_STATE_SLOT: u8 = 0;
/// Trustline slot 1 — `line_ceiling`: the extended line N (Lean
/// `Line.ceiling`, the attenuation bound). Term-pinned once OPEN
/// (`ceiling_immutable_forever`).
pub const TL_CEILING_SLOT: u8 = 1;
/// Trustline slot 2 — issuer identity (the party whose escrowed well backs
/// draws; 32-byte `CellId` encoding). Term-pinned once OPEN.
pub const TL_ISSUER_SLOT: u8 = 2;
/// Trustline slot 3 — holder identity (the counterparty who may exercise the
/// line; 32-byte `CellId` encoding). Term-pinned once OPEN.
pub const TL_HOLDER_SLOT: u8 = 3;
/// Trustline slot 4 — `drawn`: the shared counter (Lean `Line.drawn` =
/// `BudgetSlice.spent`). Up on draw, down on repay; bounded by the ceiling
/// for the cell's whole life (`trustline_within_line_forever`).
pub const TL_DRAWN_SLOT: u8 = 4;
/// Trustline slot 5 — `settled`: cumulative drawn value already redeemed to
/// the holder by epoch settlement (`rebalance_budgets` applied as a ledger
/// move). Monotonic, never exceeds `drawn` — settled credit cannot be
/// repaid back, and the payout invariant `settled ≤ drawn ≤ ceiling` is the
/// escrow-solvency proof (payouts can never exceed the funded line).
pub const TL_SETTLED_SLOT: u8 = 5;
/// Trustline slot 6 — last draw digest (audit word; the per-draw anti-replay
/// REGISTRY is the Stingray slice's `debits` list + the node's persistent
/// digest set — see `no_double_draw_forever`).
pub const TL_DIGEST_SLOT: u8 = 6;

/// Terminal state of a closed trustline (inert — no row out of CLOSED in the
/// transition table, the settlement-family no-double-resolve shape).
pub const TL_STATE_CLOSED: u64 = 2;

/// The published terms of one directional trustline: issuer extends holder a
/// line of `line` (Lean `Dregg2.Apps.Trustline.Line.init`). DIRECTIONAL —
/// the A→B line is a different cell from B→A; "mutual" credit is the pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustlineTerms {
    /// The extended line N — the attenuation bound (`Line.ceiling`). The
    /// open flow escrows exactly this amount in the trustline cell's own
    /// balance (fullReserve backing), so the line is solvent by construction.
    pub line: u64,
    /// Issuer identity (32-byte `CellId` encoding) — whose escrow backs draws.
    pub issuer: FieldElement,
    /// Holder identity (32-byte `CellId` encoding) — who may exercise the line.
    pub holder: FieldElement,
}

/// The trustline constraint set for one line. The Lean keystones each
/// constraint realizes (`metatheory/Dregg2/Apps/Trustline.lean`):
///
/// 1. term pins on ceiling/issuer/holder — `ceiling_immutable_forever` (and
///    the parties are immutable registers, design doc §3);
/// 2. `AllowedTransitions` — OPEN is the live state; CLOSED is terminal and
///    inert (no row out), the settlement-family no-double-resolve shape;
/// 3. `FieldLteField(drawn ≤ ceiling)` — `trustline_within_line_forever` /
///    `draw_within_line` (the `boundedBy` ceiling, executor-enforced on
///    EVERY turn that touches the cell);
/// 4. `Monotonic(settled)` + `FieldLteField(settled ≤ drawn)` — settlement
///    only redeems what was actually drawn, exactly once (the
///    `settlePay_conserves_hard` leg: combined with tooth 3, cumulative
///    payouts ≤ ceiling = the escrowed balance, so the escrow is solvent at
///    every reachable state).
///
/// Fails closed on a zero line (an undrawable line whose all-zero terms are
/// indistinguishable from an unborn cell) and zero party identities (a zero
/// holder would make settlement target the zero cell).
pub fn trustline_state_constraints(
    terms: &TrustlineTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.line == 0 {
        return Err(BlueprintError::ZeroLine);
    }
    if terms.issuer == FIELD_ZERO || terms.holder == FIELD_ZERO {
        return Err(BlueprintError::ZeroParty);
    }
    Ok(vec![
        // ── 1. term integrity (Lean: immutable ceiling + party registers) ──
        pin_term(TL_CEILING_SLOT, field_from_u64(terms.line)),
        pin_term(TL_ISSUER_SLOT, terms.issuer),
        pin_term(TL_HOLDER_SLOT, terms.holder),
        // ── 2. the lifecycle (CLOSED is terminal/inert) ──
        StateConstraint::AllowedTransitions {
            slot_index: TL_STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(TL_STATE_CLOSED)),
            ],
        },
        // ── 3. BOUNDED BY THE LINE (trustline_within_line_forever) ──
        StateConstraint::FieldLteField {
            left_index: TL_DRAWN_SLOT,
            right_index: TL_CEILING_SLOT,
        },
        // ── 4. settlement teeth (monotone redemption, never beyond drawn) ──
        StateConstraint::Monotonic {
            index: TL_SETTLED_SLOT,
        },
        StateConstraint::FieldLteField {
            left_index: TL_SETTLED_SLOT,
            right_index: TL_DRAWN_SLOT,
        },
    ])
}

/// The `CellProgram` installed on the trustline cell for its whole life.
pub fn trustline_cell_program(terms: &TrustlineTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(trustline_state_constraints(terms)?))
}

/// **The trustline factory (per-line, content-addressed)** — the cell shape
/// of docs/TRUSTLINES.md §3, Lean twin `Dregg2.Apps.Trustline`. Like the
/// settlement families, each line gets its own descriptor whose constraints
/// bake the terms as literals; the escrowed value lives in the cell's own
/// `balance` (funding and settling are ordinary conserving `Transfer`s).
pub fn trustline_factory_descriptor(
    terms: &TrustlineTerms,
) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:trustline-factory v1",
        trustline_state_constraints(terms)?,
    ))
}

// =============================================================================
// Channel group — the ORGANS §4 weld (the group-key lift)
// =============================================================================
//
// A group is a CELL: membership state and the group-key epoch commitment live
// on-cell; joins/removals are ordinary turns under the group's program, so
// the whole governance algebra applies to membership. Message bodies NEVER
// touch the chain — control plane on-cell, data plane ciphertext over any
// transport (mailboxes, SSE, captp store-and-forward).
//
// ## THE KEYSTONE — epoch unification
//
// The group's key epoch and the capability freshness epoch are THE SAME
// counter, enforced from two sides:
//
// * **Slot side (program-enforced, this module):** the constraint triple
//   below makes "remove + rekey are ONE turn" a *program* fact —
//   1. membership-root change ⇒ the epoch slot strictly increases,
//   2. key-commitment change ⇒ the epoch slot strictly increases,
//   3. epoch-slot change ⇒ the key commitment is REWRITTEN
//      (`AnyOf[Immutable{epoch}, Not(Immutable{key_commit})]` — the Heyting
//      `Not` is exactly "this slot changed").
//   So the same turn that drops a member MUST bump the epoch and MUST commit
//   a fresh key — a membership change with a stale key is UNSAT.
// * **Capability side (executor-enforced, `turn/src/executor/apply.rs`
//   R7 epoch-at-retrieval):** group-held capabilities are minted with
//   `stored_epoch: Some(e)` against the group cell; exercise refuses
//   (`TurnError::CapabilityStale`) once the group cell's `delegation_epoch`
//   advances past `e`. The canonical epoch-step turn (see
//   `dregg_sdk::channels` / `node/src/channels_service.rs`) carries a
//   `RevokeDelegation{ child: epoch_anchor }` effect — the one verb that
//   bumps `delegation_epoch` — so BOTH counters step in the SAME atomic
//   turn: removing a member ends their forward-read ability (rekey) and
//   their group-held capabilities (freshness) in one epoch step.
//
// ## Honest residue (named, loud)
//
// A cell program cannot READ `delegation_epoch` (it sees slots only), so
// "epoch slot ≡ delegation_epoch" is carried by the canonical turn builders
// (SDK + node service, tested both sides) rather than by the program. The
// closure lane is a program atom that mirrors the cell's delegation epoch
// into the EvalContext (an executor + Lean `Exec.Program` change — the
// executor lane owns those files). Until then a divergence is detectable by
// any member (`epoch slot ≠ delegation_epoch` is loud) and the slot teeth
// above still force rekey-on-removal.
//
// ## Key schedule (deliberately NOT RFC 9420 — yet)
//
// The cell only ever sees COMMITMENTS, so the key schedule is swappable
// without touching this blueprint. The shipped schedule
// (`dregg_sdk::channels`) is sender-keys style: a fresh random 32-byte group
// key per epoch, sealed per-member over the existing seal-pair machinery
// (X25519 → HKDF → ChaCha20-Poly1305, `dregg_captp::store_forward`) — O(n)
// rekey, correct forward darkness. RFC 9420 MLS (TreeKEM, O(log n) rekey,
// PCS ratchet) is the named successor substrate; it replaces the FAN-OUT
// only — the on-cell interface (membership root, epoch counter, key
// commitment) is UNCHANGED.

/// Channel slot 0 — lifecycle state ([`STATE_UNINIT`] → [`STATE_OPEN`] →
/// [`CH_STATE_CLOSED`]).
pub const CH_STATE_SLOT: u8 = 0;
/// Channel slot 1 — the openable membership commitment: a domain-tagged
/// BLAKE3 hash over the SORTED member-leaf set ([`channel_member_root`]) —
/// the `sdk/src/mailbox.rs` slot-5 sender-set shape. Anyone holding the
/// open set can recompute it; a stale or foreign set fails closed.
pub const CH_MEMBER_ROOT_SLOT: u8 = 1;
/// Channel slot 2 — THE epoch counter (big-endian u64): the group-key epoch
/// AND the capability freshness epoch (the keystone unification).
pub const CH_EPOCH_SLOT: u8 = 2;
/// Channel slot 3 — the epoch key commitment
/// ([`channel_key_commitment`]`(epoch, key)`). The cell sees only this
/// commitment; the key itself is sealed member-to-member off-cell.
pub const CH_KEY_COMMIT_SLOT: u8 = 3;
/// Channel slot 4 — the governance identity: the admin public key whose
/// signature gates membership/epoch/key writes (term-pinned once OPEN).
pub const CH_ADMIN_SLOT: u8 = 4;
/// Channel slots 5/6 — application slots (unconstrained by this blueprint;
/// reserved for the M-of-N council-approval successor, see
/// [`channel_state_constraints`] docs).
pub const CH_APP_SLOT_A: u8 = 5;
/// See [`CH_APP_SLOT_A`].
pub const CH_APP_SLOT_B: u8 = 6;
/// Channel slot 7 — the group tag (term-pinned): disambiguates two groups
/// under the same admin and content-addresses the per-group factory.
pub const CH_TAG_SLOT: u8 = 7;

/// Terminal state of a closed channel (inert — no row out of CLOSED).
pub const CH_STATE_CLOSED: u64 = 2;

/// The published terms of one channel group: the governance admin key + the
/// group tag. Membership/epoch/key are LIVE state (not terms) — they change
/// under the program's teeth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChannelTerms {
    /// Admin public key (32 bytes): the `SenderIs` governance gate over
    /// membership, epoch, key-commitment, and lifecycle writes. May be any
    /// key the deployment treats as the group's governor (an operator key,
    /// or a council-held key).
    pub admin: FieldElement,
    /// Group tag (nonzero): names THIS group among the admin's groups and
    /// content-addresses the per-group factory.
    pub tag: FieldElement,
}

/// Domain tag for [`channel_member_leaf`].
const CHANNEL_MEMBER_LEAF_DOMAIN: &str = "dregg-channel-member-leaf-v1";
/// Domain tag for [`channel_member_root`].
const CHANNEL_MEMBER_ROOT_DOMAIN: &str = "dregg-channel-member-root-v1";
/// Domain tag for [`channel_key_commitment`].
const CHANNEL_KEY_COMMIT_DOMAIN: &str = "dregg-channel-key-commit-v1";

/// One member leaf: BLAKE3(domain, member_cell ‖ seal_pk). Binding the seal
/// public key INTO the on-cell membership commitment means the rekey fan-out
/// target set is pinned by the chain — a key-substitution on the off-cell
/// roster re-commits to a different root and fails closed.
pub fn channel_member_leaf(member_cell: &[u8; 32], seal_pk: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CHANNEL_MEMBER_LEAF_DOMAIN);
    hasher.update(member_cell);
    hasher.update(seal_pk);
    *hasher.finalize().as_bytes()
}

/// Canonical openable commitment over the member-leaf set: BLAKE3 over the
/// length-prefixed SORTED leaves (the mailbox sender-set shape). An empty
/// set commits to a nonzero root distinct from the unborn all-zero slot.
pub fn channel_member_root(
    leaves: &std::collections::BTreeSet<[u8; 32]>,
) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key(CHANNEL_MEMBER_ROOT_DOMAIN);
    hasher.update(&(leaves.len() as u64).to_le_bytes());
    for leaf in leaves {
        hasher.update(leaf);
    }
    *hasher.finalize().as_bytes()
}

/// The epoch key commitment written to [`CH_KEY_COMMIT_SLOT`]:
/// BLAKE3(domain, epoch ‖ key). Binding the epoch into the commitment makes
/// a replayed old-key commitment at a new epoch detectable by every member.
pub fn channel_key_commitment(epoch: u64, key: &[u8; 32]) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key(CHANNEL_KEY_COMMIT_DOMAIN);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(key);
    *hasher.finalize().as_bytes()
}

/// The channel-group constraint set. The teeth, in keystone order:
///
/// 1. **term pins** — admin + tag pinned once out of `UNINIT` (the
///    settlement-family `pin_term` shape);
/// 2. **lifecycle** — `AllowedTransitions` UNINIT→OPEN→CLOSED; CLOSED is
///    terminal/inert (no row out, no self-row);
/// 3. **epoch never rewinds** — `Monotonic{epoch}`;
/// 4. **THE EPOCH UNIFICATION TRIPLE** (see the module-section docs):
///    membership change ⇒ epoch step; key change ⇒ epoch step; epoch step ⇒
///    fresh key commitment. Together: remove + rekey are ONE turn or UNSAT.
/// 5. **governance** — membership / epoch / key / lifecycle writes admit
///    only the admin sender (`AnyOf[Immutable{slot}, SenderIs{admin}]`, the
///    polis per-slot actor binding). A turn that touches none of the gated
///    slots admits any sender (posting is off-cell anyway). The in-program
///    M-of-N council gate has its atom now ([`StateConstraint::CountGe`];
///    proved shape `councilGated`, `metatheory/Dregg2/Apps/ChannelGroup.lean`;
///    runtime shape `council_count_ge_shape` below) — it stays OUT of the
///    deployed program until the quorum-commitment slot is itself written by
///    the actor-bound approval ceremony (`CountGe` proves the distinct COUNT,
///    not per-element approval of THIS turn; see its docstring), so a council
///    governs by holding the admin key today.
/// 6. **THE EPOCH IS THE DELEGATION EPOCH** —
///    `DelegationEpochEquals { index: CH_EPOCH_SLOT }`: the epoch slot equals
///    the cell's own post-turn `delegation_epoch` (the R7 capability-freshness
///    counter) on EVERY admitted turn. This is the program-enforced form of
///    the tie the canonical builders check fail-closed
///    (`Channel::epoch_step`, `sdk/src/channels.rs`;
///    `node/src/channels_service.rs` — both kept as defense-in-depth): an
///    epoch-slot write that does not ride the same turn as the anchor
///    `RevokeDelegation` (or any forged divergence between the two counters)
///    is REFUSED by the program itself. Lean: constraint 6 of
///    `channelConstraints` + `admitted_ties_delegation_epoch`, which
///    DISCHARGES the `DelegationEpochTie` premise
///    (`metatheory/Dregg2/Apps/ChannelGroup.lean`).
///
/// Fails closed on a zero admin (no governor) and a zero tag
/// (indistinguishable from an unborn cell).
pub fn channel_state_constraints(
    terms: &ChannelTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.admin == FIELD_ZERO {
        return Err(BlueprintError::ZeroAdmin);
    }
    if terms.tag == FIELD_ZERO {
        return Err(BlueprintError::ZeroTag);
    }
    let admin_gated = |slot: u8| StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: slot },
            SimpleStateConstraint::SenderIs { pk: terms.admin },
        ],
    };
    let epoch_steps_when_changed = |slot: u8| StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: slot },
            SimpleStateConstraint::StrictMonotonic {
                index: CH_EPOCH_SLOT,
            },
        ],
    };
    Ok(vec![
        // ── 1. term pins ──
        pin_term(CH_ADMIN_SLOT, terms.admin),
        pin_term(CH_TAG_SLOT, terms.tag),
        // ── 2. lifecycle (CLOSED terminal/inert) ──
        StateConstraint::AllowedTransitions {
            slot_index: CH_STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(CH_STATE_CLOSED)),
            ],
        },
        // ── 3. the epoch never rewinds ──
        StateConstraint::Monotonic {
            index: CH_EPOCH_SLOT,
        },
        // ── 4. THE EPOCH UNIFICATION TRIPLE ──
        // membership change ⇒ epoch strictly steps:
        epoch_steps_when_changed(CH_MEMBER_ROOT_SLOT),
        // key-commitment change ⇒ epoch strictly steps (no silent rekey
        // within an epoch):
        epoch_steps_when_changed(CH_KEY_COMMIT_SLOT),
        // epoch step ⇒ the key commitment is REWRITTEN (a removal that
        // bumps the epoch but keeps the old key is UNSAT):
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable {
                    index: CH_EPOCH_SLOT,
                },
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::Immutable {
                    index: CH_KEY_COMMIT_SLOT,
                })),
            ],
        },
        // ── 5. governance: the admin sender gates the control plane ──
        admin_gated(CH_MEMBER_ROOT_SLOT),
        admin_gated(CH_EPOCH_SLOT),
        admin_gated(CH_KEY_COMMIT_SLOT),
        admin_gated(CH_STATE_SLOT),
        // ── 6. THE EPOCH IS THE DELEGATION EPOCH (the program-readable tie) ──
        StateConstraint::DelegationEpochEquals {
            index: CH_EPOCH_SLOT,
        },
    ])
}

/// The `CellProgram` installed on the channel cell for its whole life.
pub fn channel_cell_program(terms: &ChannelTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(channel_state_constraints(terms)?))
}

/// **The channel-group factory (per-group, content-addressed)** — the ORGANS
/// §4 group cell. Like the settlement families, each (admin, tag) pair gets
/// its own descriptor whose constraints bake the terms as literals.
pub fn channel_factory_descriptor(
    terms: &ChannelTerms,
) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:channel-factory v1",
        channel_state_constraints(terms)?,
    ))
}

// =============================================================================
// Program-level tests (the executor-independent half; the end-to-end half
// lives in `sdk/tests/factory_settlement_e2e.rs` on the real TurnExecutor)
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preconditions::EvalContext;
    use crate::program::TransitionMeta;
    use crate::program::WitnessBundle;
    use crate::state::CellState;

    fn terms() -> EscrowTerms {
        EscrowTerms {
            amount: 40,
            depositor: field_from_u64(2222),
            beneficiary: field_from_u64(1111),
            condition: field_from_u64(99),
            timeout_height: 100,
        }
    }

    fn ctx_at(height: u64) -> EvalContext {
        EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender: None,
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }

    fn eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
    ) -> Result<(), crate::program::ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(&ctx_at(height)),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    /// The post-open state of the canonical test escrow.
    fn open_state(t: &EscrowTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[VALUE_SLOT as usize] = field_from_u64(t.amount);
        s.fields[PARTY_A_SLOT as usize] = t.depositor;
        s.fields[PARTY_B_SLOT as usize] = t.beneficiary;
        s.fields[CONDITION_SLOT as usize] = t.condition;
        s.fields[DEADLINE_SLOT as usize] = field_from_u64(t.timeout_height);
        s
    }

    #[test]
    fn birth_state_satisfies_program() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let born = CellState::new(0);
        assert!(
            eval(&p, &born, None, 0).is_ok(),
            "all-zero birth state must pass"
        );
    }

    #[test]
    fn open_writes_terms_and_passes() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let born = CellState::new(0);
        assert!(eval(&p, &open_state(&t), Some(&born), 0).is_ok());
    }

    #[test]
    fn open_with_tampered_terms_rejected() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let born = CellState::new(0);
        let mut bad = open_state(&t);
        bad.fields[VALUE_SLOT as usize] = field_from_u64(7_000_000); // inflate the amount
        assert!(
            eval(&p, &bad, Some(&born), 0).is_err(),
            "term pin must bite"
        );
    }

    #[test]
    fn term_rewrite_while_open_rejected() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[PARTY_B_SLOT as usize] = field_from_u64(0xDEAD); // re-point the beneficiary
        assert!(eval(&p, &new, Some(&old), 0).is_err());
    }

    #[test]
    fn release_with_correct_witness_passes() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[WITNESS_SLOT as usize] = t.condition;
        new.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        assert!(eval(&p, &new, Some(&old), 0).is_ok());
    }

    #[test]
    fn release_without_witness_rejected() {
        // Lean keystone (c): release_requires_condition.
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        assert!(eval(&p, &new, Some(&old), 0).is_err());
    }

    #[test]
    fn release_with_wrong_witness_rejected() {
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[WITNESS_SLOT as usize] = field_from_u64(7); // 7 ≠ 99
        new.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        assert!(eval(&p, &new, Some(&old), 0).is_err());
    }

    #[test]
    fn refund_before_timeout_rejected_after_timeout_passes() {
        let t = terms(); // timeout 100
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(
            eval(&p, &new, Some(&old), 99).is_err(),
            "height 99 < timeout 100"
        );
        assert!(
            eval(&p, &new, Some(&old), 100).is_ok(),
            "height 100 >= timeout 100"
        );
    }

    #[test]
    fn zero_timeout_escrow_refunds_any_time() {
        // Lean semantics: escrowRefund is gated only on OPEN.
        let mut t = terms();
        t.timeout_height = 0;
        let p = escrow_cell_program(&t).unwrap();
        let old = open_state(&t);
        let mut new = old.clone();
        new.fields[DEADLINE_SLOT as usize] = FIELD_ZERO;
        let mut old0 = old.clone();
        old0.fields[DEADLINE_SLOT as usize] = FIELD_ZERO;
        new.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(eval(&p, &new, Some(&old0), 0).is_ok());
    }

    #[test]
    fn no_double_resolve() {
        // Lean keystone (b): a resolved cell admits NO further transition —
        // not a second release, not a refund, not even a touch.
        let t = terms();
        let p = escrow_cell_program(&t).unwrap();
        let mut released = open_state(&t);
        released.fields[WITNESS_SLOT as usize] = t.condition;
        released.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        // released → refunded:
        let mut refund = released.clone();
        refund.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(eval(&p, &refund, Some(&released), 1000).is_err());
        // released → released (the self-row is absent: terminal cells are inert):
        assert!(eval(&p, &released, Some(&released), 1000).is_err());
    }

    #[test]
    fn zero_condition_rejected_at_build() {
        let mut t = terms();
        t.condition = FIELD_ZERO;
        assert_eq!(
            escrow_state_constraints(&t),
            Err(BlueprintError::ZeroCondition)
        );
    }

    #[test]
    fn obligation_slash_gates() {
        let t = ObligationTerms {
            bond: 50,
            obligor: field_from_u64(10),
            obligee: field_from_u64(20),
            condition: field_from_u64(42),
            deadline_height: 200,
        };
        let p = obligation_cell_program(&t).unwrap();
        let mut open = CellState::new(0);
        open.fields[STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        open.fields[VALUE_SLOT as usize] = field_from_u64(t.bond);
        open.fields[PARTY_A_SLOT as usize] = t.obligor;
        open.fields[PARTY_B_SLOT as usize] = t.obligee;
        open.fields[CONDITION_SLOT as usize] = t.condition;
        open.fields[DEADLINE_SLOT as usize] = field_from_u64(t.deadline_height);

        // Slash before the deadline: rejected.
        let mut slashed = open.clone();
        slashed.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(eval(&p, &slashed, Some(&open), 199).is_err());
        // Slash after the deadline: admitted.
        assert!(eval(&p, &slashed, Some(&open), 200).is_ok());
        // Slash that exhibits the condition witness: rejected even after the
        // deadline (Lean slash_rejects_when_condition_met).
        let mut bad = slashed.clone();
        bad.fields[WITNESS_SLOT as usize] = t.condition;
        assert!(eval(&p, &bad, Some(&open), 500).is_err());
        // Fulfil with the condition witness: admitted (and time-ungated).
        let mut fulfilled = open.clone();
        fulfilled.fields[WITNESS_SLOT as usize] = t.condition;
        fulfilled.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        assert!(eval(&p, &fulfilled, Some(&open), 0).is_ok());
    }

    #[test]
    fn obligation_zero_deadline_rejected_at_build() {
        let t = ObligationTerms {
            bond: 50,
            obligor: field_from_u64(10),
            obligee: field_from_u64(20),
            condition: field_from_u64(42),
            deadline_height: 0,
        };
        assert_eq!(
            obligation_state_constraints(&t),
            Err(BlueprintError::ZeroDeadline)
        );
    }

    #[test]
    fn bridge_finalize_requires_finality_witness() {
        let t = BridgeTerms {
            amount: 75,
            originator: field_from_u64(5),
            pot: field_from_u64(6),
            finality_witness: field_from_u64(777),
            timeout_height: 0,
        };
        let p = bridge_cell_program(&t).unwrap();
        let mut locked = CellState::new(0);
        locked.fields[STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        locked.fields[VALUE_SLOT as usize] = field_from_u64(t.amount);
        locked.fields[PARTY_A_SLOT as usize] = t.originator;
        locked.fields[PARTY_B_SLOT as usize] = t.pot;
        locked.fields[CONDITION_SLOT as usize] = t.finality_witness;

        let mut finalized = locked.clone();
        finalized.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_A);
        assert!(
            eval(&p, &finalized, Some(&locked), 0).is_err(),
            "no witness → rejected"
        );
        finalized.fields[WITNESS_SLOT as usize] = t.finality_witness;
        assert!(eval(&p, &finalized, Some(&locked), 0).is_ok());
        // Cancel with zero timeout: any time while locked (Lean locked_cancellable).
        let mut cancelled = locked.clone();
        cancelled.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(eval(&p, &cancelled, Some(&locked), 0).is_ok());
    }

    // ── Trustline program teeth (Lean Dregg2.Apps.Trustline polarities) ──

    fn tl_terms() -> TrustlineTerms {
        TrustlineTerms {
            line: 100,
            issuer: field_from_u64(0xA11CE),
            holder: field_from_u64(0xB0B),
        }
    }

    /// The post-open state of the canonical test trustline (Lean `demo₀`).
    fn tl_open_state(t: &TrustlineTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[TL_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[TL_CEILING_SLOT as usize] = field_from_u64(t.line);
        s.fields[TL_ISSUER_SLOT as usize] = t.issuer;
        s.fields[TL_HOLDER_SLOT as usize] = t.holder;
        s
    }

    fn tl_with(base: &CellState, drawn: u64, settled: u64) -> CellState {
        let mut s = base.clone();
        s.fields[TL_DRAWN_SLOT as usize] = field_from_u64(drawn);
        s.fields[TL_SETTLED_SLOT as usize] = field_from_u64(settled);
        s
    }

    #[test]
    fn trustline_birth_and_open() {
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let born = CellState::new(0);
        assert!(eval(&p, &born, None, 0).is_ok(), "all-zero birth passes");
        assert!(
            eval(&p, &tl_open_state(&t), Some(&born), 0).is_ok(),
            "open writes the terms"
        );
        // Tampered ceiling at open: rejected (term pin).
        let mut bad = tl_open_state(&t);
        bad.fields[TL_CEILING_SLOT as usize] = field_from_u64(1_000_000);
        assert!(eval(&p, &bad, Some(&born), 0).is_err());
    }

    #[test]
    fn trustline_ceiling_immutable_forever() {
        // Lean `ceiling_immutable_forever`: no op moves the ceiling.
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let old = tl_open_state(&t);
        let mut new = old.clone();
        new.fields[TL_CEILING_SLOT as usize] = field_from_u64(101);
        assert!(eval(&p, &new, Some(&old), 0).is_err());
        // Re-pointing the holder is equally rejected.
        let mut new2 = old.clone();
        new2.fields[TL_HOLDER_SLOT as usize] = field_from_u64(0xDEAD);
        assert!(eval(&p, &new2, Some(&old), 0).is_err());
    }

    #[test]
    fn trustline_draw_within_line_and_refusal() {
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let open = tl_open_state(&t);
        // POSITIVE: a within-line draw admits (Lean `draw_within_line`).
        assert!(eval(&p, &tl_with(&open, 30, 0), Some(&open), 0).is_ok());
        // The boundary draw (exactly the line) admits — the bound is tight.
        assert!(eval(&p, &tl_with(&open, 100, 0), Some(&open), 0).is_ok());
        // NEGATIVE: an over-line draw is refused (`over_line_draw_refused`).
        assert!(eval(&p, &tl_with(&open, 101, 0), Some(&open), 0).is_err());
    }

    #[test]
    fn trustline_repay_monotone_down_with_settled_floor() {
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let open = tl_open_state(&t);
        let drawn30 = tl_with(&open, 30, 0);
        // Repay restores the line (Lean `draw_repay_roundtrip` shape).
        assert!(eval(&p, &tl_with(&open, 20, 0), Some(&drawn30), 0).is_ok());
        assert!(eval(&p, &tl_with(&open, 0, 0), Some(&drawn30), 0).is_ok());
        // Settled credit cannot be repaid back: drawn may not drop below
        // settled (the redeemed part is hard money in the holder's hands).
        let settled20 = tl_with(&open, 30, 20);
        assert!(eval(&p, &tl_with(&open, 25, 20), Some(&settled20), 0).is_ok());
        assert!(
            eval(&p, &tl_with(&open, 10, 20), Some(&settled20), 0).is_err(),
            "repaying below the settled floor must be refused"
        );
    }

    #[test]
    fn trustline_settlement_teeth() {
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let open = tl_open_state(&t);
        let pos = tl_with(&open, 30, 0);
        // Settle redeems up to drawn (settlePay_conserves_hard leg).
        assert!(eval(&p, &tl_with(&open, 30, 30), Some(&pos), 0).is_ok());
        // Settling beyond drawn is refused (would over-pay the escrow).
        assert!(eval(&p, &tl_with(&open, 30, 31), Some(&pos), 0).is_err());
        // Settlement is monotone: un-settling is refused.
        let settled = tl_with(&open, 30, 30);
        assert!(eval(&p, &tl_with(&open, 30, 10), Some(&settled), 0).is_err());
    }

    #[test]
    fn trustline_closed_is_inert() {
        let t = tl_terms();
        let p = trustline_cell_program(&t).unwrap();
        let open = tl_open_state(&t);
        let mut closed = open.clone();
        closed.fields[TL_STATE_SLOT as usize] = field_from_u64(TL_STATE_CLOSED);
        assert!(eval(&p, &closed, Some(&open), 0).is_ok(), "OPEN → CLOSED");
        // Any touch of a closed line is rejected — including reopening.
        assert!(eval(&p, &closed, Some(&closed), 0).is_err());
        assert!(eval(&p, &open, Some(&closed), 0).is_err());
    }

    #[test]
    fn trustline_zero_terms_rejected_at_build() {
        let mut t = tl_terms();
        t.line = 0;
        assert_eq!(
            trustline_state_constraints(&t),
            Err(BlueprintError::ZeroLine)
        );
        let mut t2 = tl_terms();
        t2.holder = FIELD_ZERO;
        assert_eq!(
            trustline_state_constraints(&t2),
            Err(BlueprintError::ZeroParty)
        );
    }

    #[test]
    fn trustline_descriptors_are_per_line_content_addressed() {
        let a = trustline_factory_descriptor(&tl_terms()).unwrap();
        let b = trustline_factory_descriptor(&tl_terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same line → same factory");
        let mut t2 = tl_terms();
        t2.line = 101;
        let c = trustline_factory_descriptor(&t2).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk);
        // Directionality: swapping issuer/holder is a DIFFERENT line.
        let swapped = TrustlineTerms {
            line: tl_terms().line,
            issuer: tl_terms().holder,
            holder: tl_terms().issuer,
        };
        let d = trustline_factory_descriptor(&swapped).unwrap();
        assert_ne!(a.factory_vk, d.factory_vk, "A→B ≠ B→A");
    }

    // ── Channel-group program teeth (ORGANS §4 — the epoch unification) ──

    fn ctx_sender(pk: [u8; 32], height: u64) -> EvalContext {
        EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender: Some(pk),
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }

    fn eval_ctx(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        ctx: &EvalContext,
    ) -> Result<(), crate::program::ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(ctx),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    /// Channel-program evaluation with the executor's per-cell
    /// `delegation_epoch` stamp (constraint 6 reads it; the executor's
    /// program-check loop stamps it on every touched cell —
    /// `turn/src/executor/execute_tree.rs`).
    fn eval_ch(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        ctx: &EvalContext,
        delegation_epoch: u64,
    ) -> Result<(), crate::program::ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(ctx),
            &TransitionMeta::wildcard().with_delegation_epoch(delegation_epoch),
            &WitnessBundle::empty(),
        )
    }

    const ADMIN: [u8; 32] = [0xADu8; 32];
    const STRANGER: [u8; 32] = [0x57u8; 32];

    fn ch_terms() -> ChannelTerms {
        ChannelTerms {
            admin: ADMIN,
            tag: field_from_u64(0xC0FFEE),
        }
    }

    fn ch_member_set(n: u64) -> std::collections::BTreeSet<[u8; 32]> {
        (0..n)
            .map(|i| {
                channel_member_leaf(
                    &field_from_u64(100 + i),
                    &field_from_u64(200 + i),
                )
            })
            .collect()
    }

    /// The post-open state of the canonical test channel: 3 members at
    /// epoch 1, key k1 committed.
    fn ch_open_state(t: &ChannelTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[CH_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[CH_MEMBER_ROOT_SLOT as usize] = channel_member_root(&ch_member_set(3));
        s.fields[CH_EPOCH_SLOT as usize] = field_from_u64(1);
        s.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(1, &[0x11; 32]);
        s.fields[CH_ADMIN_SLOT as usize] = t.admin;
        s.fields[CH_TAG_SLOT as usize] = t.tag;
        s
    }

    #[test]
    fn channel_birth_and_open() {
        let t = ch_terms();
        let p = channel_cell_program(&t).unwrap();
        let born = CellState::new(0);
        assert!(
            eval_ch(&p, &born, None, &ctx_sender(ADMIN, 0), 0).is_ok(),
            "all-zero birth passes (epoch slot 0 = delegation_epoch 0)"
        );
        assert!(
            eval_ch(&p, &ch_open_state(&t), Some(&born), &ctx_sender(ADMIN, 0), 1).is_ok(),
            "the open turn writes terms + the first epoch (and the anchor \
             revocation bumps delegation_epoch 0 → 1 in the same turn)"
        );
        // Open with a tampered admin slot: rejected (term pin).
        let mut bad = ch_open_state(&t);
        bad.fields[CH_ADMIN_SLOT as usize] = STRANGER;
        assert!(eval_ch(&p, &bad, Some(&born), &ctx_sender(ADMIN, 0), 1).is_err());
    }

    /// THE KEYSTONE, slot side: remove + rekey are ONE turn or UNSAT.
    #[test]
    fn channel_remove_and_rekey_are_one_turn() {
        let t = ch_terms();
        let p = channel_cell_program(&t).unwrap();
        let open = ch_open_state(&t);
        let admin = ctx_sender(ADMIN, 0);

        // The canonical remove: drop a member AND step the epoch AND commit
        // a fresh key (delegation_epoch riding 1 → 2) — admitted.
        let mut removed = open.clone();
        removed.fields[CH_MEMBER_ROOT_SLOT as usize] = channel_member_root(&ch_member_set(2));
        removed.fields[CH_EPOCH_SLOT as usize] = field_from_u64(2);
        removed.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(2, &[0x22; 32]);
        assert!(eval_ch(&p, &removed, Some(&open), &admin, 2).is_ok());

        // THE TIE TOOTH (constraint 6): the SAME otherwise-legal remove turn
        // whose epoch slot is FORGED away from the cell's delegation_epoch
        // (slot 2, counter still 1 — the turn did not carry the anchor
        // revocation): UNSAT.
        assert!(
            eval_ch(&p, &removed, Some(&open), &admin, 1).is_err(),
            "an epoch-slot write diverging from delegation_epoch must refuse"
        );

        // Remove WITHOUT the epoch step: UNSAT (membership ⇒ epoch tooth).
        let mut no_epoch = removed.clone();
        no_epoch.fields[CH_EPOCH_SLOT as usize] = open.fields[CH_EPOCH_SLOT as usize];
        no_epoch.fields[CH_KEY_COMMIT_SLOT as usize] =
            open.fields[CH_KEY_COMMIT_SLOT as usize];
        assert!(
            eval_ch(&p, &no_epoch, Some(&open), &admin, 1).is_err(),
            "membership change without an epoch step must refuse"
        );

        // Remove + epoch step but the OLD key kept: UNSAT (epoch ⇒ fresh-key
        // tooth — the removal that forgets to rekey).
        let mut stale_key = removed.clone();
        stale_key.fields[CH_KEY_COMMIT_SLOT as usize] =
            open.fields[CH_KEY_COMMIT_SLOT as usize];
        assert!(
            eval_ch(&p, &stale_key, Some(&open), &admin, 2).is_err(),
            "an epoch step carrying the stale key must refuse"
        );

        // A silent rekey (key change without an epoch step): UNSAT.
        let mut silent = open.clone();
        silent.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(1, &[0x99; 32]);
        assert!(
            eval_ch(&p, &silent, Some(&open), &admin, 1).is_err(),
            "rekey without an epoch step must refuse"
        );

        // Epoch rewind: UNSAT (Monotonic), even with the counter rewound too.
        let mut rewind = removed.clone();
        rewind.fields[CH_EPOCH_SLOT as usize] = field_from_u64(0);
        assert!(eval_ch(&p, &rewind, Some(&open), &admin, 0).is_err());

        // A pure rekey (epoch step + fresh key, membership unchanged):
        // admitted — compromise recovery.
        let mut rekey = open.clone();
        rekey.fields[CH_EPOCH_SLOT as usize] = field_from_u64(2);
        rekey.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(2, &[0x33; 32]);
        assert!(eval_ch(&p, &rekey, Some(&open), &admin, 2).is_ok());

        // Defense-in-depth fail-closed: with NO delegation_epoch stamp at all
        // (a legacy/wildcard meta — no executor in the loop), the program
        // refuses even the canonical remove (MissingContextField).
        assert!(
            eval_ctx(&p, &removed, Some(&open), &admin).is_err(),
            "an unstamped evaluation of the channel program must fail closed"
        );
    }

    /// The governance algebra gates membership: only the admin sender may
    /// touch membership / epoch / key / lifecycle.
    #[test]
    fn channel_governance_gates_membership() {
        let t = ch_terms();
        let p = channel_cell_program(&t).unwrap();
        let open = ch_open_state(&t);

        let mut joined = open.clone();
        joined.fields[CH_MEMBER_ROOT_SLOT as usize] = channel_member_root(&ch_member_set(4));
        joined.fields[CH_EPOCH_SLOT as usize] = field_from_u64(2);
        joined.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(2, &[0x44; 32]);

        // Admin joins a member: admitted.
        assert!(eval_ch(&p, &joined, Some(&open), &ctx_sender(ADMIN, 0), 2).is_ok());
        // A NON-MEMBER (any non-admin sender) forcing their own join:
        // refused — the SenderIs gate.
        assert!(
            eval_ch(&p, &joined, Some(&open), &ctx_sender(STRANGER, 0), 2).is_err(),
            "non-admin membership write must refuse"
        );
        // No sender at all (system turn): fail-closed on gated slots.
        assert!(eval_ch(&p, &joined, Some(&open), &ctx_at(0), 2).is_err());
        // A non-admin turn touching NOTHING gated: admitted (app slots are
        // free; the control plane alone is governed).
        let mut app_write = open.clone();
        app_write.fields[CH_APP_SLOT_A as usize] = field_from_u64(7);
        assert!(eval_ch(&p, &app_write, Some(&open), &ctx_sender(STRANGER, 0), 1).is_ok());

        // ── Heap proof-of-life: a HEAP-keyed constraint coexists with the
        // channel's slot constraints in ONE program (the rotation's
        // app-state lane; Lean twin `mixedHeapProgram`,
        // metatheory/Dregg2/Exec/Program.lean). The channel's app state —
        // here a message sequence counter — lives at heap key 64
        // (>= STATE_SLOTS, committed in fields_map), governed by a
        // heap-keyed Monotonic alongside the slot teeth.
        let mut constraints = channel_state_constraints(&t).unwrap();
        constraints.push(StateConstraint::HeapField {
            key: 64,
            atom: crate::program::HeapAtom::Monotonic,
        });
        let p2 = CellProgram::Predicate(constraints);
        let mut open_h = open.clone();
        assert!(open_h.set_field_ext(64, field_from_u64(5)));
        // Heap counter advances, control plane untouched: admitted for anyone.
        let mut seq_up = open_h.clone();
        assert!(seq_up.set_field_ext(64, field_from_u64(6)));
        assert!(eval_ch(&p2, &seq_up, Some(&open_h), &ctx_sender(STRANGER, 0), 1).is_ok());
        // Heap counter REWINDS: the heap tooth bites (slots all clean).
        let mut seq_down = open_h.clone();
        assert!(seq_down.set_field_ext(64, field_from_u64(4)));
        assert!(
            eval_ch(&p2, &seq_down, Some(&open_h), &ctx_sender(STRANGER, 0), 1).is_err(),
            "heap-keyed Monotonic must refuse a rewind of heap[64]"
        );
        // The SLOT teeth still bite under p2: a stranger forcing membership
        // (heap untouched) is refused exactly as under p.
        let mut joined_h = open_h.clone();
        joined_h.fields[CH_MEMBER_ROOT_SLOT as usize] = channel_member_root(&ch_member_set(4));
        joined_h.fields[CH_EPOCH_SLOT as usize] = field_from_u64(2);
        joined_h.fields[CH_KEY_COMMIT_SLOT as usize] = channel_key_commitment(2, &[0x44; 32]);
        assert!(
            eval_ch(&p2, &joined_h, Some(&open_h), &ctx_sender(STRANGER, 0), 2).is_err(),
            "slot governance must keep biting with the heap atom installed"
        );
        assert!(eval_ch(&p2, &joined_h, Some(&open_h), &ctx_sender(ADMIN, 0), 2).is_ok());
    }

    #[test]
    fn channel_terms_pinned_and_closed_inert() {
        let t = ch_terms();
        let p = channel_cell_program(&t).unwrap();
        let open = ch_open_state(&t);
        let admin = ctx_sender(ADMIN, 0);

        // Re-pointing the admin or the tag is refused even FOR the admin.
        let mut usurp = open.clone();
        usurp.fields[CH_ADMIN_SLOT as usize] = STRANGER;
        assert!(eval_ch(&p, &usurp, Some(&open), &admin, 1).is_err());
        let mut retag = open.clone();
        retag.fields[CH_TAG_SLOT as usize] = field_from_u64(2);
        assert!(eval_ch(&p, &retag, Some(&open), &admin, 1).is_err());

        // OPEN → CLOSED admits (admin); any touch of a closed group refuses.
        let mut closed = open.clone();
        closed.fields[CH_STATE_SLOT as usize] = field_from_u64(CH_STATE_CLOSED);
        assert!(eval_ch(&p, &closed, Some(&open), &admin, 1).is_ok());
        assert!(eval_ch(&p, &closed, Some(&closed), &admin, 1).is_err());
        assert!(eval_ch(&p, &open, Some(&closed), &admin, 1).is_err());
    }

    /// **The council shape (`CountGe` — in-program M-of-N), at the blueprint
    /// level.** The proved Lean twin is `councilGated` + the `council_*`
    /// keystones (`metatheory/Dregg2/Apps/ChannelGroup.lean`). This ships as
    /// a TEST shape, not a change to the deployed `channel_state_constraints`
    /// governance: `CountGe` discharges "the committed set opens ∧ ≥ M
    /// distinct elements" — it does NOT bind each element to a live approver
    /// of THIS turn, so until the quorum-commitment slot (`CH_APP_SLOT_A`
    /// here) is itself written by the actor-bound approval ceremony, wiring
    /// it into the live control plane would let whoever can write that slot
    /// mint quorums. The executor-path accept/refuse twin is
    /// `turn::tests::test_program_count_ge_enforced`.
    #[test]
    fn council_count_ge_shape() {
        use crate::program::{WitnessBlobView, WitnessKindTag};

        let t = ch_terms();
        // The council roster: members A and B (2-of-N quorum threshold 2).
        let member_a = [0xA1u8; 32];
        let member_b = [0xB2u8; 32];
        let quorum: std::collections::BTreeSet<[u8; 32]> =
            [member_a, member_b].into_iter().collect();
        let commitment = crate::program::count_ge_set_commitment(&quorum);

        // councilGated(member_root): AnyOf[Immutable, SenderIs admin, CountGe 2 @ app_a].
        let council = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable {
                    index: CH_MEMBER_ROOT_SLOT,
                },
                SimpleStateConstraint::SenderIs { pk: t.admin },
                SimpleStateConstraint::CountGe {
                    threshold: 2,
                    set_commitment_slot: CH_APP_SLOT_A,
                },
            ],
        }]);

        let mut open = ch_open_state(&t);
        open.fields[CH_APP_SLOT_A as usize] = commitment;
        let mut flipped = open.clone();
        flipped.fields[CH_MEMBER_ROOT_SLOT as usize] = channel_member_root(&ch_member_set(2));

        let exhibit =
            |elems: &[[u8; 32]]| postcard::to_allocvec(&elems.to_vec()).unwrap();
        let eval_with = |new: &CellState,
                         ctx: &EvalContext,
                         blob: Option<&[u8]>|
         -> Result<(), crate::program::ProgramError> {
            let views: Vec<WitnessBlobView<'_>> = blob
                .map(|b| {
                    vec![WitnessBlobView {
                        kind: WitnessKindTag::Cleartext,
                        bytes: b,
                    }]
                })
                .unwrap_or_default();
            council.evaluate_full(
                new,
                Some(&open),
                Some(ctx),
                &TransitionMeta::wildcard(),
                &WitnessBundle {
                    blobs: &views,
                    registry: None,
                },
            )
        };

        // A NON-admin flip carrying the 2-distinct quorum exhibit: ADMITTED.
        let both = exhibit(&[member_a, member_b]);
        assert!(
            eval_with(&flipped, &ctx_sender(STRANGER, 0), Some(&both)).is_ok(),
            "a bound 2-of-2 quorum exhibit must admit the flip without the admin"
        );
        // The duplicate-padded exhibit ([A, A] = ONE approver): REFUSED — the
        // distinctness tooth (this is what the affineLe-flag trick could not
        // enforce against unbounded counters).
        let dup = exhibit(&[member_a, member_a]);
        assert!(
            eval_with(&flipped, &ctx_sender(STRANGER, 0), Some(&dup)).is_err(),
            "a duplicate-padded exhibit must not count as a quorum"
        );
        // No exhibit at all: REFUSED (fail-closed witness absence).
        assert!(eval_with(&flipped, &ctx_sender(STRANGER, 0), None).is_err());
        // The admin still flips without any exhibit (the SenderIs disjunct).
        assert!(eval_with(&flipped, &ctx_sender(ADMIN, 0), None).is_ok());
        // A stranger leaving the slot untouched: ADMITTED (ceremony open).
        assert!(eval_with(&open, &ctx_sender(STRANGER, 0), None).is_ok());
    }

    #[test]
    fn channel_zero_terms_rejected_at_build() {
        let mut t = ch_terms();
        t.admin = FIELD_ZERO;
        assert_eq!(channel_state_constraints(&t), Err(BlueprintError::ZeroAdmin));
        let mut t2 = ch_terms();
        t2.tag = FIELD_ZERO;
        assert_eq!(channel_state_constraints(&t2), Err(BlueprintError::ZeroTag));
    }

    #[test]
    fn channel_descriptors_are_per_group_content_addressed() {
        let a = channel_factory_descriptor(&ch_terms()).unwrap();
        let b = channel_factory_descriptor(&ch_terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same group → same factory");
        let mut t2 = ch_terms();
        t2.tag = field_from_u64(2);
        let c = channel_factory_descriptor(&t2).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk, "different tag → different group");
        let mut t3 = ch_terms();
        t3.admin = STRANGER;
        let d = channel_factory_descriptor(&t3).unwrap();
        assert_ne!(a.factory_vk, d.factory_vk, "different admin → different group");
    }

    #[test]
    fn channel_member_root_binds_seal_keys() {
        // The root is deterministic over the open set…
        let r1 = channel_member_root(&ch_member_set(3));
        let r2 = channel_member_root(&ch_member_set(3));
        assert_eq!(r1, r2);
        // …distinct from the empty set and the unborn slot…
        assert_ne!(r1, channel_member_root(&std::collections::BTreeSet::new()));
        assert_ne!(channel_member_root(&std::collections::BTreeSet::new()), FIELD_ZERO);
        // …and a SEAL-KEY substitution for the same member cell re-commits
        // to a different root (the fan-out target set is chain-pinned).
        let mut subbed = ch_member_set(2);
        subbed.insert(channel_member_leaf(
            &field_from_u64(102),
            &field_from_u64(0xEEEE), // wrong seal pk for member 102
        ));
        assert_ne!(r1, channel_member_root(&subbed));
        // The key commitment binds the epoch.
        assert_ne!(
            channel_key_commitment(1, &[0x11; 32]),
            channel_key_commitment(2, &[0x11; 32])
        );
    }

    #[test]
    fn descriptors_are_per_deal_content_addressed() {
        let a = escrow_factory_descriptor(&terms()).unwrap();
        let b = escrow_factory_descriptor(&terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same deal → same factory");
        assert_eq!(a.hash(), b.hash());
        let mut t2 = terms();
        t2.amount = 41;
        let c = escrow_factory_descriptor(&t2).unwrap();
        assert_ne!(
            a.factory_vk, c.factory_vk,
            "different deal → different factory"
        );
        // Across families, the domain tags separate identical term tuples.
        let ob = obligation_factory_descriptor(&ObligationTerms {
            bond: terms().amount,
            obligor: terms().depositor,
            obligee: terms().beneficiary,
            condition: terms().condition,
            deadline_height: terms().timeout_height,
        })
        .unwrap();
        assert_ne!(a.factory_vk, ob.factory_vk);
    }
}
