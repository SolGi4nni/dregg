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
//! All three families are conditional-settlement cells over the same 8-slot
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
//! * The cell `balance` is sealed (not one of the 8 slots), so "resolve drains
//!   the full balance" and "the payout goes to the published counterparty" are
//!   NOT program-enforced; they are enforced by the SDK builders
//!   (`dregg_sdk::factories`) constructing the only sensible turn, and by the
//!   kernel move law (a `Transfer` conserves and fail-closes). This mirrors the
//!   Lean contracts, where the settle target is an argument of
//!   `escrowRelease`/`obSettle` rather than a checked field.
//! * The committed-escrow knowledge gate (release on a HASH-PREIMAGE reveal)
//!   needs `PreimageGate` under a state guard, which the current constraint
//!   grammar cannot express (`PreimageGate` is not a `SimpleStateConstraint`,
//!   so it cannot sit inside `AnyOf`/`Implies`). The cleartext witness-equality
//!   gate below is exactly the Lean `EscrowFactory` contract; the committed
//!   variant is kernel-design feedback for the dregg3 constraint grammar.

use crate::factory::{CapTarget, CapTemplate, ChildVkStrategy, FactoryDescriptor};
use crate::permissions::AuthRequired;
use crate::program::{
    CellProgram, SimpleStateConstraint, StateConstraint, field_from_u64,
};
use crate::state::{FIELD_ZERO, FieldElement};
use crate::cell::CellMode;

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
            SimpleStateConstraint::FieldEquals { index: slot, value: lit },
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
pub fn escrow_state_constraints(terms: &EscrowTerms) -> Result<Vec<StateConstraint>, BlueprintError> {
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
pub fn bridge_state_constraints(terms: &BridgeTerms) -> Result<Vec<StateConstraint>, BlueprintError> {
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
        assert!(eval(&p, &born, None, 0).is_ok(), "all-zero birth state must pass");
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
        assert!(eval(&p, &bad, Some(&born), 0).is_err(), "term pin must bite");
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
        assert!(eval(&p, &new, Some(&old), 99).is_err(), "height 99 < timeout 100");
        assert!(eval(&p, &new, Some(&old), 100).is_ok(), "height 100 >= timeout 100");
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
        assert_eq!(escrow_state_constraints(&t), Err(BlueprintError::ZeroCondition));
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
        assert_eq!(obligation_state_constraints(&t), Err(BlueprintError::ZeroDeadline));
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
        assert!(eval(&p, &finalized, Some(&locked), 0).is_err(), "no witness → rejected");
        finalized.fields[WITNESS_SLOT as usize] = t.finality_witness;
        assert!(eval(&p, &finalized, Some(&locked), 0).is_ok());
        // Cancel with zero timeout: any time while locked (Lean locked_cancellable).
        let mut cancelled = locked.clone();
        cancelled.fields[STATE_SLOT as usize] = field_from_u64(STATE_RESOLVED_B);
        assert!(eval(&p, &cancelled, Some(&locked), 0).is_ok());
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
        assert_ne!(a.factory_vk, c.factory_vk, "different deal → different factory");
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
