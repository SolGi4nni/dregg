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
use crate::program::{CellProgram, HashKind, SimpleStateConstraint, StateConstraint, field_from_u64};
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
    /// An allowance with a zero per-epoch ceiling is unspendable and its
    /// all-zero terms are indistinguishable from an unborn cell. Rejected at
    /// build (fail-closed).
    ZeroCeiling,
    /// An allowance with a zero epoch length has no period boundary — the
    /// epoch index `(block - start) / epoch_length` is undefined. Rejected at
    /// build (fail-closed).
    ZeroEpochLength,
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
            BlueprintError::ZeroCeiling => {
                write!(f, "allowance per-epoch ceiling must be nonzero")
            }
            BlueprintError::ZeroEpochLength => {
                write!(f, "allowance epoch length must be a nonzero number of blocks")
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
// Vault — Dregg2.Apps.Vault (HOUSE WELD #1: the conditional-timelock vault)
// =============================================================================
//
// A VAULT is value LOCKED until a release rule, claimable EXACTLY ONCE by the
// beneficiary after the condition is genuinely met — savings, a vesting
// schedule, a commitment device ("I cannot spend this until block N"), a
// deadbolt fund opened by a secret. It is the FIRST house room welded
// (`docs/HOUSE-CAPACITIES-WELD-PLAN.md` headline #1: highest value × smallest).
//
// A vault is a COMPOSITION, NOT a new `Effect`: it rides the SAME committed-cell
// substrate and the SAME wired settlement triple as the escrow/obligation/bridge
// families (`CreateCellFromFactory` + `Transfer` + `SetField`), and every gate it
// needs ALREADY EXISTS. So it is a factory descriptor over the existing
// constraint vocabulary, light-client-verifiable:
//
//   * create a vault   = `CreateCellFromFactory` over `vault_factory_descriptor`
//                        (installs the lock terms + the one-shot claim machine),
//   * fund the lock    = an ordinary `Transfer` IN (the value lives in the cell's
//                        own `balance`),
//   * claim it         = a `SetField` advancing OPEN→CLAIMED (admitted ONLY when
//                        the release condition holds) + a `Transfer` OUT to the
//                        beneficiary.
//
// The four claim-safety teeth (mirroring the settlement family + the Lean twin
// `Dregg2.Apps.Vault` / probe `Dregg2.Verify.VaultFactoryProbe`):
//
//   1. **Deal-term integrity** — beneficiary / release-height / condition-digest
//      are term-pinned once OPEN (`pin_term`).
//   2. **One-shot** — `AllowedTransitions` admits only
//      `(UNINIT,UNINIT), (UNINIT,OPEN), (OPEN,OPEN), (OPEN,CLAIMED)`. CLAIMED is a
//      terminal with NO outgoing (or self) row, so a claimed vault is INERT — no
//      double-claim, no replay (the lone terminal IS the one-shot tooth; vault is
//      escrow MINUS the refund leg).
//   3. **Release gate** — entering CLAIMED requires the committed condition to be
//      genuinely met:
//        * a TIMELOCK vault: `TemporalGate { not_before: release_height }` — the
//          claiming turn's block height must reach the release height (NO early
//          release; the same height clock the settlement family's resolve-B uses);
//        * a HASH-LOCK vault: `PreimageGate { commitment_index: COND_DIGEST_SLOT }`
//          — the claiming turn must reveal a preimage hashing to the committed
//          digest (NO forged proof).
//   4. **Drain tooth** — entering CLAIMED requires `BalanceLte { max: 0 }`: the
//      claim drains the full locked balance to the beneficiary (the value cannot be
//      partially claimed or stranded in the cell).
//
// The locked VALUE lives in the minted cell's own `balance`; funding is an
// ordinary conserving `Transfer` IN, claiming an ordinary `Transfer` OUT — NO
// side-table, so vault conservation is the ordinary kernel move law. (The
// beneficiary-is-the-claim-target binding is enforced by the SDK builder
// constructing the only sensible claim turn, exactly as the settlement family's
// payout target is — see the blueprint module-doc "What the program CANNOT see".)

/// Vault slot 0 — lifecycle state ([`STATE_UNINIT`] → [`STATE_OPEN`] →
/// [`VAULT_STATE_CLAIMED`]).
pub const VAULT_STATE_SLOT: u8 = 0;
/// Vault slot 1 — the beneficiary identity (the claim target; 32-byte `CellId`
/// encoding). Term-pinned once OPEN.
pub const VAULT_BENEFICIARY_SLOT: u8 = 1;
/// Vault slot 2 — the timelock release height (big-endian u64; the block height
/// at/after which a timelock vault is claimable). Term-pinned once OPEN. `0` for
/// a pure hash-lock vault (the preimage governs).
pub const VAULT_RELEASE_HEIGHT_SLOT: u8 = 2;
/// Vault slot 3 — the hash-lock target `H(preimage)` (the committed digest a
/// claim's revealed preimage must hash to). Term-pinned once OPEN. All-zero for a
/// pure timelock vault.
pub const VAULT_COND_DIGEST_SLOT: u8 = 3;

/// Terminal state of a claimed vault (inert — no row out of CLAIMED in the
/// transition table, the settlement-family one-shot shape).
pub const VAULT_STATE_CLAIMED: u64 = 2;

/// The release condition a vault is locked under (the minimal genuine slice: one
/// of two — a height timelock or a hash-lock). Mirrors the Lean
/// `Dregg2.Verify.VaultFactoryProbe` condition shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VaultCondition {
    /// Released at/after `release_height`: the claiming turn's block height must
    /// reach it (`TemporalGate { not_before: release_height }`). The "savings
    /// until block N" / "vested at block N" lock. `release_height` must be
    /// nonzero (a zero-height vault is claimable from genesis — not a lock).
    AtHeight { release_height: u64 },
    /// Released when a preimage hashing to `digest` is revealed
    /// (`PreimageGate { commitment_index: COND_DIGEST_SLOT }`). The "deadbolt
    /// fund opened by a secret/proof" lock. `digest` is the committed
    /// `H(preimage)` and must be nonzero (a zero digest is satisfied by an
    /// untouched slot).
    OnProof {
        /// The committed hash-lock target `H(genuine_preimage)`.
        digest: FieldElement,
        /// The hash family the preimage gate verifies against (Poseidon2 in
        /// circuit, BLAKE3 otherwise).
        hash_kind: HashKind,
    },
}

/// The published terms of one conditional vault: who may claim, and the release
/// condition. The locked amount is whatever is `Transfer`-ed IN (held in the
/// cell's own `balance`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VaultTerms {
    /// Beneficiary identity (the claim target), 32-byte encoding. Must be nonzero.
    pub beneficiary: FieldElement,
    /// The release condition the vault is locked under.
    pub condition: VaultCondition,
}

/// The vault constraint set for one lock. The teeth, in keystone order (see the
/// module-section docs); fails closed on a zero beneficiary (a claim would target
/// the zero cell), a zero release height (an `AtHeight` vault would be claimable
/// from genesis — not a lock), and a zero condition digest (an `OnProof` gate is
/// satisfied by the untouched slot).
///
/// Safety contract (proved on the Lean twin `Dregg2.Apps.Vault` + the probe
/// `Dregg2.Verify.VaultFactoryProbe`): conservation (the value moves by ordinary
/// `Transfer`), one-shot / no-double-claim (the one-terminal state machine),
/// claim-only-on-condition (`timelock_rejects_early` / `hashlock_rejects_forged`),
/// value-not-stranded (`open_vault_claimable`).
pub fn vault_state_constraints(terms: &VaultTerms) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.beneficiary == FIELD_ZERO {
        return Err(BlueprintError::ZeroParty);
    }
    // ── the release-height term + the release gate (timelock vs hash-lock) ──
    let (release_height, cond_digest, release_gate): (u64, FieldElement, SimpleStateConstraint) =
        match &terms.condition {
            VaultCondition::AtHeight { release_height } => {
                if *release_height == 0 {
                    return Err(BlueprintError::ZeroDeadline);
                }
                (
                    *release_height,
                    FIELD_ZERO,
                    SimpleStateConstraint::TemporalGate {
                        not_before: Some(*release_height),
                        not_after: None,
                    },
                )
            }
            VaultCondition::OnProof { digest, hash_kind } => {
                if *digest == FIELD_ZERO {
                    return Err(BlueprintError::ZeroCondition);
                }
                (
                    0,
                    *digest,
                    SimpleStateConstraint::PreimageGate {
                        commitment_index: VAULT_COND_DIGEST_SLOT,
                        hash_kind: *hash_kind,
                    },
                )
            }
        };
    Ok(vec![
        // ── 1. deal-term integrity (Lean: the Immutable deal terms) ──
        pin_term(VAULT_BENEFICIARY_SLOT, terms.beneficiary),
        pin_term(VAULT_RELEASE_HEIGHT_SLOT, field_from_u64(release_height)),
        pin_term(VAULT_COND_DIGEST_SLOT, cond_digest),
        // ── 2. the one-shot state machine (Lean: admitTable [(open, claimed)]) ──
        // CLAIMED is terminal/inert (no row out): the value leaves AT MOST once
        // (no double-claim / replay) — vault is escrow minus the refund leg.
        StateConstraint::AllowedTransitions {
            slot_index: VAULT_STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(VAULT_STATE_CLAIMED)),
            ],
        },
        // ── 3. the RELEASE gate: entering CLAIMED requires the condition met ──
        // (Lean: timelock_rejects_early / hashlock_rejects_forged.)
        when_state(VAULT_STATE_CLAIMED, release_gate),
        // ── 4. the DRAIN tooth: a claim drains the full locked balance out ──
        // (the value cannot be partially claimed or stranded in the cell).
        when_state(
            VAULT_STATE_CLAIMED,
            SimpleStateConstraint::BalanceLte { max: 0 },
        ),
    ])
}

/// The `CellProgram` installed on the vault cell for its whole life.
pub fn vault_cell_program(terms: &VaultTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(vault_state_constraints(terms)?))
}

/// **The vault factory (per-lock, content-addressed)** — HOUSE WELD #1. A vault is
/// a COMPOSITION over the existing constraint vocabulary settled by the wired
/// `CreateCellFromFactory` + `Transfer` + `SetField` triple — NO new `Effect`.
/// Lean twin: `Dregg2.Apps.Vault.vaultFactoryEntry`. Each lock gets its own
/// content-addressed descriptor whose constraints bake the terms as literals; the
/// locked value lives in the cell's own `balance`.
pub fn vault_factory_descriptor(terms: &VaultTerms) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:vault-factory v1",
        vault_state_constraints(terms)?,
    ))
}

// =============================================================================
// Allowance — Dregg2.Apps.Allowance (HOUSE WELD #2: the rate-limited allowance)
// =============================================================================
//
// An ALLOWANCE is a sub-capability that may spend up to a fixed CEILING of value
// per epoch, the ceiling enforced so it can be neither EXCEEDED nor FORGED,
// refilling each epoch — pocket money an agent hands a sub-agent that the
// sub-agent literally CANNOT overspend within an epoch. It is the SECOND house
// room welded (`docs/HOUSE-CAPACITIES-WELD-PLAN.md`, after the vault).
//
// An allowance is a COMPOSITION, NOT a new `Effect`: it rides the SAME
// committed-cell substrate and the SAME wired settlement triple as the
// vault/escrow families (`CreateCellFromFactory` + `Transfer` + `SetField`), and
// every gate it needs ALREADY EXISTS. So it is a factory descriptor over the
// existing constraint vocabulary, light-client-verifiable:
//
//   * create an allowance = `CreateCellFromFactory` over
//                           `allowance_factory_descriptor` (installs the frozen
//                           ceiling/epoch terms + the per-epoch ceiling teeth),
//   * fund the budget     = an ordinary `Transfer` IN (the spendable value lives
//                           in the cell's own `balance`),
//   * spend it            = a `SetField` advancing the epoch cursor + the spent
//                           counter (admitted ONLY when the post-spend running
//                           total stays under the ceiling) + a `Transfer` OUT to
//                           the beneficiary.
//
// The four allowance-safety teeth (mirroring the settlement family + the Lean
// twin `Dregg2.Apps.Allowance` / probe `Dregg2.Verify.AllowanceFactoryProbe`):
//
//   1. **Deal-term integrity (no-forge ceiling)** — beneficiary / ceiling /
//      epoch-length / start are term-pinned once OPEN (`pin_term`). A tampered
//      ceiling diverges from the committed literal and is rejected.
//   2. **The ceiling (no over-limit)** — `FieldLteField { spent ≤ ceiling }`: the
//      committed `spent_this_epoch` counter can NEVER exceed the per-epoch
//      ceiling (the exact trustline `drawn ≤ ceiling` shape), AND the
//      executor-side `RateLimitBySum { slot: spent, max_sum: ceiling, window:
//      epoch_length }` binds the cumulative value added to the spent slot within
//      a window to the ceiling — cumulative spend per epoch ≤ ceiling.
//   3. **Monotone epoch cursor (no stale/backward refill)** — `Monotonic`
//      `current_epoch`: the cursor never moves backward, so a backdated spend
//      cannot reach into a closed epoch's headroom.
//   4. **Perpetual lifecycle** — `AllowedTransitions` admits
//      `(UNINIT,UNINIT), (UNINIT,OPEN), (OPEN,OPEN)`. OPEN is the live state and
//      stays live (an allowance refills forever — no terminal, unlike the vault's
//      one-shot CLAIMED).
//
// The spendable VALUE lives in the minted cell's own `balance`; funding is an
// ordinary conserving `Transfer` IN, spending an ordinary `Transfer` OUT — NO
// side-table, so allowance conservation is the ordinary kernel move law. The
// epoch rollover (resetting `spent_this_epoch` to 0 when a genuinely later epoch
// is crossed) is the SDK builder constructing the only sensible spend turn — the
// epoch is DERIVED from the block, so an early reset is structurally impossible
// (the same off-program target binding the settlement family's payout has — see
// the blueprint module-doc "What the program CANNOT see").

/// Allowance slot 0 — lifecycle state ([`STATE_UNINIT`] → [`STATE_OPEN`], which
/// is perpetual: an allowance refills forever, no terminal).
pub const ALLOWANCE_STATE_SLOT: u8 = 0;
/// Allowance slot 1 — the beneficiary identity (the spend target; 32-byte
/// `CellId` encoding). Term-pinned once OPEN.
pub const ALLOWANCE_BENEFICIARY_SLOT: u8 = 1;
/// Allowance slot 2 — the per-epoch CEILING `limit_per_epoch` (big-endian u64;
/// the maximum value spendable within a single epoch). Term-pinned once OPEN
/// (the no-forge tooth).
pub const ALLOWANCE_LIMIT_SLOT: u8 = 2;
/// Allowance slot 3 — the epoch length in blocks (big-endian u64). Term-pinned
/// once OPEN.
pub const ALLOWANCE_EPOCH_LENGTH_SLOT: u8 = 3;
/// Allowance slot 4 — the block height at which epoch `0` begins (big-endian
/// u64). Term-pinned once OPEN.
pub const ALLOWANCE_START_SLOT: u8 = 4;
/// Allowance slot 5 — the committed `current_epoch` cursor (big-endian u64). The
/// epoch the spent counter belongs to; monotone (never moves backward).
pub const ALLOWANCE_CURRENT_EPOCH_SLOT: u8 = 5;
/// Allowance slot 6 — the committed `spent_this_epoch` counter (big-endian u64).
/// Bounded at or below the ceiling; the epoch rollover resets it to `0` when a
/// genuinely later epoch is crossed.
pub const ALLOWANCE_SPENT_SLOT: u8 = 6;

/// The published terms of one rate-limited allowance: who may spend, the
/// per-epoch ceiling, the epoch length, and the block epoch `0` begins. The
/// spendable amount is whatever is `Transfer`-ed IN (held in the cell's own
/// `balance`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllowanceTerms {
    /// Beneficiary identity (the spend target), 32-byte encoding. Must be nonzero.
    pub beneficiary: FieldElement,
    /// The maximum value spendable within a single epoch. Must be `> 0`.
    pub limit_per_epoch: u64,
    /// The epoch length in blocks. Must be `> 0` — epoch `k` spans
    /// `[start + k·epoch_length, start + (k+1)·epoch_length)`.
    pub epoch_length: u64,
    /// The block height at which epoch `0` begins.
    pub start: u64,
}

/// The allowance constraint set for one budget. The teeth, in keystone order (see
/// the module-section docs); fails closed on a zero beneficiary (a spend would
/// target the zero cell), a zero ceiling (an unspendable budget whose all-zero
/// terms are indistinguishable from an unborn cell), and a zero epoch length (the
/// epoch index is undefined).
///
/// Safety contract (proved on the Lean twin `Dregg2.Apps.Allowance` + the probe
/// `Dregg2.Verify.AllowanceFactoryProbe`): conservation (the value moves by
/// ordinary `Transfer`), the ceiling (`over_ceiling_rejected` — `spent ≤ limit`),
/// no-forged/early refill (`stale_epoch_rejected` / `no_early_refill` — the epoch
/// is derived from the block), within-budget-spendable (`within_budget_spendable`).
pub fn allowance_state_constraints(
    terms: &AllowanceTerms,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    if terms.beneficiary == FIELD_ZERO {
        return Err(BlueprintError::ZeroParty);
    }
    if terms.limit_per_epoch == 0 {
        return Err(BlueprintError::ZeroCeiling);
    }
    if terms.epoch_length == 0 {
        return Err(BlueprintError::ZeroEpochLength);
    }
    Ok(vec![
        // ── 1. deal-term integrity / no-forge ceiling (Lean: the four Immutable
        //       deal terms — beneficiary/limit/epochLength/start) ──
        pin_term(ALLOWANCE_BENEFICIARY_SLOT, terms.beneficiary),
        pin_term(ALLOWANCE_LIMIT_SLOT, field_from_u64(terms.limit_per_epoch)),
        pin_term(
            ALLOWANCE_EPOCH_LENGTH_SLOT,
            field_from_u64(terms.epoch_length),
        ),
        pin_term(ALLOWANCE_START_SLOT, field_from_u64(terms.start)),
        // ── 2. the perpetual lifecycle: OPEN is live and stays live (no terminal
        //       — an allowance refills forever, unlike the vault's one-shot) ──
        StateConstraint::AllowedTransitions {
            slot_index: ALLOWANCE_STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
            ],
        },
        // ── 3. THE CEILING (Lean: over_ceiling_rejected — spent ≤ limit) ──
        // The committed spent_this_epoch counter can NEVER exceed the per-epoch
        // ceiling — the exact trustline `drawn ≤ ceiling` shape.
        StateConstraint::FieldLteField {
            left_index: ALLOWANCE_SPENT_SLOT,
            right_index: ALLOWANCE_LIMIT_SLOT,
        },
        // ── 4. the per-epoch SUM ceiling (executor-side cumulative bound) ──
        // The value added to the spent slot within an epoch_length window cannot
        // exceed the ceiling: cumulative spend per epoch ≤ ceiling, the rate the
        // budget caveat's `(limit, window)` always wanted but couldn't commit.
        StateConstraint::RateLimitBySum {
            slot_index: ALLOWANCE_SPENT_SLOT,
            max_sum_per_epoch: terms.limit_per_epoch,
            epoch_duration: terms.epoch_length,
        },
        // ── 5. the monotone epoch cursor (Lean: the Monotonic currentEpoch —
        //       no stale/backward refill; a backdated spend can't reuse a closed
        //       epoch's headroom) ──
        StateConstraint::Monotonic {
            index: ALLOWANCE_CURRENT_EPOCH_SLOT,
        },
    ])
}

/// The `CellProgram` installed on the allowance cell for its whole life.
pub fn allowance_cell_program(terms: &AllowanceTerms) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(allowance_state_constraints(terms)?))
}

/// **The allowance factory (per-budget, content-addressed)** — HOUSE WELD #2. An
/// allowance is a COMPOSITION over the existing constraint vocabulary settled by
/// the wired `CreateCellFromFactory` + `Transfer` + `SetField` triple — NO new
/// `Effect`. Lean twin: `Dregg2.Apps.Allowance.allowanceFactoryEntry`. Each
/// budget gets its own content-addressed descriptor whose constraints bake the
/// terms as literals; the spendable value lives in the cell's own `balance`.
pub fn allowance_factory_descriptor(
    terms: &AllowanceTerms,
) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:allowance-factory v1",
        allowance_state_constraints(terms)?,
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

// ── The collateral axis (Lean §12 `Collateral`, ORGANS parameterization) ──

/// Trustline slot 7 — the collateral mode of the line, term-pinned once OPEN
/// for pureCredit lines ([`TL_COLLATERAL_PURE_CREDIT`]). fullReserve lines
/// keep the EXACT pre-axis constraint set (no pin, value stays the all-zero
/// default = [`TL_COLLATERAL_FULL_RESERVE`]) so their program VK — and every
/// already-born cell — is byte-identical to before the axis was reified.
/// Identification is by VK re-derivation, never by reading this slot.
pub const TL_COLLATERAL_SLOT: u8 = 7;
/// Slot-7 code: the full line is escrowed at open (the payment-channel point
/// — the deployed default; Lean `Collateral.fullReserve`).
pub const TL_COLLATERAL_FULL_RESERVE: u64 = 0;
/// Slot-7 code: no hard backing; the line is the issuer's consented risk
/// (the mutual-credit point; Lean `Collateral.pureCredit`).
pub const TL_COLLATERAL_PURE_CREDIT: u64 = 1;

/// The collateral backing of a trustline (Lean twin
/// `Dregg2.Apps.Trustline.Collateral`, §12). One axis, two points, ONE
/// parametric conservation keystone (`settleC_conserves_hard`):
///
/// * **fullReserve** — the issuer escrows the full line at open; epoch
///   settlement pays the holder OUT OF THE ESCROW while `settled` marches
///   (`settleC_fullReserve_spec`). Solvent by construction
///   (`escrow_solvent_forever`).
/// * **pureCredit** — nothing is escrowed; the bilateral ±`drawn` pair IS the
///   credit (Lean §11: `holderAcct = +drawn`, `issuerWell = −drawn`, both
///   DERIVED — the deployed cell carries no extra registers). Draws and
///   repays move no hard value (§12b `stepC`); settlement is the holder
///   repaying the issuer hard value while the credit legs unwind
///   (`settleC_pureCredit_agrees_settlePay` — the §5b `settlePay` shape).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TrustlineCollateral {
    /// The full line is escrowed at open (the deployed default).
    #[default]
    FullReserve,
    /// No hard backing; draws are issuer-moves on the DERIVED ±drawn pair.
    PureCredit,
}

impl TrustlineCollateral {
    /// The slot-7 code this mode pins (pureCredit) or defaults to
    /// (fullReserve).
    pub fn slot_code(self) -> u64 {
        match self {
            TrustlineCollateral::FullReserve => TL_COLLATERAL_FULL_RESERVE,
            TrustlineCollateral::PureCredit => TL_COLLATERAL_PURE_CREDIT,
        }
    }
}

/// [`trustline_state_constraints`] at a point of the collateral axis.
/// `FullReserve` returns the EXACT historical constraint vector (identical
/// program VK — existing lines are untouched); `PureCredit` additionally
/// term-pins slot 7 to [`TL_COLLATERAL_PURE_CREDIT`], so the mode is
/// content-addressed into the per-line program and a born cell
/// self-authenticates its collateral point forever.
pub fn trustline_state_constraints_collateral(
    terms: &TrustlineTerms,
    collateral: TrustlineCollateral,
) -> Result<Vec<StateConstraint>, BlueprintError> {
    let mut constraints = trustline_state_constraints(terms)?;
    if collateral == TrustlineCollateral::PureCredit {
        constraints.push(pin_term(
            TL_COLLATERAL_SLOT,
            field_from_u64(TL_COLLATERAL_PURE_CREDIT),
        ));
    }
    Ok(constraints)
}

/// The `CellProgram` installed on a trustline cell at a collateral point.
pub fn trustline_cell_program_collateral(
    terms: &TrustlineTerms,
    collateral: TrustlineCollateral,
) -> Result<CellProgram, BlueprintError> {
    Ok(CellProgram::Predicate(
        trustline_state_constraints_collateral(terms, collateral)?,
    ))
}

/// [`trustline_factory_descriptor`] at a point of the collateral axis (the
/// fullReserve point is byte-identical to the historical descriptor).
pub fn trustline_factory_descriptor_collateral(
    terms: &TrustlineTerms,
    collateral: TrustlineCollateral,
) -> Result<FactoryDescriptor, BlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:trustline-factory v1",
        trustline_state_constraints_collateral(terms, collateral)?,
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
pub fn channel_member_root(leaves: &std::collections::BTreeSet<[u8; 32]>) -> FieldElement {
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
    fn trustline_collateral_axis_full_reserve_is_byte_identical() {
        // The fullReserve point of the axis IS the historical program: same
        // constraints, same VK, same factory — no already-born line moves.
        let t = tl_terms();
        assert_eq!(
            trustline_state_constraints(&t).unwrap(),
            trustline_state_constraints_collateral(&t, TrustlineCollateral::FullReserve).unwrap(),
        );
        assert_eq!(
            trustline_factory_descriptor(&t).unwrap().factory_vk,
            trustline_factory_descriptor_collateral(&t, TrustlineCollateral::FullReserve)
                .unwrap()
                .factory_vk,
        );
    }

    #[test]
    fn trustline_pure_credit_pins_the_mode_and_distinguishes_the_vk() {
        let t = tl_terms();
        let full = trustline_factory_descriptor(&t).unwrap();
        let pure =
            trustline_factory_descriptor_collateral(&t, TrustlineCollateral::PureCredit).unwrap();
        assert_ne!(
            full.factory_vk, pure.factory_vk,
            "the collateral point is content-addressed into the per-line program"
        );

        let p = trustline_cell_program_collateral(&t, TrustlineCollateral::PureCredit).unwrap();
        let born = CellState::new(0);
        assert!(eval(&p, &born, None, 0).is_ok(), "all-zero birth passes");
        // The open turn writes the mode pin alongside the terms.
        let mut open = tl_open_state(&t);
        open.fields[TL_COLLATERAL_SLOT as usize] = field_from_u64(TL_COLLATERAL_PURE_CREDIT);
        assert!(eval(&p, &open, Some(&born), 0).is_ok(), "pureCredit open");
        // Opening WITHOUT the mode pin is refused (slot 7 ≠ the pinned literal).
        assert!(
            eval(&p, &tl_open_state(&t), Some(&born), 0).is_err(),
            "a pureCredit program refuses an unpinned open"
        );
        // Once open, flipping the mode back is refused (term pin).
        let mut flipped = open.clone();
        flipped.fields[TL_COLLATERAL_SLOT as usize] = field_from_u64(TL_COLLATERAL_FULL_RESERVE);
        assert!(
            eval(&p, &flipped, Some(&open), 0).is_err(),
            "mode immutable"
        );
        // The credit teeth ride unchanged: within-line draw admits, over-line
        // refuses (Lean §12b stepC — draws move only the credit registers).
        let mut drawn = open.clone();
        drawn.fields[TL_DRAWN_SLOT as usize] = field_from_u64(30);
        assert!(eval(&p, &drawn, Some(&open), 0).is_ok());
        let mut over = open.clone();
        over.fields[TL_DRAWN_SLOT as usize] = field_from_u64(101);
        assert!(eval(&p, &over, Some(&open), 0).is_err());
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
            .map(|i| channel_member_leaf(&field_from_u64(100 + i), &field_from_u64(200 + i)))
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
            eval_ch(
                &p,
                &ch_open_state(&t),
                Some(&born),
                &ctx_sender(ADMIN, 0),
                1
            )
            .is_ok(),
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
        no_epoch.fields[CH_KEY_COMMIT_SLOT as usize] = open.fields[CH_KEY_COMMIT_SLOT as usize];
        assert!(
            eval_ch(&p, &no_epoch, Some(&open), &admin, 1).is_err(),
            "membership change without an epoch step must refuse"
        );

        // Remove + epoch step but the OLD key kept: UNSAT (epoch ⇒ fresh-key
        // tooth — the removal that forgets to rekey).
        let mut stale_key = removed.clone();
        stale_key.fields[CH_KEY_COMMIT_SLOT as usize] = open.fields[CH_KEY_COMMIT_SLOT as usize];
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

        let exhibit = |elems: &[[u8; 32]]| postcard::to_allocvec(&elems.to_vec()).unwrap();
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
                    finalized_roots: None,
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
        assert_eq!(
            channel_state_constraints(&t),
            Err(BlueprintError::ZeroAdmin)
        );
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
        assert_ne!(
            a.factory_vk, c.factory_vk,
            "different tag → different group"
        );
        let mut t3 = ch_terms();
        t3.admin = STRANGER;
        let d = channel_factory_descriptor(&t3).unwrap();
        assert_ne!(
            a.factory_vk, d.factory_vk,
            "different admin → different group"
        );
    }

    #[test]
    fn channel_member_root_binds_seal_keys() {
        // The root is deterministic over the open set…
        let r1 = channel_member_root(&ch_member_set(3));
        let r2 = channel_member_root(&ch_member_set(3));
        assert_eq!(r1, r2);
        // …distinct from the empty set and the unborn slot…
        assert_ne!(r1, channel_member_root(&std::collections::BTreeSet::new()));
        assert_ne!(
            channel_member_root(&std::collections::BTreeSet::new()),
            FIELD_ZERO
        );
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

    // =========================================================================
    // Vault — HOUSE WELD #1 (the conditional-timelock vault as a factory cell).
    // The four claim-safety teeth, on the program the executor installs: term
    // integrity, one-shot (no double-claim), claim-only-on-condition (timelock
    // no-early-release + hash-lock no-forged-proof), and the drain tooth. The
    // Lean twin is `Dregg2.Apps.Vault` (+ probe `VaultFactoryProbe`).
    // =========================================================================

    /// A timelock vault: beneficiary 1111 may claim at/after block 11_000.
    fn timelock_terms() -> VaultTerms {
        VaultTerms {
            beneficiary: field_from_u64(1111),
            condition: VaultCondition::AtHeight {
                release_height: 11_000,
            },
        }
    }

    /// The genuine hash-lock preimage + a hash-lock vault committing to its hash.
    fn hashlock_preimage() -> [u8; 32] {
        let mut p = [0u8; 32];
        p[0..18].copy_from_slice(b"the-secret-preima\0");
        p
    }
    fn hashlock_terms() -> VaultTerms {
        let digest = *blake3::hash(&hashlock_preimage()).as_bytes();
        VaultTerms {
            beneficiary: field_from_u64(1111),
            condition: VaultCondition::OnProof {
                digest,
                hash_kind: HashKind::Blake3,
            },
        }
    }

    /// The post-open (locked, OPEN) state of a vault. The locked VALUE lives in
    /// the cell's own `balance` (held until claimed).
    fn vault_open_state(t: &VaultTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[VAULT_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[VAULT_BENEFICIARY_SLOT as usize] = t.beneficiary;
        match &t.condition {
            VaultCondition::AtHeight { release_height } => {
                s.fields[VAULT_RELEASE_HEIGHT_SLOT as usize] = field_from_u64(*release_height);
                s.fields[VAULT_COND_DIGEST_SLOT as usize] = FIELD_ZERO;
            }
            VaultCondition::OnProof { digest, .. } => {
                s.fields[VAULT_RELEASE_HEIGHT_SLOT as usize] = field_from_u64(0);
                s.fields[VAULT_COND_DIGEST_SLOT as usize] = *digest;
            }
        }
        s.set_balance(500); // the locked value, held in the cell
        s
    }

    /// The claimed (CLAIMED) post-state: the value has been moved OUT to the
    /// beneficiary (balance drained to 0), the state advanced to CLAIMED.
    fn vault_claimed_state(open: &CellState) -> CellState {
        let mut s = open.clone();
        s.fields[VAULT_STATE_SLOT as usize] = field_from_u64(VAULT_STATE_CLAIMED);
        s.set_balance(0); // the claim drained the full locked balance to the beneficiary
        s
    }

    /// Evaluate a vault program at `height` with an optional revealed preimage.
    fn vault_eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
        preimage: Option<[u8; 32]>,
    ) -> Result<(), crate::program::ProgramError> {
        let ctx = EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender: None,
            sender_epoch_count: 0,
            revealed_preimage: preimage,
        };
        program.evaluate_full(
            new,
            old,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    #[test]
    fn vault_birth_and_open_pass_and_term_tamper_refuses() {
        let t = timelock_terms();
        let p = vault_cell_program(&t).unwrap();
        // the all-zero birth state passes (factory mints with no initial fields):
        let born = CellState::new(0);
        assert!(vault_eval(&p, &born, None, 0, None).is_ok(), "birth state");
        // opening writes the lock terms and passes:
        let open = vault_open_state(&t);
        assert!(
            vault_eval(&p, &open, Some(&born), 0, None).is_ok(),
            "open writes the lock terms"
        );
        // re-pointing the beneficiary while OPEN is rejected (term pin bites):
        let mut bad = open.clone();
        bad.fields[VAULT_BENEFICIARY_SLOT as usize] = field_from_u64(0xDEAD);
        assert!(
            vault_eval(&p, &bad, Some(&open), 0, None).is_err(),
            "beneficiary term pin must bite"
        );
        // tampering the release height while OPEN is rejected:
        let mut bad2 = open.clone();
        bad2.fields[VAULT_RELEASE_HEIGHT_SLOT as usize] = field_from_u64(1);
        assert!(
            vault_eval(&p, &bad2, Some(&open), 0, None).is_err(),
            "release-height term pin must bite"
        );
    }

    #[test]
    fn vault_timelock_claim_after_release_passes_before_rejects() {
        // KEYSTONE (c) timelock: no early release; claimable at/after the height.
        let t = timelock_terms(); // release at 11_000
        let p = vault_cell_program(&t).unwrap();
        let open = vault_open_state(&t);
        let claimed = vault_claimed_state(&open);

        // EARLY: one block before the release height is REJECTED.
        assert!(
            vault_eval(&p, &claimed, Some(&open), 10_999, None).is_err(),
            "cannot claim before the timelock (no early release)"
        );
        // AT the release height is the live boundary (non-vacuity).
        assert!(
            vault_eval(&p, &claimed, Some(&open), 11_000, None).is_ok(),
            "claimable exactly at the release height"
        );
        // AFTER is claimable too.
        assert!(
            vault_eval(&p, &claimed, Some(&open), 11_500, None).is_ok(),
            "claimable after the release height"
        );
    }

    #[test]
    fn vault_hashlock_claim_with_genuine_preimage_passes_forged_rejects() {
        // KEYSTONE (c) hash-lock: genuine preimage claims; forged proof rejected.
        let t = hashlock_terms();
        let p = vault_cell_program(&t).unwrap();
        let open = vault_open_state(&t);
        let claimed = vault_claimed_state(&open);

        // GENUINE preimage discharges the gate (non-vacuity — the live accept).
        assert!(
            vault_eval(&p, &claimed, Some(&open), 0, Some(hashlock_preimage())).is_ok(),
            "the genuine preimage discharges the hash-lock"
        );
        // FORGED preimage (wrong secret) is REJECTED.
        let mut forged = [0u8; 32];
        forged[0..5].copy_from_slice(b"WRONG");
        assert!(
            vault_eval(&p, &claimed, Some(&open), 0, Some(forged)).is_err(),
            "a wrong preimage does not satisfy the hash-lock (no forged proof)"
        );
        // NO preimage at all is REJECTED.
        assert!(
            vault_eval(&p, &claimed, Some(&open), 0, None).is_err(),
            "claiming a hash-lock vault without any preimage is rejected"
        );
    }

    #[test]
    fn vault_no_double_claim() {
        // KEYSTONE (b): a CLAIMED vault is inert — no further transition admitted
        // (no double-claim, no replay). The lone terminal IS the one-shot tooth.
        let t = timelock_terms();
        let p = vault_cell_program(&t).unwrap();
        let open = vault_open_state(&t);
        let claimed = vault_claimed_state(&open);

        // the first claim (OPEN→CLAIMED, after release) is live:
        assert!(vault_eval(&p, &claimed, Some(&open), 11_500, None).is_ok());
        // a SECOND claim (CLAIMED→CLAIMED self-row absent) is REJECTED:
        assert!(
            vault_eval(&p, &claimed, Some(&claimed), 11_500, None).is_err(),
            "a claimed vault cannot be claimed again (one-shot)"
        );
    }

    #[test]
    fn vault_claim_must_drain_the_full_balance() {
        // The drain tooth: a claim entering CLAIMED with value still in the cell
        // (balance > 0) is rejected — the value cannot be partially claimed or
        // stranded in the vault.
        let t = timelock_terms();
        let p = vault_cell_program(&t).unwrap();
        let open = vault_open_state(&t);
        // CLAIMED but the balance was NOT drained (still 500 in the cell):
        let mut undrained = open.clone();
        undrained.fields[VAULT_STATE_SLOT as usize] = field_from_u64(VAULT_STATE_CLAIMED);
        // (balance left at 500 from vault_open_state)
        assert!(
            vault_eval(&p, &undrained, Some(&open), 11_500, None).is_err(),
            "a claim must drain the full locked balance to the beneficiary"
        );
    }

    #[test]
    fn vault_ill_formed_terms_rejected_at_build() {
        // a zero beneficiary would target the zero cell on claim:
        assert_eq!(
            vault_state_constraints(&VaultTerms {
                beneficiary: FIELD_ZERO,
                condition: VaultCondition::AtHeight {
                    release_height: 11_000
                },
            }),
            Err(BlueprintError::ZeroParty)
        );
        // a zero release height is claimable from genesis — not a lock:
        assert_eq!(
            vault_state_constraints(&VaultTerms {
                beneficiary: field_from_u64(1111),
                condition: VaultCondition::AtHeight { release_height: 0 },
            }),
            Err(BlueprintError::ZeroDeadline)
        );
        // a zero hash-lock digest is satisfied by an untouched slot:
        assert_eq!(
            vault_state_constraints(&VaultTerms {
                beneficiary: field_from_u64(1111),
                condition: VaultCondition::OnProof {
                    digest: FIELD_ZERO,
                    hash_kind: HashKind::Blake3,
                },
            }),
            Err(BlueprintError::ZeroCondition)
        );
    }

    #[test]
    fn vault_descriptors_are_per_lock_content_addressed() {
        let a = vault_factory_descriptor(&timelock_terms()).unwrap();
        let b = vault_factory_descriptor(&timelock_terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same lock → same factory");
        // a different release height ⇒ a different factory:
        let c = vault_factory_descriptor(&VaultTerms {
            beneficiary: field_from_u64(1111),
            condition: VaultCondition::AtHeight {
                release_height: 12_000,
            },
        })
        .unwrap();
        assert_ne!(a.factory_vk, c.factory_vk, "different lock → different factory");
        // a hash-lock vault is a distinct factory from a timelock vault:
        let h = vault_factory_descriptor(&hashlock_terms()).unwrap();
        assert_ne!(a.factory_vk, h.factory_vk);
        // and distinct from the escrow family (the domain tag separates them):
        let esc = escrow_factory_descriptor(&terms()).unwrap();
        assert_ne!(a.factory_vk, esc.factory_vk);
    }

    // =========================================================================
    // Allowance — HOUSE WELD #2 (the rate-limited allowance as a factory cell).
    // The four allowance-safety teeth, on the program the executor installs:
    // term integrity (no-forge ceiling), the ceiling (spent ≤ limit, no
    // over-limit), the monotone epoch cursor (no stale/backward refill), and the
    // perpetual lifecycle. The Lean twin is `Dregg2.Apps.Allowance` (+ probe
    // `AllowanceFactoryProbe`).
    // =========================================================================

    /// An allowance: beneficiary 1111 may spend up to 100 per 1000-block epoch,
    /// starting at block 10_000.
    fn allowance_terms() -> AllowanceTerms {
        AllowanceTerms {
            beneficiary: field_from_u64(1111),
            limit_per_epoch: 100,
            epoch_length: 1000,
            start: 10_000,
        }
    }

    /// The post-open (live, OPEN) state of an allowance: the frozen terms, the
    /// cursor at epoch 0, nothing spent. The spendable VALUE lives in the cell's
    /// own `balance`.
    fn allowance_open_state(t: &AllowanceTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[ALLOWANCE_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[ALLOWANCE_BENEFICIARY_SLOT as usize] = t.beneficiary;
        s.fields[ALLOWANCE_LIMIT_SLOT as usize] = field_from_u64(t.limit_per_epoch);
        s.fields[ALLOWANCE_EPOCH_LENGTH_SLOT as usize] = field_from_u64(t.epoch_length);
        s.fields[ALLOWANCE_START_SLOT as usize] = field_from_u64(t.start);
        s.fields[ALLOWANCE_CURRENT_EPOCH_SLOT as usize] = field_from_u64(0);
        s.fields[ALLOWANCE_SPENT_SLOT as usize] = field_from_u64(0);
        s.set_balance(1000); // the spendable value, held in the cell
        s
    }

    /// A post-spend state: the spent counter advanced to `spent`, the cursor at
    /// `epoch`, the held balance reduced by the cumulative spend.
    fn allowance_after_spend(open: &CellState, epoch: u64, spent: u64, balance: i64) -> CellState {
        let mut s = open.clone();
        s.fields[ALLOWANCE_CURRENT_EPOCH_SLOT as usize] = field_from_u64(epoch);
        s.fields[ALLOWANCE_SPENT_SLOT as usize] = field_from_u64(spent);
        s.set_balance(balance);
        s
    }

    /// Evaluate an allowance program transition (no preimage; the height drives
    /// any temporal gate — the allowance has none in-program, the epoch is the
    /// SDK builder's derived term).
    fn allowance_eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
    ) -> Result<(), crate::program::ProgramError> {
        let ctx = EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender: None,
            sender_epoch_count: 0,
            revealed_preimage: None,
        };
        program.evaluate_full(
            new,
            old,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    #[test]
    fn allowance_birth_and_open_pass_and_term_tamper_refuses() {
        let t = allowance_terms();
        let p = allowance_cell_program(&t).unwrap();
        // the all-zero birth state passes (factory mints with no initial fields):
        let born = CellState::new(0);
        assert!(allowance_eval(&p, &born, None, 0).is_ok(), "birth state");
        // opening writes the budget terms and passes:
        let open = allowance_open_state(&t);
        assert!(
            allowance_eval(&p, &open, Some(&born), 0).is_ok(),
            "open writes the budget terms"
        );
        // re-pointing the beneficiary while OPEN is rejected (term pin bites):
        let mut bad = open.clone();
        bad.fields[ALLOWANCE_BENEFICIARY_SLOT as usize] = field_from_u64(0xDEAD);
        assert!(
            allowance_eval(&p, &bad, Some(&open), 0).is_err(),
            "beneficiary term pin must bite"
        );
        // FORGING THE CEILING up while OPEN is rejected (the no-forge tooth):
        let mut bad2 = open.clone();
        bad2.fields[ALLOWANCE_LIMIT_SLOT as usize] = field_from_u64(999_999);
        assert!(
            allowance_eval(&p, &bad2, Some(&open), 0).is_err(),
            "a forged-up ceiling term pin must bite"
        );
    }

    #[test]
    fn allowance_spend_within_ceiling_passes_over_rejects() {
        // KEYSTONE (b): the ceiling — spent ≤ limit. A spend within budget passes;
        // a committed spent counter over the ceiling is rejected.
        let t = allowance_terms(); // ceiling 100
        let p = allowance_cell_program(&t).unwrap();
        let open = allowance_open_state(&t);

        // spend 40 of the 100 ceiling (spent 0→40, balance 1000→960): passes.
        let s40 = allowance_after_spend(&open, 0, 40, 960);
        assert!(
            allowance_eval(&p, &s40, Some(&open), 10_500).is_ok(),
            "a within-budget spend (40 ≤ 100) passes"
        );
        // spend EXACTLY the ceiling (100) is the live boundary (non-vacuity):
        let s100 = allowance_after_spend(&open, 0, 100, 900);
        assert!(
            allowance_eval(&p, &s100, Some(&open), 10_500).is_ok(),
            "spending exactly the ceiling (100 ≤ 100) is live"
        );
        // a committed spent counter OVER the ceiling (101) is REJECTED:
        let s101 = allowance_after_spend(&open, 0, 101, 899);
        assert!(
            allowance_eval(&p, &s101, Some(&open), 10_500).is_err(),
            "a spent counter over the ceiling (101 > 100) is rejected — no over-limit"
        );
    }

    #[test]
    fn allowance_epoch_cursor_is_monotone_no_backward_refill() {
        // KEYSTONE (c): the monotone cursor — a backdated spend cannot move the
        // committed epoch cursor backward (no reaching into a closed epoch's
        // headroom). The cursor at epoch 2 cannot regress to epoch 0.
        let t = allowance_terms();
        let p = allowance_cell_program(&t).unwrap();
        // a state already advanced into epoch 2:
        let open = allowance_open_state(&t);
        let at_epoch2 = allowance_after_spend(&open, 2, 30, 970);
        // a CURRENT-epoch (2) spend is live (non-vacuity):
        let fwd = allowance_after_spend(&at_epoch2, 2, 60, 940);
        assert!(
            allowance_eval(&p, &fwd, Some(&at_epoch2), 12_600).is_ok(),
            "a current-epoch spend advancing the counter is live"
        );
        // a BACKWARD cursor move (epoch 2 → 0) is REJECTED by the Monotonic tooth:
        let mut backdated = at_epoch2.clone();
        backdated.fields[ALLOWANCE_CURRENT_EPOCH_SLOT as usize] = field_from_u64(0);
        backdated.fields[ALLOWANCE_SPENT_SLOT as usize] = field_from_u64(5);
        assert!(
            allowance_eval(&p, &backdated, Some(&at_epoch2), 10_500).is_err(),
            "the epoch cursor cannot move backward (no stale-epoch refill)"
        );
    }

    #[test]
    fn allowance_epoch_rollover_refills_to_full_ceiling() {
        // The genuine rollover: at a later epoch the cursor advances and the spent
        // counter resets to a fresh value within the ceiling. Spend the full 100
        // in epoch 0, then a fresh 100 in epoch 1 — both within the ceiling.
        let t = allowance_terms();
        let p = allowance_cell_program(&t).unwrap();
        let open = allowance_open_state(&t);
        // exhaust epoch 0 (spent 100, cursor 0):
        let e0 = allowance_after_spend(&open, 0, 100, 900);
        assert!(allowance_eval(&p, &e0, Some(&open), 10_500).is_ok());
        // epoch 1 (block 11_000): cursor 0→1 (forward, monotone), spent resets to
        // a fresh 100 — within the ceiling, the refilled budget:
        let e1 = allowance_after_spend(&e0, 1, 100, 800);
        assert!(
            allowance_eval(&p, &e1, Some(&e0), 11_000).is_ok(),
            "the genuine epoch rollover refills the budget (cursor 0→1, spent reset within ceiling)"
        );
    }

    #[test]
    fn allowance_ill_formed_terms_rejected_at_build() {
        // a zero beneficiary would target the zero cell on spend:
        assert_eq!(
            allowance_state_constraints(&AllowanceTerms {
                beneficiary: FIELD_ZERO,
                limit_per_epoch: 100,
                epoch_length: 1000,
                start: 10_000,
            }),
            Err(BlueprintError::ZeroParty)
        );
        // a zero ceiling is an unspendable budget:
        assert_eq!(
            allowance_state_constraints(&AllowanceTerms {
                beneficiary: field_from_u64(1111),
                limit_per_epoch: 0,
                epoch_length: 1000,
                start: 10_000,
            }),
            Err(BlueprintError::ZeroCeiling)
        );
        // a zero epoch length leaves the epoch index undefined:
        assert_eq!(
            allowance_state_constraints(&AllowanceTerms {
                beneficiary: field_from_u64(1111),
                limit_per_epoch: 100,
                epoch_length: 0,
                start: 10_000,
            }),
            Err(BlueprintError::ZeroEpochLength)
        );
    }

    #[test]
    fn allowance_descriptors_are_per_budget_content_addressed() {
        let a = allowance_factory_descriptor(&allowance_terms()).unwrap();
        let b = allowance_factory_descriptor(&allowance_terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same budget → same factory");
        // a different ceiling ⇒ a different factory:
        let c = allowance_factory_descriptor(&AllowanceTerms {
            beneficiary: field_from_u64(1111),
            limit_per_epoch: 500,
            epoch_length: 1000,
            start: 10_000,
        })
        .unwrap();
        assert_ne!(
            a.factory_vk, c.factory_vk,
            "different ceiling → different factory"
        );
        // and distinct from the vault family (the domain tag separates them):
        let v = vault_factory_descriptor(&timelock_terms()).unwrap();
        assert_ne!(a.factory_vk, v.factory_vk);
    }
}

// =============================================================================
// Flash well — the zero-duration line of credit (the flash-loan answer)
// =============================================================================
//
// A FLASH WELL is a liquidity cell whose credit has ZERO DURATION: borrowing
// and settlement are the SAME action. The load-bearing semantics is the
// executor's per-action net-delta program check
// (`turn/src/executor/execute_tree.rs`): before an action's effects apply,
// the executor snapshots every cell the action touches (lines 600–624, over
// `collect_touched_cells`, `turn/src/executor/authorize.rs:2127`), and after
// the effects it re-evaluates each touched cell's installed program against
// the NET `(old, new)` pair (lines 770–886; a violation is
// `TurnError::ProgramViolation` and the WHOLE action refuses). The program
// never sees the intra-action dip — only the net — so a well program of the
// shape "my post-balance ≥ my pre-balance + fee" admits ANY intra-action use
// of the liquidity (any ring of legs through any cells) while refusing every
// action that nets the well down. The ACTION is the loan's whole lifetime.
//
// ## The granularity constraint (per-ACTION, not per-turn)
//
// Programs are evaluated once per action over that action's net. A ring
// split across TWO actions is two nets: the borrow action alone nets the
// well down `amount` and refuses; nothing carries credit forward. This is
// the flash-loan atomicity law as a PROGRAM consequence, not builder
// convention — see `flash_well_tests::ring_split_across_two_actions_refuses`.
//
// ## Encoding `post ≥ pre + fee` with today's atoms (the quantized ratchet)
//
// The runtime has NO relative balance atom: `BalanceGte`/`BalanceLte`
// (`cell/src/program.rs`) read only the absolute post-state balance. The
// well therefore carries its floor in a slot — `FW_RATCHET_SLOT`, the fee
// schedule position — and the program welds three teeth into the relative
// gate:
//
// 1. **Quantization** — `MemberOf{ratchet, {0, fee, 2·fee, …}}`: the ratchet
//    only ever sits on whole-fee rungs (no penny-stepping past the floor).
// 2. **Strict-on-touch** — `state == OPEN ⇒ StrictMonotonic{ratchet}`: EVERY
//    action that touches an open well (the executor's touched-set is every
//    cell named by any effect, incl. `ExerciseViaCapability` inner effects)
//    must climb the ratchet at least one rung. A net-zero borrow/repay that
//    skips the fee is refused HERE — the fee-evasion tooth.
// 3. **The rung ladder** — for every rung k:
//    `state == OPEN ∧ ratchet == k·fee ⇒ BalanceGte{principal + (k−1)·fee}`.
//    Climbing a rung raises the absolute floor by `fee`, so the net effect
//    of any admitted well-touching action is `post ≥ floor(old rung) + fee·Δrungs
//    ≥ pre-floor + fee` — the flash-loan invariant, program-enforced.
//
// Together: an action that touches an open well MUST climb ≥1 rung (tooth 2),
// CAN only climb in whole fees (tooth 1), and every climb drags the absolute
// balance floor up with it (tooth 3). The well's liquidity never decreases
// and every use pays ≥ the published fee. Accrued fees live IN the well's
// balance (solvent by the same floor) until the owner closes and sweeps.
//
// ## Honest residue (named, with the closure lane)
//
// * The floor is the SCHEDULE, not the literal pre-balance: a donation above
//   the current floor builds a cushion a later borrower could spend down to
//   the floor. Donations to an open well are not the protocol shape (fund
//   while UNINIT; while OPEN every touch pays a quantum anyway). The closure
//   lane is a real `BalanceDeltaGte { min_delta }` atom (old-vs-new balance,
//   one evaluator arm + a Lean `Exec.Program` twin) which collapses teeth
//   1–3 into one constraint; this blueprint's published surface (terms,
//   slots, builders) is unchanged by that swap.
// * EVERY open-well touch pays a quantum — including a post-open
//   `GrantCapability{from: well}` (the touched-set includes grant sources).
//   Mint borrower capabilities at adopt time (pre-OPEN), or attenuate the
//   adopt-time grant holder-side (delegation does not touch the well cell).
// * `max_draws` bounds the ladder (descriptor size is O(max_draws)); a well
//   at the last rung is exhausted — close it and open a successor.
//
// Lean twin: NOT YET AUTHORED (this blueprint is runtime-first; the
// `Dregg2.Apps.FlashWell` keystones — net-floor admission, fee-evasion
// refusal, two-action refusal — are the named lane to land with the
// `BalanceDeltaGte` atom). Until then the spec is this module doc + the
// program-level tests below + the executor-path tests in
// `sdk/src/flashwell.rs`.

/// Flash-well slot 0 — lifecycle state ([`STATE_UNINIT`] → [`STATE_OPEN`] →
/// [`FW_STATE_CLOSED`]).
pub const FW_STATE_SLOT: u8 = 0;
/// Flash-well slot 1 — the published principal: the liquidity the well must
/// never end an action below (big-endian u64). Term-pinned once OPEN.
pub const FW_PRINCIPAL_SLOT: u8 = 1;
/// Flash-well slot 2 — the published flat fee per use (big-endian u64).
/// Term-pinned once OPEN.
pub const FW_FEE_SLOT: u8 = 2;
/// Flash-well slot 3 — the governance identity: the public key whose
/// signature gates lifecycle writes (open/close). Term-pinned once OPEN.
pub const FW_OWNER_SLOT: u8 = 3;
/// Flash-well slot 4 — THE RATCHET: the fee-schedule position, a multiple of
/// the published fee. The open turn primes it to `1·fee`; every open-well
/// touch must climb ≥1 rung, and rung k pins the absolute balance floor
/// `principal + (k−1)·fee`. Accrued (redeemable) fees =
/// [`flash_well_accrued_fees`]` = ratchet − fee`.
pub const FW_RATCHET_SLOT: u8 = 4;

/// Terminal state of a closed (swept) flash well — inert: no transition row
/// out of CLOSED, the settlement-family no-double-resolve shape.
pub const FW_STATE_CLOSED: u64 = 2;

/// The ladder-size guard: descriptors are O(`max_draws`) constraints, so the
/// blueprint refuses schedules past this many rungs (fail-closed at build).
pub const MAX_FLASH_WELL_DRAWS: u32 = 4096;

/// The published terms of one flash well.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlashWellTerms {
    /// The well's principal: the liquidity floor (nonzero). Funded at birth
    /// (while UNINIT) like the settlement families; the program's rung
    /// ladder keeps the balance ≥ this forever while OPEN.
    pub principal: u64,
    /// Flat fee per use (nonzero): the minimum the well's balance must rise
    /// per well-touching action while OPEN.
    pub fee: u64,
    /// Governance public key (nonzero): the `SenderIs` gate over lifecycle
    /// writes (the [`ChannelTerms::admin`] shape — the executor evaluates
    /// `EvalContext::sender` as the acting agent cell's public key).
    pub owner: FieldElement,
    /// Number of servable draws after open (nonzero, ≤
    /// [`MAX_FLASH_WELL_DRAWS`]). Rung domain is `{0} ∪ {k·fee : k ∈
    /// 1..=max_draws+1}` (rung 1 is the open turn's priming quantum); a well
    /// at the last rung is exhausted.
    pub max_draws: u32,
}

/// A flash-well term set the blueprint refuses to publish (fail-closed at
/// build). A separate enum from [`BlueprintError`] so this section stays
/// append-only against the parallel lanes editing that enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlashWellError {
    /// `principal == 0`: a well with nothing to lend, indistinguishable from
    /// an unborn cell.
    ZeroPrincipal,
    /// `fee == 0`: the ratchet rungs collapse onto one value, so the
    /// strict-on-touch tooth would refuse every use forever (and the well
    /// would earn nothing). Rejected at build.
    ZeroFee,
    /// A zero owner key would have NO governor: the well could never open.
    ZeroOwner,
    /// `max_draws == 0` (an unusable well) or `> MAX_FLASH_WELL_DRAWS` (a
    /// descriptor-size bomb).
    BadDrawBound,
    /// `principal + (max_draws+1)·fee` overflows u64: the top rung's floor
    /// would wrap. Rejected at build.
    ScheduleOverflow,
}

impl std::fmt::Display for FlashWellError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FlashWellError::ZeroPrincipal => write!(f, "flash-well principal must be nonzero"),
            FlashWellError::ZeroFee => write!(f, "flash-well fee must be nonzero"),
            FlashWellError::ZeroOwner => write!(f, "flash-well owner key must be nonzero"),
            FlashWellError::BadDrawBound => write!(
                f,
                "flash-well max_draws must be in 1..={MAX_FLASH_WELL_DRAWS}"
            ),
            FlashWellError::ScheduleOverflow => write!(
                f,
                "flash-well fee schedule overflows u64 (principal + (max_draws+1)*fee)"
            ),
        }
    }
}

impl std::error::Error for FlashWellError {}

/// The redeemable accrued fees at a given ratchet reading: `ratchet − fee`
/// (the open turn's priming quantum is the schedule origin, not income).
pub fn flash_well_accrued_fees(ratchet: u64, fee: u64) -> u64 {
    ratchet.saturating_sub(fee)
}

/// The absolute balance floor pinned at rung `k` (`k ≥ 1`):
/// `principal + (k−1)·fee`.
pub fn flash_well_floor_at(terms: &FlashWellTerms, rung: u32) -> u64 {
    terms.principal + (rung.saturating_sub(1) as u64) * terms.fee
}

/// The flash-well constraint set. The teeth, in keystone order (see the
/// section docs above for why this encodes `post ≥ pre + fee`):
///
/// 1. **term pins** — principal / fee / owner pinned once out of `UNINIT`
///    (the settlement-family `pin_term` shape);
/// 2. **lifecycle** — `AllowedTransitions` UNINIT→OPEN→CLOSED; CLOSED is
///    terminal and inert (no row out — the sweep is the last word);
/// 3. **governance** — lifecycle writes admit only the owner sender
///    (`AnyOf[Immutable{state}, SenderIs{owner}]`);
/// 4. **ratchet never rewinds** — `Monotonic{ratchet}`;
/// 5. **quantization** — `MemberOf{ratchet, {0} ∪ {k·fee}}`;
/// 6. **strict-on-touch** — `OPEN ⇒ StrictMonotonic{ratchet}`: every action
///    touching an open well climbs ≥1 rung (the fee-evasion tooth; also
///    forces the open turn itself to prime rung 1);
/// 7. **the rung ladder** — `OPEN ∧ ratchet == k·fee ⇒
///    BalanceGte{principal + (k−1)·fee}` for every rung k: the climb drags
///    the absolute liquidity floor up by `fee` per rung.
pub fn flash_well_state_constraints(
    terms: &FlashWellTerms,
) -> Result<Vec<StateConstraint>, FlashWellError> {
    if terms.principal == 0 {
        return Err(FlashWellError::ZeroPrincipal);
    }
    if terms.fee == 0 {
        return Err(FlashWellError::ZeroFee);
    }
    if terms.owner == FIELD_ZERO {
        return Err(FlashWellError::ZeroOwner);
    }
    if terms.max_draws == 0 || terms.max_draws > MAX_FLASH_WELL_DRAWS {
        return Err(FlashWellError::BadDrawBound);
    }
    // Top rung = max_draws + 1 (rung 1 is the open turn's priming quantum).
    let top_rung = terms.max_draws as u64 + 1;
    let schedule_top = top_rung
        .checked_mul(terms.fee)
        .and_then(|fees| terms.principal.checked_add(fees))
        .ok_or(FlashWellError::ScheduleOverflow)?;
    let _ = schedule_top;

    let mut cs = vec![
        // ── 1. term pins ──
        pin_term(FW_PRINCIPAL_SLOT, field_from_u64(terms.principal)),
        pin_term(FW_FEE_SLOT, field_from_u64(terms.fee)),
        pin_term(FW_OWNER_SLOT, terms.owner),
        // ── 2. lifecycle (CLOSED terminal/inert) ──
        StateConstraint::AllowedTransitions {
            slot_index: FW_STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(STATE_OPEN)),
                (field_from_u64(STATE_OPEN), field_from_u64(FW_STATE_CLOSED)),
            ],
        },
        // ── 3. governance: only the owner steps the lifecycle ──
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable {
                    index: FW_STATE_SLOT,
                },
                SimpleStateConstraint::SenderIs { pk: terms.owner },
            ],
        },
        // ── 4. the ratchet never rewinds ──
        StateConstraint::Monotonic {
            index: FW_RATCHET_SLOT,
        },
        // ── 5. quantization: whole-fee rungs only ──
        StateConstraint::MemberOf {
            index: FW_RATCHET_SLOT,
            set: std::iter::once(0)
                .chain((1..=top_rung).map(|k| k * terms.fee))
                .collect(),
        },
        // ── 6. THE FEE-EVASION TOOTH: every open-well touch climbs ──
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(state_is(STATE_OPEN))),
                SimpleStateConstraint::StrictMonotonic {
                    index: FW_RATCHET_SLOT,
                },
            ],
        },
    ];
    // ── 7. THE RUNG LADDER: OPEN ∧ ratchet == k·fee ⇒ balance ≥ floor(k) ──
    // Rung 0 (unreachable while OPEN — tooth 6 forces the open turn off it)
    // is floored at the principal anyway, defense-in-depth.
    cs.push(StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(state_is(STATE_OPEN))),
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: FW_RATCHET_SLOT,
                value: field_from_u64(0),
            })),
            SimpleStateConstraint::BalanceGte {
                min: terms.principal,
            },
        ],
    });
    for k in 1..=top_rung {
        cs.push(StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(state_is(STATE_OPEN))),
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: FW_RATCHET_SLOT,
                    value: field_from_u64(k * terms.fee),
                })),
                SimpleStateConstraint::BalanceGte {
                    min: terms.principal + (k - 1) * terms.fee,
                },
            ],
        });
    }
    Ok(cs)
}

/// The `CellProgram` installed on the flash-well cell for its whole life.
pub fn flash_well_cell_program(terms: &FlashWellTerms) -> Result<CellProgram, FlashWellError> {
    Ok(CellProgram::Predicate(flash_well_state_constraints(terms)?))
}

/// **The flash-well factory (per-well, content-addressed)** — like the
/// settlement families, each term set gets its own descriptor whose
/// constraints bake the terms as literals; the liquidity lives in the cell's
/// own `balance` (funding and sweeping are ordinary conserving `Transfer`s).
pub fn flash_well_factory_descriptor(
    terms: &FlashWellTerms,
) -> Result<FactoryDescriptor, FlashWellError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:flash-well-factory v1",
        flash_well_state_constraints(terms)?,
    ))
}

// =============================================================================
// Flash-well program tests — the executor-independent half. Each test name
// states the LAW it pins; the executor-path twins (real TurnExecutor, real
// per-action snapshots) live in `sdk/src/flashwell.rs`.
//
// VERIFIED 2026-06-12: all 10 program-level tests pass (`cargo test -p
// dregg-cell flash_well`); the executor-path twins pass in the SDK lane.
// =============================================================================

#[cfg(test)]
mod flash_well_tests {
    use super::*;
    use crate::preconditions::EvalContext;
    use crate::program::{TransitionMeta, WitnessBundle};
    use crate::state::CellState;

    const OWNER: [u8; 32] = [0x0Fu8; 32];
    const STRANGER: [u8; 32] = [0x51u8; 32];

    fn fw_terms() -> FlashWellTerms {
        FlashWellTerms {
            principal: 1_000,
            fee: 10,
            owner: OWNER,
            max_draws: 4,
        }
    }

    fn ctx(sender: Option<[u8; 32]>) -> EvalContext {
        EvalContext {
            block_height: 7,
            timestamp: 0,
            current_epoch: 0,
            sender,
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }

    fn eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        sender: Option<[u8; 32]>,
    ) -> Result<(), crate::program::ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(&ctx(sender)),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    /// The post-open canonical well: terms written, ratchet primed at rung 1
    /// (`1·fee`), balance = exactly the principal (the funded birth, after
    /// the adopt turn burns its fee — the settlement-family lifecycle).
    fn open_well(t: &FlashWellTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[FW_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        s.fields[FW_PRINCIPAL_SLOT as usize] = field_from_u64(t.principal);
        s.fields[FW_FEE_SLOT as usize] = field_from_u64(t.fee);
        s.fields[FW_OWNER_SLOT as usize] = t.owner;
        s.fields[FW_RATCHET_SLOT as usize] = field_from_u64(t.fee);
        s.set_balance(t.principal as i64);
        s
    }

    /// `old_well` net-mutated to rung `k` with balance `bal` — the (old, new)
    /// pair the executor's per-action program check sees
    /// (`turn/src/executor/execute_tree.rs:600-624` snapshot,
    /// `:770-886` net re-check). The intra-action borrow/use legs are
    /// INVISIBLE here by construction — that is the artifact's whole point.
    fn net(base: &CellState, rung: u64, fee: u64, bal: i64) -> CellState {
        let mut s = base.clone();
        s.fields[FW_RATCHET_SLOT as usize] = field_from_u64(rung * fee);
        s.set_balance(bal);
        s
    }

    #[test]
    fn birth_funding_and_open() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        // All-zero birth passes.
        let born = CellState::new(0);
        assert!(eval(&p, &born, None, Some(OWNER)).is_ok());
        // Funding while UNINIT (balance up, slots untouched): admitted, no
        // ratchet quantum owed — UNINIT is exempt from the touch tooth.
        let mut funded = born.clone();
        funded.set_balance(t.principal as i64);
        assert!(eval(&p, &funded, Some(&born), Some(STRANGER)).is_ok());
        // The owner opens: terms + state + the rung-1 priming quantum.
        assert!(eval(&p, &open_well(&t), Some(&funded), Some(OWNER)).is_ok());
        // A stranger may NOT open (lifecycle is owner-gated).
        assert!(eval(&p, &open_well(&t), Some(&funded), Some(STRANGER)).is_err());
        // Opening without priming the ratchet: refused (the touch tooth —
        // the open turn is itself an open-well-ending touch).
        let mut unprimed = open_well(&t);
        unprimed.fields[FW_RATCHET_SLOT as usize] = field_from_u64(0);
        assert!(eval(&p, &unprimed, Some(&funded), Some(OWNER)).is_err());
        // Opening with a tampered principal term: refused (term pin).
        let mut inflated = open_well(&t);
        inflated.fields[FW_PRINCIPAL_SLOT as usize] = field_from_u64(9_999_999);
        assert!(eval(&p, &inflated, Some(&funded), Some(OWNER)).is_err());
    }

    /// LAW 1 — the honest ring succeeds. The ring's net on the well is
    /// (ratchet +1 rung, balance +fee); every intra-action leg (the draw out,
    /// the caller's ring legs, the repayment in) collapses into that net
    /// before the program ever runs.
    #[test]
    fn honest_ring_net_admits() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t); // rung 1, balance = principal
        let new = net(&old, 2, t.fee, (t.principal + t.fee) as i64);
        assert!(
            eval(&p, &new, Some(&old), Some(STRANGER)).is_ok(),
            "borrow→use→repay(+fee) in ONE action must admit, any sender"
        );
        // And again from rung 2 (the well keeps lending; fees accrue in
        // the balance, floored by the next rung).
        let newer = net(&new, 3, t.fee, (t.principal + 2 * t.fee) as i64);
        assert!(eval(&p, &newer, Some(&new), Some(STRANGER)).is_ok());
        assert_eq!(flash_well_accrued_fees(2 * t.fee, t.fee), t.fee);
    }

    /// LAW 2 — a ring missing its repayment leg refuses WHOLE: the net is
    /// (ratchet +1, balance −amount), under the new rung's floor. In the
    /// executor this is `TurnError::ProgramViolation` for the whole action
    /// (`execute_tree.rs:870-880`) — no leg of the ring survives.
    #[test]
    fn missing_repayment_refuses() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t);
        let borrowed = 600;
        let new = net(&old, 2, t.fee, (t.principal - borrowed) as i64);
        assert!(eval(&p, &new, Some(&old), Some(STRANGER)).is_err());
        // Even repaying the principal exactly (fee short) nets under-floor —
        // see the under-fee law; and not bumping the rung at all is the
        // fee-evasion law. All roads refuse.
    }

    /// LAW 3 — an under-fee ring refuses; the boundary (exactly +fee) admits.
    #[test]
    fn under_fee_refuses_boundary_admits() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t);
        let short = net(&old, 2, t.fee, (t.principal + t.fee - 1) as i64);
        assert!(
            eval(&p, &short, Some(&old), Some(STRANGER)).is_err(),
            "one unit under the fee must refuse (rung-2 floor)"
        );
        let exact = net(&old, 2, t.fee, (t.principal + t.fee) as i64);
        assert!(eval(&p, &exact, Some(&old), Some(STRANGER)).is_ok());
    }

    /// LAW 4 — THE GRANULARITY CONSTRAINT: a ring split across TWO actions
    /// refuses. Programs evaluate per ACTION over the net (old, new) pair —
    /// `execute_tree.rs` snapshots the touched set BEFORE one action's
    /// effects (lines 600–624) and re-checks each touched cell's program on
    /// its (pre, post) AFTER them (lines 770–886). The borrow action alone
    /// nets the well down: there is no cross-action credit to carry.
    #[test]
    fn ring_split_across_two_actions_refuses() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t);
        let borrowed = 600;
        // Action 1 of the split ring: draw out (with the dutiful rung bump).
        let action1 = net(&old, 2, t.fee, (t.principal - borrowed) as i64);
        assert!(
            eval(&p, &action1, Some(&old), Some(STRANGER)).is_err(),
            "the borrow half of a split ring must refuse (floor)"
        );
        // Action 1 without the bump refuses too (fee-evasion tooth).
        let action1_sneaky = net(&old, 1, t.fee, (t.principal - borrowed) as i64);
        assert!(eval(&p, &action1_sneaky, Some(&old), Some(STRANGER)).is_err());
        // The SAME two legs fused into ONE action are the admitted honest
        // ring of `honest_ring_net_admits` — granularity IS the law.
    }

    /// The fee-evasion tooth: a net-zero touch (borrow X, repay exactly X,
    /// no rung climb) refuses — every action touching an open well pays.
    #[test]
    fn net_zero_touch_without_climb_refuses() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t);
        assert!(
            eval(&p, &old.clone(), Some(&old), Some(STRANGER)).is_err(),
            "an untouched-net touch of an open well must refuse (StrictMonotonic)"
        );
        // Climbing one rung while paying: admits (the contrast).
        let paid = net(&old, 2, t.fee, (t.principal + t.fee) as i64);
        assert!(eval(&p, &paid, Some(&old), Some(STRANGER)).is_ok());
    }

    /// Quantization + monotonicity teeth: penny-steps, rewinds, and
    /// past-the-schedule climbs all refuse.
    #[test]
    fn ratchet_quantized_monotone_bounded() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let old = open_well(&t);
        // A non-multiple ratchet write: refused (MemberOf).
        let mut penny = old.clone();
        penny.fields[FW_RATCHET_SLOT as usize] = field_from_u64(t.fee + 1);
        penny.set_balance((t.principal + t.fee) as i64);
        assert!(eval(&p, &penny, Some(&old), Some(STRANGER)).is_err());
        // A rewind: refused (Monotonic), even back onto a valid rung.
        let high = net(&old, 3, t.fee, (t.principal + 2 * t.fee) as i64);
        let rewound = net(&high, 2, t.fee, (t.principal + 2 * t.fee) as i64);
        assert!(eval(&p, &rewound, Some(&high), Some(STRANGER)).is_err());
        // Past the top rung (max_draws=4 → top rung 5): refused — exhaustion.
        let top = net(&old, 5, t.fee, (t.principal + 4 * t.fee) as i64);
        assert!(eval(&p, &top, Some(&old), Some(STRANGER)).is_ok());
        let past = net(&top, 6, t.fee, (t.principal + 5 * t.fee) as i64);
        assert!(eval(&p, &past, Some(&top), Some(STRANGER)).is_err());
    }

    /// Close: the owner sweeps (principal + accrued fees) and the well goes
    /// inert; strangers cannot close; CLOSED is terminal.
    #[test]
    fn owner_close_sweeps_and_inert() {
        let t = fw_terms();
        let p = flash_well_cell_program(&t).unwrap();
        let open = net(&open_well(&t), 3, t.fee, (t.principal + 2 * t.fee) as i64);
        let mut closed = open.clone();
        closed.fields[FW_STATE_SLOT as usize] = field_from_u64(FW_STATE_CLOSED);
        closed.set_balance(0); // the sweep rides the same action
        assert!(eval(&p, &closed, Some(&open), Some(OWNER)).is_ok());
        assert!(eval(&p, &closed, Some(&open), Some(STRANGER)).is_err());
        // Any touch of a closed well refuses (no transition row out).
        assert!(eval(&p, &closed, Some(&closed), Some(OWNER)).is_err());
        assert!(eval(&p, &open, Some(&closed), Some(OWNER)).is_err());
    }

    #[test]
    fn bad_terms_rejected_at_build() {
        let mut t = fw_terms();
        t.principal = 0;
        assert_eq!(
            flash_well_state_constraints(&t),
            Err(FlashWellError::ZeroPrincipal)
        );
        let mut t = fw_terms();
        t.fee = 0;
        assert_eq!(
            flash_well_state_constraints(&t),
            Err(FlashWellError::ZeroFee)
        );
        let mut t = fw_terms();
        t.owner = FIELD_ZERO;
        assert_eq!(
            flash_well_state_constraints(&t),
            Err(FlashWellError::ZeroOwner)
        );
        let mut t = fw_terms();
        t.max_draws = 0;
        assert_eq!(
            flash_well_state_constraints(&t),
            Err(FlashWellError::BadDrawBound)
        );
        let mut t = fw_terms();
        t.principal = u64::MAX - 5;
        assert_eq!(
            flash_well_state_constraints(&t),
            Err(FlashWellError::ScheduleOverflow)
        );
    }

    #[test]
    fn descriptors_are_per_well_content_addressed() {
        let a = flash_well_factory_descriptor(&fw_terms()).unwrap();
        let b = flash_well_factory_descriptor(&fw_terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same terms → same factory");
        let mut t2 = fw_terms();
        t2.fee = 11;
        let c = flash_well_factory_descriptor(&t2).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk, "different fee → different well");
    }
}

// =============================================================================
// DKG ceremony — the randomness-organ transport cell (ORGANS §6 upgrade path)
// =============================================================================
//
// The ceremony state of one distributed key generation
// (`dregg_federation::dkg`, joint-Feldman) is a CELL. The DKG module proves
// the protocol math and DEMANDS two things of its environment: a COMMON VIEW
// (`compute_qual` is deterministic GIVEN agreed `(dealings, complaints,
// reveals)` sets) and ATTRIBUTABLE messages (so a bad dealing / false
// complaint is slashable). This blueprint is where both become chain facts:
//
// * **The phase machine** — UNINIT → DEALING → COMPLAINT → REVEAL →
//   FINAL/ABORTED, forward-only, terminals inert (the settlement-family
//   no-double-resolve shape). Rounds cannot be skipped, reopened, or
//   reordered.
// * **Per-round view roots** — each round-CLOSING turn pins the canonical
//   root of that round's agreed message set
//   (`dregg_federation::dkg_ceremony::CeremonyView::{dealings_root,
//   responses_root, reveals_root}`) into a slot that is writable ONLY by
//   that one transition and frozen forever after. "We all computed QUAL
//   over the same view" is then checkable against the chain: recompute the
//   root from the published signed messages and compare.
// * **Deadline gates** — a round may close only AFTER its window
//   (`TemporalGate`, the executor's block height), so silence becomes
//   attributable: a dealer who did not answer a complaint by the reveal
//   deadline had the whole window and is disqualified with cause.
// * **The participant set is a TERM** — the roster commitment
//   ([`dkg_roster_root`] over [`dkg_participant_leaf`]s binding index, cell,
//   seal key, AND signing key) is pinned at open, so the per-ceremony
//   factory content-addresses the EXACT participant set; substituting a
//   seal or signing key re-commits to a different ceremony and fails closed.
// * **The output is a commitment** — FINAL requires a nonzero output-slot
//   commitment (`CeremonyPublicOutput::commitment()`: QUAL ‖ the
//   `DkgPublicView` bytes); ABORTED requires it ZERO. A ceremony can
//   never present as both finished and aborted, and the committed output
//   is recomputable by anyone holding the agreed view.
//
// ## What this program CANNOT see (honesty, like the settlement families)
//
// * The roots are commitments, not the messages: the program enforces that
//   SOME root was pinned by the right transition under the right authority
//   at the right height — that the root matches the genuinely-broadcast
//   message set is the transport's auditable obligation
//   (`dregg_federation::dkg_ceremony` signed messages + the node service /
//   blocklace carrying them; any participant recomputes and compares).
// * Slashing is NOT here: an offense (`dkg_ceremony::Offense` — verifiable
//   equivocation pairs, witness-first complaint attribution) is evidence
//   against a participant's obligation bond (`obligation_factory_descriptor`
//   — bond in the cell's own balance, slash = an ordinary move), composed in
//   the adjudication lane (ORGANS §5).
//
// ## Governance shape
//
// Hosted, like the channel group: an admin key (the ceremony coordinator —
// a node operator or a council-held key) gates phase/root/output writes via
// `SenderIs`. Participants AUTHENTICATE their round messages with their own
// roster signing keys (transport layer); the admin merely sequences the
// closes. A coordinator that pins a WRONG root is caught by recomputation
// (and the descriptor's content address names exactly which ceremony it
// betrayed); it cannot forge participants' signed messages.

/// DKG slot 0 — ceremony phase ([`STATE_UNINIT`] → [`DKG_PHASE_DEALING`] →
/// [`DKG_PHASE_COMPLAINT`] → [`DKG_PHASE_REVEAL`] → [`DKG_PHASE_FINAL`] /
/// [`DKG_PHASE_ABORTED`]).
pub const DKG_PHASE_SLOT: u8 = 0;
/// DKG slot 1 — the packed ceremony parameters ([`dkg_params_field`]:
/// committee size n ‖ threshold t). Term-pinned once dealing.
pub const DKG_PARAMS_SLOT: u8 = 1;
/// DKG slot 2 — the participant-set commitment ([`dkg_roster_root`]).
/// Term-pinned once dealing: a ceremony IS its roster (resharing or a retry
/// is a NEW ceremony cell).
pub const DKG_ROSTER_SLOT: u8 = 2;
/// DKG slot 3 — the round-1 agreed-view root (canonical root over the
/// operative signed dealings). Writable only by the DEALING→COMPLAINT
/// transition; frozen forever after.
pub const DKG_DEALINGS_ROOT_SLOT: u8 = 3;
/// DKG slot 4 — the round-2 agreed-view root (acks + complaints). Writable
/// only by the COMPLAINT→REVEAL transition.
pub const DKG_RESPONSES_ROOT_SLOT: u8 = 4;
/// DKG slot 5 — the round-3 agreed-view root (complaint reveals). Writable
/// only by the closing transition into FINAL or ABORTED.
pub const DKG_REVEALS_ROOT_SLOT: u8 = 5;
/// DKG slot 6 — the finalize output commitment
/// (`dregg_federation::dkg_ceremony::CeremonyPublicOutput::commitment()`).
/// Nonzero iff FINAL (zero in every other reachable state).
pub const DKG_OUTPUT_SLOT: u8 = 6;
/// DKG slot 7 — the ceremony coordinator key (term-pinned; `SenderIs` gates
/// phase/root/output writes).
pub const DKG_ADMIN_SLOT: u8 = 7;
/// DKG slot 8 — the ceremony tag (term-pinned, nonzero): names THIS
/// ceremony among the admin's ceremonies and content-addresses the factory.
pub const DKG_TAG_SLOT: u8 = 8;
/// DKG slot 9 — dealing-round deadline (block height, term-pinned): the
/// round may close (→ COMPLAINT) only at `height ≥` this.
pub const DKG_DEALING_DEADLINE_SLOT: u8 = 9;
/// DKG slot 10 — complaint-round deadline (→ REVEAL gate).
pub const DKG_COMPLAINT_DEADLINE_SLOT: u8 = 10;
/// DKG slot 11 — reveal-round deadline (→ FINAL gate; silence past this is
/// attributable, hence the disqualification in `compute_qual` is fair).
pub const DKG_REVEAL_DEADLINE_SLOT: u8 = 11;

/// Phase 1: dealings are being broadcast + private shares delivered.
pub const DKG_PHASE_DEALING: u64 = 1;
/// Phase 2: the dealing set is pinned; acks/complaints accumulate.
pub const DKG_PHASE_COMPLAINT: u64 = 2;
/// Phase 3: the response set is pinned; complained-against dealers reveal.
pub const DKG_PHASE_REVEAL: u64 = 3;
/// Terminal: |QUAL| ≥ t, output commitment pinned. Inert.
pub const DKG_PHASE_FINAL: u64 = 4;
/// Terminal: the ceremony aborted (|QUAL| < t, or killed after timeout).
/// Output stays ZERO — an abort can never impersonate a finish. Inert.
pub const DKG_PHASE_ABORTED: u64 = 5;

/// Domain tag for [`dkg_participant_leaf`].
const DKG_PARTICIPANT_LEAF_DOMAIN: &str = "dregg-dkg-participant-leaf-v1";
/// Domain tag for [`dkg_roster_root`].
const DKG_ROSTER_ROOT_DOMAIN: &str = "dregg-dkg-roster-root-v1";
/// Domain tag for [`dkg_ceremony_token_id`].
const DKG_CEREMONY_TOKEN_DOMAIN: &str = "dregg-dkg-ceremony-token-v1";

/// A ceremony-terms set the blueprint refuses to publish (fail-closed at
/// build). Separate from [`BlueprintError`] so this section stays strictly
/// appended (parallel-lane discipline); the two compose at the service layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DkgBlueprintError {
    /// `n == 0`, `t == 0`, or `t > n` (mirrors the federation
    /// `DkgParams::validate`, duplicated here so the cell crate stays
    /// dependency-clean).
    InvalidParams {
        /// Committee size.
        n: u64,
        /// Threshold.
        t: u64,
    },
    /// Deadlines must satisfy `0 < dealing ≤ complaint ≤ reveal` — a zero
    /// or reordered window would let a round close before it opened.
    BadDeadlines,
    /// An all-zero roster commitment is indistinguishable from an unborn
    /// cell's empty slot.
    ZeroRoster,
    /// A zero admin key would have NO coordinator: every phase write would
    /// refuse forever.
    ZeroCeremonyAdmin,
    /// A zero tag is indistinguishable from an unborn cell.
    ZeroCeremonyTag,
}

impl std::fmt::Display for DkgBlueprintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DkgBlueprintError::InvalidParams { n, t } => {
                write!(f, "invalid DKG ceremony parameters: n={n}, t={t}")
            }
            DkgBlueprintError::BadDeadlines => write!(
                f,
                "ceremony deadlines must satisfy 0 < dealing <= complaint <= reveal"
            ),
            DkgBlueprintError::ZeroRoster => {
                write!(f, "ceremony roster commitment must be nonzero")
            }
            DkgBlueprintError::ZeroCeremonyAdmin => {
                write!(f, "ceremony admin key must be a nonzero field")
            }
            DkgBlueprintError::ZeroCeremonyTag => {
                write!(f, "ceremony tag must be nonzero")
            }
        }
    }
}

impl std::error::Error for DkgBlueprintError {}

/// Pack `(n, t)` into one field element: n big-endian in bytes 8..16, t
/// big-endian in bytes 24..32. Nonzero for every valid parameter set
/// (t ≥ 1), so the pinned term is never confusable with an unborn slot.
pub fn dkg_params_field(n: u64, t: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[8..16].copy_from_slice(&n.to_be_bytes());
    f[24..32].copy_from_slice(&t.to_be_bytes());
    f
}

/// Unpack a [`dkg_params_field`] back to `(n, t)`.
pub fn dkg_params_from_field(f: &FieldElement) -> (u64, u64) {
    let n = u64::from_be_bytes(f[8..16].try_into().expect("8-byte lane"));
    let t = u64::from_be_bytes(f[24..32].try_into().expect("8-byte lane"));
    (n, t)
}

/// One participant leaf: BLAKE3(domain, index ‖ member_cell ‖ seal_pk ‖
/// auth_pk). Binding BOTH keys into the on-cell roster commitment means the
/// share fan-out targets AND the round-message verification keys are pinned
/// by the chain — a key substitution on the off-cell roster re-commits to a
/// different root and fails closed (the channel-member-leaf shape, plus the
/// signing key, because DKG rounds must be attributable).
pub fn dkg_participant_leaf(
    index: u64,
    member_cell: &[u8; 32],
    seal_pk: &[u8; 32],
    auth_pk: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(DKG_PARTICIPANT_LEAF_DOMAIN);
    hasher.update(&index.to_le_bytes());
    hasher.update(member_cell);
    hasher.update(seal_pk);
    hasher.update(auth_pk);
    *hasher.finalize().as_bytes()
}

/// Canonical openable commitment over the participant-leaf set: BLAKE3 over
/// the length-prefixed SORTED leaves (the channel-member-root shape).
pub fn dkg_roster_root(leaves: &std::collections::BTreeSet<[u8; 32]>) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key(DKG_ROSTER_ROOT_DOMAIN);
    hasher.update(&(leaves.len() as u64).to_le_bytes());
    for leaf in leaves {
        hasher.update(leaf);
    }
    *hasher.finalize().as_bytes()
}

/// The ceremony cell's token id: BLAKE3(domain, admin ‖ tag ‖ roster_root).
/// Binding the roster into the token means the ceremony's CELL ID names its
/// exact participant set — the id every round message is signed against.
pub fn dkg_ceremony_token_id(
    admin: &FieldElement,
    tag: &FieldElement,
    roster_root: &FieldElement,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(DKG_CEREMONY_TOKEN_DOMAIN);
    hasher.update(admin);
    hasher.update(tag);
    hasher.update(roster_root);
    *hasher.finalize().as_bytes()
}

/// The published terms of one DKG ceremony. ALL of these are term-pinned
/// (the ceremony's whole shape is decided at birth; only the phase, the
/// round roots, and the output commitment are live state).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgCeremonyTerms {
    /// Committee size n (participants are indexed 1..=n).
    pub n: u64,
    /// Threshold t.
    pub t: u64,
    /// The participant-set commitment ([`dkg_roster_root`]).
    pub roster_root: FieldElement,
    /// The ceremony coordinator key (`SenderIs` gate over phase/root/output
    /// writes). An operator key, or a council-held key.
    pub admin: FieldElement,
    /// Ceremony tag (nonzero): names THIS ceremony among the admin's.
    pub tag: FieldElement,
    /// Block height the dealing round may close at (≥).
    pub dealing_deadline: u64,
    /// Block height the complaint round may close at (≥).
    pub complaint_deadline: u64,
    /// Block height the reveal round may close at (≥) — the finalize gate.
    pub reveal_deadline: u64,
}

/// The DKG-ceremony constraint set. The teeth, in keystone order:
///
/// 1. **term pins** — params, roster, admin, tag, the three deadlines
///    (`pin_term`: immutable once out of UNINIT);
/// 2. **the phase machine** — `AllowedTransitions` forward-only
///    (UNINIT→DEALING→COMPLAINT→REVEAL→FINAL, aborts from any live round),
///    NO self-rows on live rounds (between closes the cell is quiet) and no
///    rows out of FINAL/ABORTED (terminals inert);
/// 3. **round roots write-once-at-close** — each root slot may change only
///    in a turn whose POST-phase is the phase that round's close enters
///    (and each such phase is entered exactly once, so the root is frozen
///    forever after); entering a post-round phase REQUIRES its closing root
///    nonzero (a close must pin SOMETHING);
/// 4. **deadline gates** — each close admits only at `height ≥` its
///    published deadline (`TemporalGate`), making silence attributable;
///    an abort is gated on the dealing deadline (no pre-window griefing);
/// 5. **output discipline** — the output slot may change only entering
///    FINAL; FINAL requires it nonzero; ABORTED requires it ZERO;
/// 6. **governance** — phase, roots, and output writes admit only the admin
///    sender (`AnyOf[Immutable{slot}, SenderIs{admin}]`, the channel-group
///    per-slot actor binding).
pub fn dkg_ceremony_state_constraints(
    terms: &DkgCeremonyTerms,
) -> Result<Vec<StateConstraint>, DkgBlueprintError> {
    if terms.n == 0 || terms.t == 0 || terms.t > terms.n {
        return Err(DkgBlueprintError::InvalidParams {
            n: terms.n,
            t: terms.t,
        });
    }
    if terms.dealing_deadline == 0
        || terms.complaint_deadline < terms.dealing_deadline
        || terms.reveal_deadline < terms.complaint_deadline
    {
        return Err(DkgBlueprintError::BadDeadlines);
    }
    if terms.roster_root == FIELD_ZERO {
        return Err(DkgBlueprintError::ZeroRoster);
    }
    if terms.admin == FIELD_ZERO {
        return Err(DkgBlueprintError::ZeroCeremonyAdmin);
    }
    if terms.tag == FIELD_ZERO {
        return Err(DkgBlueprintError::ZeroCeremonyTag);
    }
    let admin_gated = |slot: u8| StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: slot },
            SimpleStateConstraint::SenderIs { pk: terms.admin },
        ],
    };
    // `slot` changes ⇒ the post-phase is `phase` (the write-once-at-close
    // window: the phase machine enters each post-round phase exactly once).
    let writable_only_entering = |slot: u8, phase: u64| StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: slot },
            state_is(phase),
        ],
    };
    let nonzero = |slot: u8| {
        SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
            index: slot,
            value: FIELD_ZERO,
        }))
    };
    Ok(vec![
        // ── 1. term pins ──
        pin_term(DKG_PARAMS_SLOT, dkg_params_field(terms.n, terms.t)),
        pin_term(DKG_ROSTER_SLOT, terms.roster_root),
        pin_term(DKG_ADMIN_SLOT, terms.admin),
        pin_term(DKG_TAG_SLOT, terms.tag),
        pin_term(
            DKG_DEALING_DEADLINE_SLOT,
            field_from_u64(terms.dealing_deadline),
        ),
        pin_term(
            DKG_COMPLAINT_DEADLINE_SLOT,
            field_from_u64(terms.complaint_deadline),
        ),
        pin_term(
            DKG_REVEAL_DEADLINE_SLOT,
            field_from_u64(terms.reveal_deadline),
        ),
        // ── 2. the phase machine (forward-only; terminals inert) ──
        StateConstraint::AllowedTransitions {
            slot_index: DKG_PHASE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (
                    field_from_u64(STATE_UNINIT),
                    field_from_u64(DKG_PHASE_DEALING),
                ),
                (
                    field_from_u64(DKG_PHASE_DEALING),
                    field_from_u64(DKG_PHASE_COMPLAINT),
                ),
                (
                    field_from_u64(DKG_PHASE_COMPLAINT),
                    field_from_u64(DKG_PHASE_REVEAL),
                ),
                (
                    field_from_u64(DKG_PHASE_REVEAL),
                    field_from_u64(DKG_PHASE_FINAL),
                ),
                (
                    field_from_u64(DKG_PHASE_DEALING),
                    field_from_u64(DKG_PHASE_ABORTED),
                ),
                (
                    field_from_u64(DKG_PHASE_COMPLAINT),
                    field_from_u64(DKG_PHASE_ABORTED),
                ),
                (
                    field_from_u64(DKG_PHASE_REVEAL),
                    field_from_u64(DKG_PHASE_ABORTED),
                ),
            ],
        },
        // ── 3. round roots: write-once-at-close + close-pins-something ──
        writable_only_entering(DKG_DEALINGS_ROOT_SLOT, DKG_PHASE_COMPLAINT),
        writable_only_entering(DKG_RESPONSES_ROOT_SLOT, DKG_PHASE_REVEAL),
        // The reveal root closes into EITHER terminal (an abort still pins
        // the reveal record — the slash evidence survives the failure).
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable {
                    index: DKG_REVEALS_ROOT_SLOT,
                },
                state_is(DKG_PHASE_FINAL),
                state_is(DKG_PHASE_ABORTED),
            ],
        },
        when_state(DKG_PHASE_COMPLAINT, nonzero(DKG_DEALINGS_ROOT_SLOT)),
        when_state(DKG_PHASE_REVEAL, nonzero(DKG_RESPONSES_ROOT_SLOT)),
        when_state(DKG_PHASE_FINAL, nonzero(DKG_REVEALS_ROOT_SLOT)),
        // ── 4. deadline gates (rounds close only after their windows) ──
        when_state(
            DKG_PHASE_COMPLAINT,
            SimpleStateConstraint::TemporalGate {
                not_before: Some(terms.dealing_deadline),
                not_after: None,
            },
        ),
        when_state(
            DKG_PHASE_REVEAL,
            SimpleStateConstraint::TemporalGate {
                not_before: Some(terms.complaint_deadline),
                not_after: None,
            },
        ),
        when_state(
            DKG_PHASE_FINAL,
            SimpleStateConstraint::TemporalGate {
                not_before: Some(terms.reveal_deadline),
                not_after: None,
            },
        ),
        when_state(
            DKG_PHASE_ABORTED,
            SimpleStateConstraint::TemporalGate {
                not_before: Some(terms.dealing_deadline),
                not_after: None,
            },
        ),
        // ── 5. output discipline (FINAL ⇔ committed output) ──
        writable_only_entering(DKG_OUTPUT_SLOT, DKG_PHASE_FINAL),
        when_state(DKG_PHASE_FINAL, nonzero(DKG_OUTPUT_SLOT)),
        when_state(
            DKG_PHASE_ABORTED,
            SimpleStateConstraint::FieldEquals {
                index: DKG_OUTPUT_SLOT,
                value: FIELD_ZERO,
            },
        ),
        // ── 6. governance: the admin sequences the ceremony ──
        admin_gated(DKG_PHASE_SLOT),
        admin_gated(DKG_DEALINGS_ROOT_SLOT),
        admin_gated(DKG_RESPONSES_ROOT_SLOT),
        admin_gated(DKG_REVEALS_ROOT_SLOT),
        admin_gated(DKG_OUTPUT_SLOT),
    ])
}

/// The `CellProgram` installed on the ceremony cell for its whole life.
pub fn dkg_ceremony_cell_program(
    terms: &DkgCeremonyTerms,
) -> Result<CellProgram, DkgBlueprintError> {
    Ok(CellProgram::Predicate(dkg_ceremony_state_constraints(
        terms,
    )?))
}

/// **The DKG-ceremony factory (per-ceremony, content-addressed)** — the
/// ORGANS §6 upgrade-path cell ("DKG replaces the dealer"). Like the
/// settlement families, each ceremony gets its own descriptor whose
/// constraints bake every term (params, roster, deadlines, coordinator) as
/// literals; the factory births exactly ONE cell.
pub fn dkg_ceremony_factory_descriptor(
    terms: &DkgCeremonyTerms,
) -> Result<FactoryDescriptor, DkgBlueprintError> {
    Ok(settlement_descriptor(
        "dregg-blueprint:dkg-ceremony-factory v1",
        dkg_ceremony_state_constraints(terms)?,
    ))
}

// =============================================================================
// DKG-ceremony program tests (executor-independent half; the end-to-end half
// rides the node service tests, `node/src/dkg_service.rs`)
// =============================================================================

#[cfg(test)]
mod dkg_ceremony_tests {
    use super::*;
    use crate::preconditions::EvalContext;
    use crate::program::{TransitionMeta, WitnessBundle};
    use crate::state::CellState;

    const ADMIN: FieldElement = [0xAD; 32];
    const STRANGER: FieldElement = [0x66; 32];

    fn terms() -> DkgCeremonyTerms {
        DkgCeremonyTerms {
            n: 5,
            t: 3,
            roster_root: [0x77; 32],
            admin: ADMIN,
            tag: field_from_u64(42),
            dealing_deadline: 10,
            complaint_deadline: 20,
            reveal_deadline: 30,
        }
    }

    fn ctx(height: u64, sender: Option<FieldElement>) -> EvalContext {
        EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender,
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }

    fn eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
        sender: Option<FieldElement>,
    ) -> Result<(), crate::program::ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(&ctx(height, sender)),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    /// The post-open (DEALING) state of the canonical test ceremony.
    fn dealing_state(t: &DkgCeremonyTerms) -> CellState {
        let mut s = CellState::new(0);
        s.fields[DKG_PHASE_SLOT as usize] = field_from_u64(DKG_PHASE_DEALING);
        s.fields[DKG_PARAMS_SLOT as usize] = dkg_params_field(t.n, t.t);
        s.fields[DKG_ROSTER_SLOT as usize] = t.roster_root;
        s.fields[DKG_ADMIN_SLOT as usize] = t.admin;
        s.fields[DKG_TAG_SLOT as usize] = t.tag;
        s.fields[DKG_DEALING_DEADLINE_SLOT as usize] = field_from_u64(t.dealing_deadline);
        s.fields[DKG_COMPLAINT_DEADLINE_SLOT as usize] = field_from_u64(t.complaint_deadline);
        s.fields[DKG_REVEAL_DEADLINE_SLOT as usize] = field_from_u64(t.reveal_deadline);
        s
    }

    fn at_phase(t: &DkgCeremonyTerms, phase: u64) -> CellState {
        let mut s = dealing_state(t);
        s.fields[DKG_PHASE_SLOT as usize] = field_from_u64(phase);
        if phase >= DKG_PHASE_COMPLAINT {
            s.fields[DKG_DEALINGS_ROOT_SLOT as usize] = [0xD1; 32];
        }
        if phase >= DKG_PHASE_REVEAL {
            s.fields[DKG_RESPONSES_ROOT_SLOT as usize] = [0xD2; 32];
        }
        if phase >= DKG_PHASE_FINAL {
            s.fields[DKG_REVEALS_ROOT_SLOT as usize] = [0xD3; 32];
        }
        if phase == DKG_PHASE_FINAL {
            s.fields[DKG_OUTPUT_SLOT as usize] = [0xF1; 32];
        }
        s
    }

    #[test]
    fn refused_terms_fail_closed_at_build() {
        let ok = terms();
        assert!(dkg_ceremony_factory_descriptor(&ok).is_ok());
        let mut bad = ok.clone();
        bad.t = 6; // t > n
        assert_eq!(
            dkg_ceremony_state_constraints(&bad).unwrap_err(),
            DkgBlueprintError::InvalidParams { n: 5, t: 6 }
        );
        let mut bad = ok.clone();
        bad.reveal_deadline = 15; // < complaint deadline
        assert_eq!(
            dkg_ceremony_state_constraints(&bad).unwrap_err(),
            DkgBlueprintError::BadDeadlines
        );
        let mut bad = ok.clone();
        bad.roster_root = FIELD_ZERO;
        assert_eq!(
            dkg_ceremony_state_constraints(&bad).unwrap_err(),
            DkgBlueprintError::ZeroRoster
        );
        let mut bad = ok.clone();
        bad.admin = FIELD_ZERO;
        assert_eq!(
            dkg_ceremony_state_constraints(&bad).unwrap_err(),
            DkgBlueprintError::ZeroCeremonyAdmin
        );
        let mut bad = ok;
        bad.tag = FIELD_ZERO;
        assert_eq!(
            dkg_ceremony_state_constraints(&bad).unwrap_err(),
            DkgBlueprintError::ZeroCeremonyTag
        );
    }

    #[test]
    fn birth_and_open_pass_and_term_tamper_refuses() {
        let t = terms();
        let p = dkg_ceremony_cell_program(&t).unwrap();
        let born = CellState::new(0);
        assert!(eval(&p, &born, None, 0, None).is_ok(), "birth state passes");
        let open = dealing_state(&t);
        assert!(
            eval(&p, &open, Some(&born), 1, Some(ADMIN)).is_ok(),
            "open writes the terms"
        );
        // Tampered params / roster / deadline refuse at open.
        for (slot, val) in [
            (DKG_PARAMS_SLOT, dkg_params_field(5, 2)),
            (DKG_ROSTER_SLOT, [0x78; 32]),
            (DKG_DEALING_DEADLINE_SLOT, field_from_u64(11)),
        ] {
            let mut bad = open.clone();
            bad.fields[slot as usize] = val;
            assert!(
                eval(&p, &bad, Some(&born), 1, Some(ADMIN)).is_err(),
                "term pin must bite on slot {slot}"
            );
        }
        // Re-writing a term while live refuses, even for the admin.
        let mut rewrite = open.clone();
        rewrite.fields[DKG_REVEAL_DEADLINE_SLOT as usize] = field_from_u64(31);
        assert!(eval(&p, &rewrite, Some(&open), 1, Some(ADMIN)).is_err());
    }

    #[test]
    fn rounds_close_in_order_after_their_deadlines_only() {
        let t = terms();
        let p = dkg_ceremony_cell_program(&t).unwrap();
        let open = dealing_state(&t);

        // Skipping a round refuses (DEALING → REVEAL).
        let skip = at_phase(&t, DKG_PHASE_REVEAL);
        assert!(eval(&p, &skip, Some(&open), 25, Some(ADMIN)).is_err());

        // Closing the dealing round: height 9 < 10 refuses; height 10 passes
        // WITH a pinned root and the admin sender.
        let close1 = at_phase(&t, DKG_PHASE_COMPLAINT);
        assert!(eval(&p, &close1, Some(&open), 9, Some(ADMIN)).is_err());
        assert!(eval(&p, &close1, Some(&open), 10, Some(ADMIN)).is_ok());
        // ... but NOT without the root (close must pin something) ...
        let mut rootless = close1.clone();
        rootless.fields[DKG_DEALINGS_ROOT_SLOT as usize] = FIELD_ZERO;
        assert!(eval(&p, &rootless, Some(&open), 10, Some(ADMIN)).is_err());
        // ... and NOT for a stranger.
        assert!(eval(&p, &close1, Some(&open), 10, Some(STRANGER)).is_err());
        assert!(eval(&p, &close1, Some(&open), 10, None).is_err());

        // Closing the complaint round (root freeze checked next test).
        let close2 = at_phase(&t, DKG_PHASE_REVEAL);
        assert!(eval(&p, &close2, Some(&close1), 19, Some(ADMIN)).is_err());
        assert!(eval(&p, &close2, Some(&close1), 20, Some(ADMIN)).is_ok());

        // Finalize: needs the reveal deadline, the reveals root, AND a
        // nonzero output commitment.
        let fin = at_phase(&t, DKG_PHASE_FINAL);
        assert!(eval(&p, &fin, Some(&close2), 29, Some(ADMIN)).is_err());
        assert!(eval(&p, &fin, Some(&close2), 30, Some(ADMIN)).is_ok());
        let mut no_out = fin.clone();
        no_out.fields[DKG_OUTPUT_SLOT as usize] = FIELD_ZERO;
        assert!(eval(&p, &no_out, Some(&close2), 30, Some(ADMIN)).is_err());
        let mut no_reveals = fin.clone();
        no_reveals.fields[DKG_REVEALS_ROOT_SLOT as usize] = FIELD_ZERO;
        assert!(eval(&p, &no_reveals, Some(&close2), 30, Some(ADMIN)).is_err());
    }

    #[test]
    fn pinned_roots_freeze_forever() {
        let t = terms();
        let p = dkg_ceremony_cell_program(&t).unwrap();
        let close1 = at_phase(&t, DKG_PHASE_COMPLAINT);
        // The complaint-round close may NOT also rewrite the dealing root.
        let mut close2 = at_phase(&t, DKG_PHASE_REVEAL);
        close2.fields[DKG_DEALINGS_ROOT_SLOT as usize] = [0xEE; 32];
        assert!(
            eval(&p, &close2, Some(&close1), 20, Some(ADMIN)).is_err(),
            "a pinned round root must never move again"
        );
        // Nor may the finalize rewrite the responses root.
        let close2 = at_phase(&t, DKG_PHASE_REVEAL);
        let mut fin = at_phase(&t, DKG_PHASE_FINAL);
        fin.fields[DKG_RESPONSES_ROOT_SLOT as usize] = [0xEF; 32];
        assert!(eval(&p, &fin, Some(&close2), 30, Some(ADMIN)).is_err());
    }

    #[test]
    fn abort_is_gated_zero_output_and_terminal() {
        let t = terms();
        let p = dkg_ceremony_cell_program(&t).unwrap();
        let open = dealing_state(&t);

        // An abort before the dealing window closes refuses (no griefing).
        let mut abort = open.clone();
        abort.fields[DKG_PHASE_SLOT as usize] = field_from_u64(DKG_PHASE_ABORTED);
        assert!(eval(&p, &abort, Some(&open), 9, Some(ADMIN)).is_err());
        assert!(eval(&p, &abort, Some(&open), 10, Some(ADMIN)).is_ok());

        // An abort impersonating a finish (nonzero output) refuses.
        let mut fake = abort.clone();
        fake.fields[DKG_OUTPUT_SLOT as usize] = [0xF1; 32];
        assert!(eval(&p, &fake, Some(&open), 10, Some(ADMIN)).is_err());

        // Terminals are inert: any touch of FINAL or ABORTED refuses.
        assert!(eval(&p, &abort, Some(&abort), 40, Some(ADMIN)).is_err());
        let close2 = at_phase(&t, DKG_PHASE_REVEAL);
        let fin = at_phase(&t, DKG_PHASE_FINAL);
        assert!(eval(&p, &fin, Some(&close2), 30, Some(ADMIN)).is_ok());
        assert!(eval(&p, &fin, Some(&fin), 40, Some(ADMIN)).is_err());
        let mut reopened = fin.clone();
        reopened.fields[DKG_PHASE_SLOT as usize] = field_from_u64(DKG_PHASE_REVEAL);
        assert!(eval(&p, &reopened, Some(&fin), 40, Some(ADMIN)).is_err());
    }

    #[test]
    fn descriptors_content_address_the_ceremony() {
        let a = dkg_ceremony_factory_descriptor(&terms()).unwrap();
        // Same terms ⇒ same factory (re-derivable by any party).
        let b = dkg_ceremony_factory_descriptor(&terms()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk);
        assert_eq!(a.creation_budget, Some(1));
        // Any varied term ⇒ a different ceremony.
        let mut other = terms();
        other.roster_root = [0x79; 32];
        let c = dkg_ceremony_factory_descriptor(&other).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk);
        // Params round-trip through the packed field.
        assert_eq!(dkg_params_from_field(&dkg_params_field(5, 3)), (5, 3));
    }
}
