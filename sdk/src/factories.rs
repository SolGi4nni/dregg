//! # Settlement-factory builders — the dregg3 SDK surface for escrow /
//! obligation / bridge-cell deals over SURVIVING verbs only.
//!
//! Per `metatheory/Dregg2/Substrate/VerbRegistry.lean`, the kernel verb
//! families `CreateEscrow/ReleaseEscrow/RefundEscrow` (+ the `Committed`
//! trio), `CreateObligation/FulfillObligation/SlashObligation`, and
//! `BridgeLock/BridgeFinalize/BridgeCancel` are classified `factory`: their
//! arms dissolve, and their behavior re-lands as factory-born cells whose
//! [`dregg_cell::blueprint`] programs enforce the same safety. **No builder in
//! this module constructs any of those doomed variants.** Every turn here is
//! made of exactly four surviving verbs:
//!
//! * [`Effect::CreateCellFromFactory`] — birth the per-deal settlement cell,
//! * [`Effect::SetField`] — write the deal terms / drive the state machine,
//! * [`Effect::Transfer`] — move the locked value (the value lives in the
//!   settlement cell's own `balance`; NO side-table),
//! * [`Effect::GrantCapability`] — the one-time adopt self-grant that gives
//!   the operator driving reach over the born cell (survivor verb `.grant`).
//!
//! The safety is NOT in these builders: it is in the [`CellProgram`] the
//! factory installs on the cell, which the executor re-evaluates on EVERY
//! turn that touches it (`turn/src/executor/execute_tree.rs`). A caller who
//! bypasses this module and hand-writes a turn against a settlement cell
//! faces the same program gate. What the builders add is the ONE sensible
//! turn shape for each step (in particular: the payout `Transfer` targets the
//! counterparty PUBLISHED in the deal terms, and moves the published amount).
//!
//! ## Lean provenance (the proved spec each family mirrors)
//!
//! | family     | Lean module                      | keystones                                              |
//! |------------|----------------------------------|--------------------------------------------------------|
//! | escrow     | `Dregg2.Apps.EscrowFactory`      | `no_double_resolve`, `release_requires_condition`, `release_conserves`/`refund_conserves`, `open_releasable`/`open_refundable` |
//! | obligation | `Dregg2.Apps.ObligationFactory`  | `no_double_resolve_{fulfilled,slashed}`, `fulfil_requires_condition`, `slash_requires_deadline`, `slash_rejects_when_condition_met` |
//! | bridge     | `Dregg2.Apps.BridgeCell`         | `no_double_finalize`, `no_refinalize_after_cancel`, `finalize_requires_finality_witness`, `locked_cancellable` |
//!
//! ## Deal lifecycle (all three families)
//!
//! 1. **Plan** — `create_*_cell(..)` builds a [`SettlementCellPlan`]: the
//!    per-deal content-addressed [`FactoryDescriptor`] plus four turns.
//! 2. **Deploy** — register `plan.descriptor` with the executor
//!    (`AgentRuntime::deploy_factory`).
//! 3. **Create** — the creator executes `plan.create_effects` (one
//!    `CreateCellFromFactory`, an ordinary agent turn). The cell is born
//!    all-zero with the deal's program installed for life, owned by
//!    `owner_pubkey`.
//! 4. **Fund** — the funder executes `plan.fund_effects`: one `Transfer` of
//!    `value + ADOPT_TURN_FEE` into the cell ([`ADOPT_TURN_FEE`] is the fee
//!    the adopt turn burns; exactly `value` remains for settlement).
//! 5. **Adopt** — the OWNER runs `plan.adopt_effects` as a cell-agent turn
//!    (`AgentRuntime::execute_as(plan.cell_id, .., ADOPT_TURN_FEE)`): the
//!    cell self-grants the operator a c-list capability on itself. This is
//!    the in-band, effect-level form of the node's seed-time operator grant.
//! 6. **Open** — the operator executes `plan.open_effects` via
//!    `AgentRuntime::execute_on(plan.cell_id, ..)`: the deal terms are
//!    written and the state steps to OPEN (`SetField`×6). From this turn on,
//!    every term slot is pinned to the descriptor's published literal — the
//!    program rejects any rewrite.
//! 7. **Resolve** — exactly one of the two resolve builders commits (again
//!    via `execute_on`); the program then makes the cell terminally inert
//!    (no-double-resolve).
//!
//! ## Who drives the cell (authority model)
//!
//! A settlement cell is driven by turns whose ACTION TARGETS the cell,
//! signed by its `owner_pubkey` (the executor verifies the Ed25519 signature
//! against the target cell's own key) and reached through the operator's
//! c-list capability (the parent gate). The operator's agent cell is the
//! turn agent and pays the fees. This is the same shape the node's ingress
//! uses for factory-born app cells. Authority to ATTEMPT a transition is the
//! owner key + the capability; whether the transition COMMITS is decided
//! solely by the installed program (a depositor who owns the escrow cell
//! still cannot release without the condition witness — the program, not the
//! signature, is the safety gate).

use dregg_cell::blueprint::{
    BlueprintError, BridgeTerms, CONDITION_SLOT, DEADLINE_SLOT, EscrowTerms, ObligationTerms,
    PARTY_A_SLOT, PARTY_B_SLOT, STATE_OPEN, STATE_RESOLVED_A, STATE_RESOLVED_B, STATE_SLOT,
    VALUE_SLOT, WITNESS_SLOT, bridge_factory_descriptor, escrow_factory_descriptor,
    obligation_factory_descriptor,
};
use dregg_cell::state::FieldElement;
use dregg_cell::{
    AuthRequired, CapabilityRef, CellId, CellMode, FactoryCreationParams, FactoryDescriptor,
    field_from_u64,
};
use dregg_turn::Effect;

/// The fee (= computron budget) the one-time adopt turn burns from the
/// settlement cell's balance. [`SettlementCellPlan::fund_effects`] transfers
/// `value + ADOPT_TURN_FEE` so that exactly `value` remains locked after the
/// adopt turn commits. Comfortably covers the adopt turn's metered cost
/// (action base + signature verify + one effect + per-byte).
pub const ADOPT_TURN_FEE: u64 = 2_000;

/// Encode a cell identity as a 32-byte deal-term party field
/// ([`PARTY_A_SLOT`] / [`PARTY_B_SLOT`]).
pub fn party_field(cell: CellId) -> FieldElement {
    *cell.as_bytes()
}

/// Decode a deal-term party field back into the [`CellId`] the settle
/// `Transfer` targets.
fn party_cell(field: FieldElement) -> CellId {
    CellId::from_bytes(field)
}

/// A planned settlement deal: the published factory + the four turns that
/// birth, fund, adopt, and open it. See the module docs for the lifecycle.
#[derive(Clone, Debug)]
pub struct SettlementCellPlan {
    /// The per-deal, content-addressed factory descriptor. Deploy this to the
    /// executor BEFORE executing [`Self::create_effects`] — its
    /// `state_constraints` are the verified state machine the executor
    /// installs on the born cell.
    pub descriptor: FactoryDescriptor,
    /// `descriptor.factory_vk`, for convenience.
    pub factory_vk: [u8; 32],
    /// The deterministic id of the settlement cell
    /// (`CellId::derive_raw(owner_pubkey, token_id)`).
    pub cell_id: CellId,
    /// Turn 1 (creator's agent turn): birth the cell from the factory
    /// (surviving verb `CreateCellFromFactory`, nothing else).
    pub create_effects: Vec<Effect>,
    /// Turn 2 (funder's agent turn): move `value + ADOPT_TURN_FEE` into the
    /// settlement cell's own balance (one `Transfer` from the funder's cell).
    pub fund_effects: Vec<Effect>,
    /// Turn 3 (cell-agent turn —
    /// `AgentRuntime::execute_as(cell_id, .., ADOPT_TURN_FEE)`): the cell
    /// self-grants the operator a c-list capability on itself (surviving verb
    /// `GrantCapability`, one edge, non-amplifying — the implicit self-cap is
    /// the held authority). After this turn exactly `value` remains in the
    /// cell.
    pub adopt_effects: Vec<Effect>,
    /// Turn 4 (operator turn — `AgentRuntime::execute_on(cell_id, ..)`):
    /// write the deal terms and step the state to OPEN (`SetField`×6). The
    /// program gates this turn: the written terms must equal the descriptor's
    /// published literals.
    pub open_effects: Vec<Effect>,
}

/// Shared plan constructor over the three families' common slot schema.
fn settlement_plan(
    descriptor: FactoryDescriptor,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
    value: u64,
    party_a: FieldElement,
    party_b: FieldElement,
    condition: FieldElement,
    deadline_height: u64,
) -> SettlementCellPlan {
    let factory_vk = descriptor.factory_vk;
    let cell_id = CellId::derive_raw(&owner_pubkey, &token_id);
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: descriptor.child_program_vk,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };
    let create_effects = vec![Effect::CreateCellFromFactory {
        factory_vk,
        owner_pubkey,
        token_id,
        params,
    }];
    let set = |index: u8, value: FieldElement| Effect::SetField {
        cell: cell_id,
        index: index as usize,
        value,
    };
    let fund_effects = vec![Effect::Transfer {
        from: funder,
        to: cell_id,
        amount: value + ADOPT_TURN_FEE,
    }];
    // The cell self-grants the operator driving reach. Non-amplifying: the
    // granter's held authority is the implicit self-cap (⊤ on every axis);
    // the executor's self-grant arm authorizes it by the owner signature.
    let adopt_effects = vec![Effect::GrantCapability {
        from: cell_id,
        to: operator,
        cap: CapabilityRef {
            target: cell_id,
            slot: 0, // assigned by the recipient c-list at install
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }];
    let open_effects = vec![
        set(VALUE_SLOT, field_from_u64(value)),
        set(PARTY_A_SLOT, party_a),
        set(PARTY_B_SLOT, party_b),
        set(CONDITION_SLOT, condition),
        set(DEADLINE_SLOT, field_from_u64(deadline_height)),
        set(STATE_SLOT, field_from_u64(STATE_OPEN)),
    ];
    SettlementCellPlan {
        descriptor,
        factory_vk,
        cell_id,
        create_effects,
        fund_effects,
        adopt_effects,
        open_effects,
    }
}

/// Shared resolve-turn shape: exhibit a witness (optional), step the state
/// machine, and pay the published amount to the published counterparty.
/// Resolve turns run via `AgentRuntime::execute_on(cell, ..)` — the cell is
/// the action target, so the payout `Transfer` draws from the cell's own
/// balance under the owner's signature + the operator's capability, and the
/// installed program decides commit/reject.
fn resolve_effects(
    cell: CellId,
    witness: Option<FieldElement>,
    next_state: u64,
    payout_to: FieldElement,
    amount: u64,
) -> Vec<Effect> {
    let mut effects = Vec::with_capacity(3);
    if let Some(w) = witness {
        effects.push(Effect::SetField {
            cell,
            index: WITNESS_SLOT as usize,
            value: w,
        });
    }
    effects.push(Effect::SetField {
        cell,
        index: STATE_SLOT as usize,
        value: field_from_u64(next_state),
    });
    effects.push(Effect::Transfer {
        from: cell,
        to: party_cell(payout_to),
        amount,
    });
    effects
}

// =============================================================================
// Escrow — Dregg2.Apps.EscrowFactory
// =============================================================================

/// Plan a new escrow deal — the land-before-kill replacement for
/// `Effect::CreateEscrow`.
///
/// **Safety contract** (enforced by the installed cell program, proved on the
/// Lean twin `Dregg2.Apps.EscrowFactory`):
/// * the deal terms (`amount`/`depositor`/`beneficiary`/`condition`/
///   `timeout_height`) are pinned to the descriptor's published literals from
///   the open turn on (the per-deal `Immutable` caveats);
/// * the only transitions ever admitted are OPEN→RELEASED and OPEN→REFUNDED
///   (`no_double_resolve`);
/// * the locked value is held in the escrow cell's own balance — funding and
///   settling are ordinary conserving `Transfer`s (`release_conserves`,
///   `refund_conserves`), no side-table.
///
/// `terms.depositor` / `terms.beneficiary` should be [`party_field`]
/// encodings of the cells the refund / release transfers will target.
/// `funder` is the cell the fund turn draws `terms.amount` from (typically
/// the depositor's cell). Fails closed on a zero `condition`.
pub fn create_escrow_cell(
    terms: &EscrowTerms,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<SettlementCellPlan, BlueprintError> {
    Ok(settlement_plan(
        escrow_factory_descriptor(terms)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        terms.amount,
        terms.depositor,
        terms.beneficiary,
        terms.condition,
        terms.timeout_height,
    ))
}

/// Build the release turn for an open escrow — the replacement for
/// `Effect::ReleaseEscrow`.
///
/// **Safety contract**: the turn exhibits `witness` in the cell's witness
/// slot and steps OPEN→RELEASED; the cell program commits it ONLY if
/// `witness` equals the published condition (Lean
/// `release_requires_condition`) and the escrow is still OPEN (Lean
/// `no_double_resolve`). The payout `Transfer` moves the published amount to
/// the published beneficiary — there is no other turn shape this builder can
/// produce. A wrong or missing witness is rejected by the EXECUTOR
/// (`TurnError::ProgramViolation`), not by this builder.
pub fn release_escrow(escrow: CellId, terms: &EscrowTerms, witness: FieldElement) -> Vec<Effect> {
    resolve_effects(
        escrow,
        Some(witness),
        STATE_RESOLVED_A,
        terms.beneficiary,
        terms.amount,
    )
}

/// Build the refund turn for an open escrow — the replacement for
/// `Effect::RefundEscrow`.
///
/// **Safety contract**: steps OPEN→REFUNDED and returns the published amount
/// to the published depositor. When the deal published a nonzero
/// `timeout_height`, the cell program admits this turn only at
/// `block_height >= timeout_height`; with a zero timeout, refund is admitted
/// any time while OPEN (exactly the Lean `escrowRefund` / `open_refundable`).
/// A refund of an already-resolved escrow is rejected (`no_double_resolve`).
pub fn refund_escrow(escrow: CellId, terms: &EscrowTerms) -> Vec<Effect> {
    resolve_effects(
        escrow,
        None,
        STATE_RESOLVED_B,
        terms.depositor,
        terms.amount,
    )
}

// =============================================================================
// Obligation — Dregg2.Apps.ObligationFactory
// =============================================================================

/// Plan a new bonded proof obligation — the replacement for
/// `Effect::CreateObligation`.
///
/// **Safety contract** (Lean twin `Dregg2.Apps.ObligationFactory`): the bond
/// is held in the obligation cell's own balance; the terms are pinned from
/// the open turn on; the only admitted resolutions are OPEN→FULFILLED
/// (condition witness exhibited, bond back to the obligor) and OPEN→SLASHED
/// (deadline reached AND condition NOT exhibited, bond forfeited to the
/// obligee); a resolved obligation is inert
/// (`no_double_resolve_{fulfilled,slashed}`). Fails closed on a zero
/// `condition` or a zero `deadline_height`.
///
/// `funder` is the cell the bond is posted from (typically the obligor's).
pub fn create_obligation_cell(
    terms: &ObligationTerms,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<SettlementCellPlan, BlueprintError> {
    Ok(settlement_plan(
        obligation_factory_descriptor(terms)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        terms.bond,
        terms.obligor,
        terms.obligee,
        terms.condition,
        terms.deadline_height,
    ))
}

/// Build the fulfil turn for an open obligation — the replacement for
/// `Effect::FulfillObligation`.
///
/// **Safety contract**: exhibits `witness` and steps OPEN→FULFILLED; the cell
/// program commits it ONLY if `witness` equals the published discharge
/// condition (Lean `fulfil_requires_condition`); the bond returns to the
/// published obligor. Fulfilment is time-ungated (a proof may discharge the
/// obligation any time before it is slashed).
pub fn fulfill_obligation(
    obligation: CellId,
    terms: &ObligationTerms,
    witness: FieldElement,
) -> Vec<Effect> {
    resolve_effects(
        obligation,
        Some(witness),
        STATE_RESOLVED_A,
        terms.obligor,
        terms.bond,
    )
}

/// Build the slash turn for an open obligation — the replacement for
/// `Effect::SlashObligation`.
///
/// **Safety contract**: steps OPEN→SLASHED and forfeits the bond to the
/// published obligee. The cell program admits this ONLY at
/// `block_height >= deadline_height` (the runtime strengthening of Lean
/// `slash_requires_deadline`) and ONLY if the discharge condition is NOT
/// exhibited in the witness slot (Lean `slash_rejects_when_condition_met`) —
/// a discharged obligation cannot be slashed, and a slashed one cannot be
/// re-resolved (`no_double_resolve_slashed`).
pub fn slash_obligation(obligation: CellId, terms: &ObligationTerms) -> Vec<Effect> {
    resolve_effects(
        obligation,
        None,
        STATE_RESOLVED_B,
        terms.obligee,
        terms.bond,
    )
}

// =============================================================================
// Bridge — Dregg2.Apps.BridgeCell
// =============================================================================

/// Plan a cross-domain bridge lock — the replacement for
/// `Effect::BridgeLock`. (`Effect::BridgeMint` SURVIVES as a shield verb and
/// is NOT replaced by this module.)
///
/// **Safety contract** (Lean twin `Dregg2.Apps.BridgeCell`): the locked
/// amount is held in the bridge cell's own balance; the only admitted
/// resolutions are LOCKED→FINALIZED (finality witness exhibited, value to the
/// published pot — Lean `finalize_requires_finality_witness`) and
/// LOCKED→CANCELLED (value back to the originator; gated on the published
/// timeout when nonzero — value can never be trapped, Lean
/// `locked_cancellable`); a resolved lock is inert (`no_double_finalize`,
/// `no_refinalize_after_cancel`). Fails closed on a zero `finality_witness`.
///
/// `funder` is the cell the locked value is drawn from (the originator's).
pub fn bridge_lock_cell(
    terms: &BridgeTerms,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<SettlementCellPlan, BlueprintError> {
    Ok(settlement_plan(
        bridge_factory_descriptor(terms)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        terms.amount,
        terms.originator,
        terms.pot,
        terms.finality_witness,
        terms.timeout_height,
    ))
}

/// Build the finalize turn for a locked bridge cell — the replacement for
/// `Effect::BridgeFinalize`.
///
/// **Safety contract**: exhibits `finality_witness` and steps
/// LOCKED→FINALIZED; the cell program commits it ONLY if the witness equals
/// the published finality witness (Lean `finalize_requires_finality_witness`)
/// and the lock is still open (`no_double_finalize`,
/// `no_refinalize_after_cancel`). The value moves to the published pot.
pub fn finalize_bridge(
    bridge: CellId,
    terms: &BridgeTerms,
    finality_witness: FieldElement,
) -> Vec<Effect> {
    resolve_effects(
        bridge,
        Some(finality_witness),
        STATE_RESOLVED_A,
        terms.pot,
        terms.amount,
    )
}

/// Build the cancel turn for a locked bridge cell — the replacement for
/// `Effect::BridgeCancel`.
///
/// **Safety contract**: steps LOCKED→CANCELLED and returns the locked value
/// to the published originator. With a nonzero published `timeout_height` the
/// cell program admits this only at `block_height >= timeout_height`
/// (the verb-era recovery semantics); with a zero timeout, any time while
/// locked (Lean `locked_cancellable`). A cancelled lock cannot be finalized
/// (`no_refinalize_after_cancel`).
pub fn cancel_bridge(bridge: CellId, terms: &BridgeTerms) -> Vec<Effect> {
    resolve_effects(
        bridge,
        None,
        STATE_RESOLVED_B,
        terms.originator,
        terms.amount,
    )
}

// =============================================================================
// Supply — the cap-gated mint entry (`docs/SUPPLY-MODEL.md`)
// =============================================================================

/// Plan a cap-gated **mint** of supply into a holder — the one authored entry
/// for new supply (`docs/SUPPLY-MODEL.md`; the sign-flipped dual of `Burn`).
///
/// The minted asset is `recipient`'s own asset class (its `token_id`); the
/// asset's deterministic per-asset **issuer well** is debited negative-capably
/// (going more negative as supply enters) and `recipient` is credited, so the
/// turn conserves exactly (per-turn, per-asset `Σδ=0`) and restores the
/// standing `Σholders + well = 0` invariant.
///
/// **Safety contract** (enforced by the EXECUTOR, not this builder): the turn
/// commits ONLY if the turn agent holds a control-grade **mint-cap** over the
/// issuer well — a full (`AuthRequired::None`) capability carrying the
/// `EFFECT_MINT` facet, the Rust image of Lean `mintAuthorizedB`. A turn with
/// no such cap, a wrong-facet cap, or a self-mint (`agent == recipient`) is
/// REJECTED (`TurnError::CapabilityNotHeld` / `InvalidEffect`). "A cell cannot
/// coin its own supply" — mint authority is a cap over the issuer, not bare
/// ownership.
pub fn mint_supply(recipient: CellId, amount: u64) -> Vec<Effect> {
    vec![Effect::Mint {
        target: recipient,
        slot: 0,
        amount,
    }]
}
