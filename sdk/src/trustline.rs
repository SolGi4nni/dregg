//! # Trustline — the bilateral line of credit as an SDK noun
//! (docs/ORGANS.md §1, docs/TRUSTLINES.md; Lean twin
//! `metatheory/Dregg2/Apps/Trustline.lean`).
//!
//! "Issuer A extends holder B a line of N" is an ATTENUATED CAPABILITY whose
//! exercise debits a shared counter — the granted ⊆ held relation made
//! QUANTITATIVE (`holder_credit_le_line_forever`). This module is the
//! embedded-runtime face of that primitive, riding the owner runtime's
//! normal `.turn()` path exactly like [`crate::factories`] settlement deals
//! (no new executor entry):
//!
//! * **The cell** is born from the per-line content-addressed
//!   [`trustline_factory_descriptor`] (`dregg_cell::blueprint`), whose
//!   installed program the executor re-evaluates on EVERY turn touching the
//!   cell: `drawn ≤ ceiling` for life (`trustline_within_line_forever`),
//!   terms pinned (`ceiling_immutable_forever`), settlement monotone and
//!   never beyond drawn.
//! * **The escrow** (fullReserve backing): [`Trustline::open`] moves the
//!   full line `N` from the issuer's cell into the trustline cell's own
//!   balance — an ordinary conserving `Transfer`, never a mint. Combined
//!   with the `drawn ≤ ceiling` tooth, every settlement payout is solvent
//!   by construction.
//! * **The capability**: at open, the cell grants the HOLDER (and the
//!   operator) a c-list capability over itself — the line IS the
//!   capability; adoption is attenuation.
//! * **Draw / repay** move the shared `drawn` counter (the Stingray
//!   `BudgetSlice` face — `draw_slice_tracks_tryDebit`): draws are
//!   digest-identified and one-shot (`no_double_draw_forever`); repayment
//!   restores the line but never resurrects a digest
//!   (`draw_repay_roundtrip`, `repay_draws_fixed`).
//! * **Settle** redeems the outstanding drawn amount as an ordinary
//!   `Transfer` from the escrow to the holder (the `(agent, total_spent)`
//!   settlement-list shape of `rebalance_budgets`, applied as a move —
//!   `settlePay_conserves_hard`).
//!
//! The NODE-side twin (`node/src/trustline_service.rs`) drives the same
//! cell shape against the live ledger AND welds the Stingray
//! `StingrayCounter` coordinator to it (`init_budget_coordinator` at birth,
//! `collect_spending_certificates`/`rebalance_budgets` at settle). The SDK
//! face has no coordinator: the executor-installed cell program is the
//! enforcement tooth, and the per-digest anti-replay registry is carried by
//! the [`Trustline`] handle (a divergence from the Lean model's
//! forever-registry only across handle loss; the node face closes it with a
//! service-held registry).

use std::collections::BTreeSet;

use dregg_cell::blueprint::{
    STATE_OPEN, TL_CEILING_SLOT, TL_COLLATERAL_SLOT, TL_DIGEST_SLOT, TL_DRAWN_SLOT, TL_HOLDER_SLOT,
    TL_ISSUER_SLOT, TL_SETTLED_SLOT, TL_STATE_CLOSED, TL_STATE_SLOT, TrustlineCollateral,
    TrustlineTerms, trustline_factory_descriptor_collateral,
};
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::program::field_from_u64;
use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CellId, CellMode};
use dregg_turn::Effect;
use dregg_turn::action::{Event, symbol};
use dregg_turn::turn::TurnReceipt;

use crate::error::SdkError;
use crate::factories::ADOPT_TURN_FEE;
use crate::runtime::AgentRuntime;

/// Decode a slot's trailing big-endian u64 (the cell-program encoding).
fn field_to_u64(f: FieldElement) -> u64 {
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

/// The fixed computron fee a pureCredit settle's holder-side hard-move turn
/// pays (a cell-agent turn — `execute_as` takes an explicit fee; this is the
/// same order as the channel-exercise turns).
pub const PURE_CREDIT_SETTLE_FEE: u64 = 10_000;

/// A planned trustline: the published per-line factory + the four turns that
/// birth, fund (escrow the full line), adopt (grant operator + holder their
/// capabilities), and open it — the [`crate::factories`] settlement-plan
/// lifecycle on the trustline slot schema.
#[derive(Clone, Debug)]
pub struct TrustlinePlan {
    /// The per-line, content-addressed factory descriptor. Deploy BEFORE
    /// executing [`Self::create_effects`].
    pub descriptor: FactoryDescriptor,
    /// `descriptor.factory_vk`, for convenience.
    pub factory_vk: [u8; 32],
    /// The deterministic id of the trustline cell.
    pub cell_id: CellId,
    /// Turn 1 (issuer agent turn): birth the cell from the factory.
    pub create_effects: Vec<Effect>,
    /// Turn 2 (issuer agent turn): escrow `line + ADOPT_TURN_FEE` into the
    /// trustline cell — THE FUNDED BIRTH (the funder's real ledger debit;
    /// exactly `line` remains escrowed after the adopt turn burns its fee).
    pub fund_effects: Vec<Effect>,
    /// Turn 3 (cell-agent turn, fee [`ADOPT_TURN_FEE`]): the cell grants the
    /// operator driving reach AND the holder their line capability — "I
    /// extend you a line of N" as a granted, attenuatable capability.
    pub adopt_effects: Vec<Effect>,
    /// Turn 4 (operator turn): write the terms and step UNINIT → OPEN. The
    /// program pins every term to the descriptor's literals from here on.
    pub open_effects: Vec<Effect>,
}

/// Plan a new directional trustline `issuer → holder` of `line` at the
/// fullReserve collateral point (the deployed default — see
/// [`plan_trustline_collateral`] for the axis).
///
/// `owner_pubkey` is the key the executor verifies cell-targeted turns
/// against (the issuer/operator's key in the embedded setting); `token_id`
/// disambiguates multiple lines between the same parties.
pub fn plan_trustline(
    line: u64,
    issuer: CellId,
    holder: CellId,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
) -> Result<TrustlinePlan, dregg_cell::blueprint::BlueprintError> {
    plan_trustline_collateral(
        line,
        issuer,
        holder,
        owner_pubkey,
        token_id,
        operator,
        TrustlineCollateral::FullReserve,
    )
}

/// [`plan_trustline`] at a point of the collateral axis (Lean §12
/// `Collateral`). The fullReserve plan is the historical plan exactly; the
/// pureCredit plan escrows NOTHING (the fund turn carries only the adopt
/// fee) and the open turn pins the mode into slot 7 — the per-line program
/// (and so the cell's VK) content-addresses the collateral point.
#[allow(clippy::too_many_arguments)]
pub fn plan_trustline_collateral(
    line: u64,
    issuer: CellId,
    holder: CellId,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    collateral: TrustlineCollateral,
) -> Result<TrustlinePlan, dregg_cell::blueprint::BlueprintError> {
    let terms = TrustlineTerms {
        line,
        issuer: *issuer.as_bytes(),
        holder: *holder.as_bytes(),
    };
    let descriptor = trustline_factory_descriptor_collateral(&terms, collateral)?;
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
    // The funded birth: fullReserve escrows the FULL line (+ the adopt fee
    // the adopt turn burns); pureCredit escrows nothing — the line is the
    // issuer's consented risk, so only the adopt fee moves.
    let escrowed = match collateral {
        TrustlineCollateral::FullReserve => line,
        TrustlineCollateral::PureCredit => 0,
    };
    let fund_effects = vec![Effect::Transfer {
        from: issuer,
        to: cell_id,
        amount: escrowed + ADOPT_TURN_FEE,
    }];
    let self_cap = |to: CellId| Effect::GrantCapability {
        from: cell_id,
        to,
        cap: CapabilityRef {
            target: cell_id,
            slot: 0, // assigned by the recipient c-list at install
            permissions: dregg_cell::AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };
    let adopt_effects = vec![self_cap(operator), self_cap(holder)];
    let set = |index: u8, value: FieldElement| Effect::SetField {
        cell: cell_id,
        index: index as usize,
        value,
    };
    let mut open_effects = vec![
        set(TL_CEILING_SLOT, field_from_u64(line)),
        set(TL_ISSUER_SLOT, *issuer.as_bytes()),
        set(TL_HOLDER_SLOT, *holder.as_bytes()),
    ];
    if collateral == TrustlineCollateral::PureCredit {
        // The mode pin: the pureCredit program refuses an open that does not
        // write its slot-7 literal (and pins it for life thereafter).
        open_effects.push(set(
            TL_COLLATERAL_SLOT,
            field_from_u64(collateral.slot_code()),
        ));
    }
    open_effects.push(set(TL_STATE_SLOT, field_from_u64(STATE_OPEN)));
    open_effects.push(Effect::EmitEvent {
        cell: cell_id,
        event: Event::new(
            symbol("trustline-opened"),
            vec![field_from_u64(line), *issuer.as_bytes(), *holder.as_bytes()],
        ),
    });
    Ok(TrustlinePlan {
        descriptor,
        factory_vk,
        cell_id,
        create_effects,
        fund_effects,
        adopt_effects,
        open_effects,
    })
}

/// A live trustline position, read from the cell's registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustlineStatus {
    /// The extended line N (`ceiling`).
    pub line: u64,
    /// Net drawn against the line (up on draw, down on repay).
    pub drawn: u64,
    /// Cumulative drawn value already redeemed to the holder by settlement.
    pub settled: u64,
    /// Remaining undrawn line: `line - drawn`.
    pub remaining: u64,
    /// The cell's escrowed hard balance backing the line.
    pub escrow: u64,
    /// Whether the line is OPEN (terms written, live).
    pub open: bool,
}

/// An open trustline handle: issuer-side driving surface over the owner
/// runtime's `.turn()` path. The handle carries the draw-digest anti-replay
/// registry (the `BudgetSlice::debits` face).
#[derive(Debug)]
pub struct Trustline {
    /// The trustline cell.
    pub cell: CellId,
    /// The extended line N.
    pub line: u64,
    /// Issuer (the funder whose escrow backs the line).
    pub issuer: CellId,
    /// Holder (the counterparty exercising the line).
    pub holder: CellId,
    /// The collateral point of this line (Lean §12 `Collateral`).
    pub collateral: TrustlineCollateral,
    /// Committed draw digests — one-shot forever (`no_double_draw_forever`).
    digests: BTreeSet<[u8; 32]>,
}

impl Trustline {
    /// **Open a line** at the fullReserve point: issuer (this runtime's
    /// agent) extends `holder` a line of `line`, escrowing the full amount
    /// from the issuer's own cell (the funded birth — the funder is REALLY
    /// debited). Runs the four-turn factory lifecycle (create → fund →
    /// adopt → open) through the normal `.turn()` path; the executor
    /// installs the per-line program at birth.
    pub fn open(
        runtime: &mut AgentRuntime,
        holder: CellId,
        line: u64,
        token_id: [u8; 32],
    ) -> Result<Self, SdkError> {
        Self::open_with_collateral(
            runtime,
            holder,
            line,
            token_id,
            TrustlineCollateral::FullReserve,
        )
    }

    /// [`Self::open`] at a chosen point of the collateral axis. The
    /// pureCredit point escrows NOTHING (no hard backing — the issuer's
    /// consented risk): draws and repays move only the credit registers, the
    /// bilateral ±drawn pair is DERIVED (Lean §11), and settlement is the
    /// holder repaying the issuer hard value (`settleC .pureCredit` —
    /// `settleC_pureCredit_agrees_settlePay`).
    pub fn open_with_collateral(
        runtime: &mut AgentRuntime,
        holder: CellId,
        line: u64,
        token_id: [u8; 32],
        collateral: TrustlineCollateral,
    ) -> Result<Self, SdkError> {
        let issuer = runtime.cell_id();
        let owner_pubkey = runtime
            .cipherclerk()
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key()
            .0;
        let plan = plan_trustline_collateral(
            line,
            issuer,
            holder,
            owner_pubkey,
            token_id,
            issuer,
            collateral,
        )
        .map_err(|e| SdkError::Rejected(format!("trustline terms refused: {e}")))?;
        runtime.deploy_factory(plan.descriptor.clone());
        runtime.execute(plan.create_effects.clone())?;
        runtime.execute(plan.fund_effects.clone())?;
        runtime.execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)?;
        runtime.execute_on(plan.cell_id, plan.open_effects.clone())?;
        Ok(Trustline {
            cell: plan.cell_id,
            line,
            issuer,
            holder,
            collateral,
            digests: BTreeSet::new(),
        })
    }

    /// Read the live position from the cell's registers.
    pub fn status(&self, runtime: &AgentRuntime) -> Result<TrustlineStatus, SdkError> {
        let ledger = runtime.ledger().lock().unwrap();
        let cell = ledger
            .get(&self.cell)
            .ok_or_else(|| SdkError::Rejected("trustline cell not in ledger".into()))?;
        let line = field_to_u64(cell.state.fields[TL_CEILING_SLOT as usize]);
        let drawn = field_to_u64(cell.state.fields[TL_DRAWN_SLOT as usize]);
        let settled = field_to_u64(cell.state.fields[TL_SETTLED_SLOT as usize]);
        let state = field_to_u64(cell.state.fields[TL_STATE_SLOT as usize]);
        Ok(TrustlineStatus {
            line,
            drawn,
            settled,
            remaining: line.saturating_sub(drawn),
            escrow: u64::try_from(cell.state.balance()).unwrap_or(0),
            open: state == STATE_OPEN,
        })
    }

    /// **Draw against the line** (the holder exercises their capability):
    /// `drawn += amount`, digest-identified. Fail-closed twice over, exactly
    /// the Lean `draw` gate: a replayed digest is refused
    /// (`draw_replay_refused`) and an over-line draw is refused by the
    /// EXECUTOR's installed program (`over_line_draw_refused` — the
    /// `drawn ≤ ceiling` tooth bites in-protocol, with this method's mirror
    /// check only shaping the error).
    pub fn draw(
        &mut self,
        runtime: &AgentRuntime,
        digest: [u8; 32],
        amount: u64,
    ) -> Result<TurnReceipt, SdkError> {
        if self.digests.contains(&digest) {
            return Err(SdkError::Rejected(
                "trustline draw digest replayed (no-double-draw)".into(),
            ));
        }
        let status = self.status(runtime)?;
        if !status.open {
            return Err(SdkError::Rejected("trustline is not open".into()));
        }
        if amount > status.remaining {
            return Err(SdkError::Rejected(format!(
                "draw {amount} exceeds remaining line {}",
                status.remaining
            )));
        }
        let new_drawn = status.drawn + amount;
        let receipt = runtime.execute_on(
            self.cell,
            vec![
                Effect::SetField {
                    cell: self.cell,
                    index: TL_DRAWN_SLOT as usize,
                    value: field_from_u64(new_drawn),
                },
                Effect::SetField {
                    cell: self.cell,
                    index: TL_DIGEST_SLOT as usize,
                    value: digest,
                },
                Effect::EmitEvent {
                    cell: self.cell,
                    event: Event::new(
                        symbol("trustline-draw"),
                        vec![digest, field_from_u64(amount), field_from_u64(new_drawn)],
                    ),
                },
            ],
        )?;
        // Burned only on COMMIT: a rejected draw leaves the digest fresh.
        self.digests.insert(digest);
        Ok(receipt)
    }

    /// **Repay**: `drawn -= amount`, restoring the line
    /// (`draw_repay_roundtrip`). Over-repayment — beyond the outstanding
    /// UNSETTLED draw — is refused (`over_repay_refused`; settled credit is
    /// hard money in the holder's hands and cannot be repaid back: the
    /// program's `settled ≤ drawn` tooth). Spent digests stay burned.
    pub fn repay(&self, runtime: &AgentRuntime, amount: u64) -> Result<TurnReceipt, SdkError> {
        let status = self.status(runtime)?;
        let outstanding = status.drawn.saturating_sub(status.settled);
        if amount > outstanding {
            return Err(SdkError::Rejected(format!(
                "repay {amount} exceeds outstanding unsettled draw {outstanding}"
            )));
        }
        runtime.execute_on(
            self.cell,
            vec![
                Effect::SetField {
                    cell: self.cell,
                    index: TL_DRAWN_SLOT as usize,
                    value: field_from_u64(status.drawn - amount),
                },
                Effect::EmitEvent {
                    cell: self.cell,
                    event: Event::new(
                        symbol("trustline-repay"),
                        vec![
                            field_from_u64(amount),
                            field_from_u64(status.drawn - amount),
                        ],
                    ),
                },
            ],
        )
    }

    /// **Settle**: redeem the outstanding drawn amount (`drawn - settled`)
    /// at this line's collateral point — `settleC` (Lean §12), made a turn:
    ///
    /// * **fullReserve**: an ordinary `Transfer` from the escrow to the
    ///   holder, marking it settled (`settled := drawn`) — the
    ///   `(agent, total_spent)` settlement-list shape applied as a move
    ///   (`settleC_fullReserve_spec` / `settlePay_conserves_hard`); the
    ///   program's `settled ≤ drawn ≤ ceiling` teeth make the payout solvent.
    /// * **pureCredit**: the holder repays the issuer hard value while the
    ///   credit legs unwind (`drawn := settled`, the floored repay) — exactly
    ///   `settleC .pureCredit`, which IS §5b's `settlePay`
    ///   (`settleC_pureCredit_agrees_settlePay`); the escrow column (zero)
    ///   is never touched. This point is a BILATERAL pair of turns: the hard
    ///   move is a turn the HOLDER's cell authorizes (cell-agent turn —
    ///   `from == action_target`, so no cross-cell Send escalation; the
    ///   embedded runtime can sign it when the holder cell is owner-keyed,
    ///   the single-machine collapse), then the operator unwinds the credit
    ///   registers on the line. HONEST RESIDUE: the pair is sequenced, not
    ///   atomic (the one-turn shape needs a cross-cell Send/SetState grant or
    ///   a joint turn); the hard move commits FIRST, so a failure between
    ///   the legs leaves the holder paid and the unwind retryable —
    ///   re-calling `settle` never double-charges (it re-reads the cell).
    ///
    /// Both points conserve the hard column exactly
    /// (`settleC_conserves_hard`). Returns the amount moved (0 = nothing
    /// outstanding, no turn submitted).
    pub fn settle(&self, runtime: &AgentRuntime) -> Result<u64, SdkError> {
        let status = self.status(runtime)?;
        let outstanding = status.drawn.saturating_sub(status.settled);
        if outstanding == 0 {
            return Ok(0);
        }
        match self.collateral {
            TrustlineCollateral::FullReserve => {
                runtime.execute_on(
                    self.cell,
                    vec![
                        Effect::SetField {
                            cell: self.cell,
                            index: TL_SETTLED_SLOT as usize,
                            value: field_from_u64(status.drawn),
                        },
                        Effect::Transfer {
                            from: self.cell,
                            to: self.holder,
                            amount: outstanding,
                        },
                        Effect::EmitEvent {
                            cell: self.cell,
                            event: Event::new(
                                symbol("trustline-settle"),
                                vec![field_from_u64(outstanding), field_from_u64(status.drawn)],
                            ),
                        },
                    ],
                )?;
            }
            TrustlineCollateral::PureCredit => {
                // Leg 1 — the hard move, holder → issuer, authorized by the
                // holder's own cell (`settleC .pureCredit`'s value leg).
                runtime.execute_as(
                    self.holder,
                    vec![Effect::Transfer {
                        from: self.holder,
                        to: self.issuer,
                        amount: outstanding,
                    }],
                    PURE_CREDIT_SETTLE_FEE,
                )?;
                // Leg 2 — the floored repay: drawn := settled (credit legs
                // unwind; spent digests stay burned — `repayS`).
                runtime.execute_on(
                    self.cell,
                    vec![
                        Effect::SetField {
                            cell: self.cell,
                            index: TL_DRAWN_SLOT as usize,
                            value: field_from_u64(status.settled),
                        },
                        Effect::EmitEvent {
                            cell: self.cell,
                            event: Event::new(
                                symbol("trustline-settle"),
                                vec![field_from_u64(outstanding), field_from_u64(status.settled)],
                            ),
                        },
                    ],
                )?;
            }
        }
        Ok(outstanding)
    }

    /// **Close the line** (the lifecycle's terminal step, `OPEN → CLOSED`):
    /// settle-then-return-residual, ONE turn.
    ///
    /// * **fullReserve**: any outstanding draw is settled to the holder
    ///   (`settled := drawn` + escrow→holder), the RESIDUAL escrow
    ///   (`escrow − outstanding`) returns to the issuer, and the state slot
    ///   steps to [`TL_STATE_CLOSED`]. Total hard value is exactly conserved
    ///   (two moves, no mint), and the closed cell is INERT — the program's
    ///   transition table has no row out of CLOSED, so EVERY later touch
    ///   (draw, repay, even a transfer in) refuses.
    /// * **pureCredit**: there is no escrow to return; closing requires the
    ///   outstanding draw to be zero (settle/repay first — the issuer cannot
    ///   unilaterally debit the holder as a side effect of closing).
    ///
    /// Returns `(settled_to_holder, residual_to_issuer)`.
    pub fn close(&self, runtime: &AgentRuntime) -> Result<(u64, u64), SdkError> {
        let status = self.status(runtime)?;
        if !status.open {
            return Err(SdkError::Rejected("trustline is not open".into()));
        }
        let outstanding = status.drawn.saturating_sub(status.settled);
        let mut effects = Vec::new();
        let residual = match self.collateral {
            TrustlineCollateral::FullReserve => {
                if outstanding > 0 {
                    effects.push(Effect::SetField {
                        cell: self.cell,
                        index: TL_SETTLED_SLOT as usize,
                        value: field_from_u64(status.drawn),
                    });
                    effects.push(Effect::Transfer {
                        from: self.cell,
                        to: self.holder,
                        amount: outstanding,
                    });
                }
                let residual = status.escrow.saturating_sub(outstanding);
                if residual > 0 {
                    effects.push(Effect::Transfer {
                        from: self.cell,
                        to: self.issuer,
                        amount: residual,
                    });
                }
                residual
            }
            TrustlineCollateral::PureCredit => {
                if outstanding > 0 {
                    return Err(SdkError::Rejected(format!(
                        "pureCredit close refused: {outstanding} outstanding — settle or \
                         repay first (closing cannot debit the holder)"
                    )));
                }
                0
            }
        };
        effects.push(Effect::SetField {
            cell: self.cell,
            index: TL_STATE_SLOT as usize,
            value: field_from_u64(TL_STATE_CLOSED),
        });
        effects.push(Effect::EmitEvent {
            cell: self.cell,
            event: Event::new(
                symbol("trustline-closed"),
                vec![field_from_u64(outstanding), field_from_u64(residual)],
            ),
        });
        runtime.execute_on(self.cell, effects)?;
        Ok((outstanding, residual))
    }
}

// =============================================================================
// Tests — the embedded e2e: every Lean polarity on the REAL executor
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::AgentCipherclerk;

    const LINE: u64 = 100;
    const FUNDING: u64 = 1_000_000;

    fn digest(n: u64) -> [u8; 32] {
        *blake3::Hasher::new_derive_key("trustline-test-digest-v1")
            .update(&n.to_le_bytes())
            .finalize()
            .as_bytes()
    }

    /// A funded issuer runtime + a holder cell on the same ledger.
    fn setup() -> (AgentRuntime, CellId) {
        let cclerk = AgentCipherclerk::new();
        let issuer_pk = cclerk.public_key().0;
        let runtime = AgentRuntime::new_simple(cclerk, "trustline-test");
        let holder_pk = blake3::derive_key("trustline-test-holder-v1", b"holder");
        let holder_cell = dregg_cell::Cell::with_balance(holder_pk, [0u8; 32], 500);
        let holder = holder_cell.id();
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger.insert_cell(holder_cell).unwrap();
            // Fund the issuer agent cell: the escrow + every turn fee comes
            // from here (the funder is REALLY debited). Materialize it the
            // way genesis does if the runtime has not already.
            let issuer = runtime.cell_id();
            if ledger.get(&issuer).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let cell = dregg_cell::Cell::with_balance(issuer_pk, token, 0);
                assert_eq!(cell.id(), issuer, "derivation must match runtime");
                ledger.insert_cell(cell).unwrap();
            }
            assert!(
                ledger
                    .get_mut(&issuer)
                    .unwrap()
                    .state
                    .credit_balance(FUNDING),
                "issuer accepts funding"
            );
        }
        (runtime, holder)
    }

    fn balance(runtime: &AgentRuntime, cell: CellId) -> i128 {
        runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&cell)
            .map(|c| c.state.balance() as i128)
            .unwrap_or(0)
    }

    // ── open: the funded birth ───────────────────────────────────────────────

    #[test]
    fn open_escrows_the_line_and_grants_the_holder_capability() {
        let (mut runtime, holder) = setup();
        let issuer_before = balance(&runtime, runtime.cell_id());

        let tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        // The escrow holds EXACTLY the line (fund moved line + ADOPT_TURN_FEE;
        // the adopt turn burned its fee).
        assert_eq!(balance(&runtime, tl.cell), LINE as i128);
        // THE FUNDER IS DEBITED: at least the escrowed line left the issuer.
        let issuer_after = balance(&runtime, runtime.cell_id());
        assert!(
            issuer_before - issuer_after >= (LINE + ADOPT_TURN_FEE) as i128,
            "issuer must be debited the escrow + adopt fee (was {} → {})",
            issuer_before,
            issuer_after
        );
        // The holder holds the line AS A CAPABILITY over the trustline cell.
        {
            let ledger = runtime.ledger().lock().unwrap();
            assert!(
                ledger
                    .get(&holder)
                    .unwrap()
                    .capabilities
                    .has_access(&tl.cell),
                "holder must hold the line capability"
            );
        }
        let status = tl.status(&runtime).unwrap();
        assert!(status.open);
        assert_eq!(status.line, LINE);
        assert_eq!(status.drawn, 0);
        assert_eq!(status.remaining, LINE);
    }

    // ── draw: within line / over line / boundary ─────────────────────────────

    #[test]
    fn draw_within_line_succeeds_and_over_line_refuses() {
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        // Within line: admits (Lean positive polarity).
        tl.draw(&runtime, digest(1), 30).expect("draw 30");
        let s = tl.status(&runtime).unwrap();
        assert_eq!(s.drawn, 30);
        assert_eq!(s.remaining, 70);

        // Over line: refused, counter unmoved (over_line_draw_refused).
        let err = tl.draw(&runtime, digest(2), 80).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)), "{err:?}");
        assert_eq!(tl.status(&runtime).unwrap().drawn, 30);

        // The boundary draw (exactly the remaining 70) admits — tight bound.
        tl.draw(&runtime, digest(2), 70).expect("boundary draw");
        assert_eq!(tl.status(&runtime).unwrap().remaining, 0);
    }

    #[test]
    fn executor_program_rejects_over_line_draw_directly() {
        // THE EXECUTOR TOOTH, bypassing the SDK mirror: a raw turn writing
        // drawn = ceiling + 1 violates the installed program and is rejected
        // by the executor; the register is unmoved.
        let (mut runtime, holder) = setup();
        let tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        let res = runtime.execute_on(
            tl.cell,
            vec![Effect::SetField {
                cell: tl.cell,
                index: TL_DRAWN_SLOT as usize,
                value: field_from_u64(LINE + 1),
            }],
        );
        assert!(matches!(res, Err(SdkError::Turn(_))), "{res:?}");
        assert_eq!(tl.status(&runtime).unwrap().drawn, 0, "counter unmoved");

        // The ceiling itself is immutable (ceiling_immutable_forever).
        let res = runtime.execute_on(
            tl.cell,
            vec![Effect::SetField {
                cell: tl.cell,
                index: TL_CEILING_SLOT as usize,
                value: field_from_u64(LINE * 10),
            }],
        );
        assert!(matches!(res, Err(SdkError::Turn(_))), "{res:?}");
        assert_eq!(tl.status(&runtime).unwrap().line, LINE);
    }

    // ── no double draw ───────────────────────────────────────────────────────

    #[test]
    fn double_draw_of_same_digest_refuses() {
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        tl.draw(&runtime, digest(7), 30).expect("first draw");
        let err = tl.draw(&runtime, digest(7), 1).unwrap_err();
        assert!(
            matches!(&err, SdkError::Rejected(m) if m.contains("replayed")),
            "{err:?}"
        );
        assert_eq!(tl.status(&runtime).unwrap().drawn, 30, "counter unmoved");
    }

    // ── repay then redraw ────────────────────────────────────────────────────

    #[test]
    fn repay_restores_the_line_and_redraw_succeeds() {
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        tl.draw(&runtime, digest(1), 30).expect("draw");
        tl.repay(&runtime, 30).expect("repay");
        let s = tl.status(&runtime).unwrap();
        assert_eq!(s.drawn, 0, "draw_repay_roundtrip: counter restored");
        assert_eq!(s.remaining, LINE);

        // The spent digest stays burned (repay_draws_fixed)…
        let err = tl.draw(&runtime, digest(1), 10).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)));
        // …but a fresh digest draws fine on the restored line.
        tl.draw(&runtime, digest(2), LINE)
            .expect("redraw full line");

        // Over-repay is refused (over_repay_refused).
        let tl2 = &tl;
        let err = tl2.repay(&runtime, LINE + 1).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)));
    }

    // ── settle: ledger moves match net positions, total conserved ────────────

    #[test]
    fn settle_moves_net_position_and_conserves() {
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");

        tl.draw(&runtime, digest(1), 30).expect("draw 30");
        tl.repay(&runtime, 10).expect("repay 10");
        // Net position: 20 outstanding.

        let escrow_before = balance(&runtime, tl.cell);
        let holder_before = balance(&runtime, holder);
        let moved = tl.settle(&runtime).expect("settle");
        assert_eq!(moved, 20, "settle moves exactly the net position");

        // The hard pair is exactly conserved (settlePay_conserves_hard).
        let escrow_after = balance(&runtime, tl.cell);
        let holder_after = balance(&runtime, holder);
        assert_eq!(holder_after - holder_before, 20);
        assert_eq!(escrow_before - escrow_after, 20);
        assert_eq!(
            escrow_after + holder_after,
            escrow_before + holder_before,
            "total conserved across the settle move"
        );

        let s = tl.status(&runtime).unwrap();
        assert_eq!(s.settled, 20);
        assert_eq!(s.drawn, 20);
        // Settled credit cannot be repaid back (the settled ≤ drawn tooth).
        let err = tl.repay(&runtime, 1).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)));
        // Nothing further outstanding: settle is a no-op.
        assert_eq!(tl.settle(&runtime).unwrap(), 0);
    }

    #[test]
    fn executor_rejects_unsettling_tamper() {
        // The Monotonic(settled) tooth: un-settling (which would let the
        // escrow pay the same draw twice) is rejected by the executor.
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");
        tl.draw(&runtime, digest(1), 30).expect("draw");
        tl.settle(&runtime).expect("settle");

        let res = runtime.execute_on(
            tl.cell,
            vec![Effect::SetField {
                cell: tl.cell,
                index: TL_SETTLED_SLOT as usize,
                value: field_from_u64(0),
            }],
        );
        assert!(matches!(res, Err(SdkError::Turn(_))), "{res:?}");
        assert_eq!(tl.status(&runtime).unwrap().settled, 30);
    }

    // ── close: settle-then-return-residual, then the line is INERT ──────────

    #[test]
    fn close_settles_then_returns_residual_and_line_goes_inert() {
        let (mut runtime, holder) = setup();
        let mut tl = Trustline::open(&mut runtime, holder, LINE, [7u8; 32]).expect("open");
        tl.draw(&runtime, digest(1), 30).expect("draw 30");
        tl.repay(&runtime, 10).expect("repay 10");
        // Net position: 20 outstanding; escrow holds the full LINE.

        let issuer = runtime.cell_id();
        let escrow_before = balance(&runtime, tl.cell);
        let holder_before = balance(&runtime, holder);
        let issuer_before = balance(&runtime, issuer);
        assert_eq!(escrow_before, LINE as i128);

        let (settled, residual) = tl.close(&runtime).expect("close");
        assert_eq!(settled, 20, "close settles the outstanding draw");
        assert_eq!(residual, LINE - 20, "residual = escrow − outstanding");

        // The escrow fully drains: outstanding → holder, residual → issuer.
        assert_eq!(balance(&runtime, tl.cell), 0, "escrow drained at close");
        assert_eq!(balance(&runtime, holder) - holder_before, 20);
        // The issuer is the operator agent that DRIVES the close, so its net
        // is the residual Transfer it RECEIVES (`LINE − outstanding`) minus the
        // close turn's fee it PAYS (the default `execute_on` budget). The
        // residual-receipt leg is what the trustline semantics promise; the fee
        // is the orthogonal cost of driving the turn.
        const CLOSE_TURN_FEE: i128 = 10_000;
        assert_eq!(
            (balance(&runtime, issuer) - issuer_before) + CLOSE_TURN_FEE,
            (LINE - 20) as i128,
            "residual escrow returns to the issuer (net of the close turn fee it pays)"
        );
        // The hard column is exactly conserved across the close turn (the
        // close turn's fee is paid by the operator agent = issuer; account it
        // via the three-column total + the turn fee being the only leak is
        // checked by the executor's conservation gate — here the moved pair):
        assert_eq!(
            (balance(&runtime, tl.cell) + balance(&runtime, holder))
                - (escrow_before + holder_before),
            -((LINE - 20) as i128),
            "escrow+holder gave up exactly the residual (which the issuer received)"
        );

        let status = tl.status(&runtime).unwrap();
        assert!(!status.open, "TL_STATE_CLOSED");
        // `repay(10)` lowered `drawn` 30 → 20, so the post-repay drawn (and the
        // amount settled to the holder at close) is 20 — settled marches to the
        // LIVE drawn, not the gross pre-repay draw.
        assert_eq!(
            status.settled, 20,
            "settled marched to (post-repay) drawn at close"
        );
        assert_eq!(
            status.drawn, 20,
            "repay lowered drawn to the outstanding 20"
        );

        // INERT: the program has no row out of CLOSED — every later touch
        // refuses, including a draw, a repay, and even a transfer INTO it.
        let err = tl.draw(&runtime, digest(2), 1).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)), "{err:?}");
        let res = runtime.execute_on(
            tl.cell,
            vec![Effect::SetField {
                cell: tl.cell,
                index: TL_DRAWN_SLOT as usize,
                value: field_from_u64(31),
            }],
        );
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "closed line is inert: {res:?}"
        );
        let res = runtime.execute(vec![Effect::Transfer {
            from: issuer,
            to: tl.cell,
            amount: 1,
        }]);
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "no value re-enters a closed line: {res:?}"
        );
        // A second close refuses (not open).
        assert!(matches!(tl.close(&runtime), Err(SdkError::Rejected(_))));
    }

    // ── the pureCredit collateral point (Lean §12) ──────────────────────────

    /// A funded issuer runtime + an OWNER-KEYED holder cell (the runtime can
    /// sign the holder's cell-agent turns — the single-machine collapse the
    /// pureCredit settle's bilateral hard move needs), holder funded to repay.
    fn setup_owned_holder() -> (AgentRuntime, CellId) {
        let cclerk = AgentCipherclerk::new();
        let issuer_pk = cclerk.public_key().0;
        let runtime = AgentRuntime::new_simple(cclerk, "trustline-purecredit-test");
        let holder_cell = dregg_cell::Cell::with_balance(
            issuer_pk,
            *blake3::hash(b"pc-holder").as_bytes(),
            100_000,
        );
        let holder = holder_cell.id();
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger.insert_cell(holder_cell).unwrap();
            let issuer = runtime.cell_id();
            if ledger.get(&issuer).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let cell = dregg_cell::Cell::with_balance(issuer_pk, token, 0);
                assert_eq!(cell.id(), issuer);
                ledger.insert_cell(cell).unwrap();
            }
            assert!(
                ledger
                    .get_mut(&issuer)
                    .unwrap()
                    .state
                    .credit_balance(FUNDING)
            );
        }
        (runtime, holder)
    }

    #[test]
    fn pure_credit_open_escrows_nothing_and_draws_move_no_hard_value() {
        let (mut runtime, holder) = setup_owned_holder();
        let issuer = runtime.cell_id();
        let issuer_before = balance(&runtime, issuer);
        let holder_before = balance(&runtime, holder);

        let mut tl = Trustline::open_with_collateral(
            &mut runtime,
            holder,
            LINE,
            [9u8; 32],
            TrustlineCollateral::PureCredit,
        )
        .expect("pureCredit open");

        // NOTHING escrowed: no hard backing (the issuer's consented risk).
        assert_eq!(
            balance(&runtime, tl.cell),
            0,
            "pureCredit escrow column is zero"
        );
        // The issuer paid only fees (adopt fee + per-turn fees), never the
        // line. The two collateral points share the EXACT same four-turn fee
        // schedule — the only hard-value difference is whether the line is
        // escrowed at the fund turn — so a fullReserve open of the same line
        // costs the issuer exactly `LINE` MORE. Differencing the two flows
        // proves the pureCredit line itself was never escrowed.
        let pure_credit_spent = issuer_before - balance(&runtime, issuer);
        let (mut fr_runtime, fr_holder) = setup_owned_holder();
        let fr_issuer = fr_runtime.cell_id();
        let fr_before = balance(&fr_runtime, fr_issuer);
        Trustline::open_with_collateral(
            &mut fr_runtime,
            fr_holder,
            LINE,
            [9u8; 32],
            TrustlineCollateral::FullReserve,
        )
        .expect("fullReserve open");
        let full_reserve_spent = fr_before - balance(&fr_runtime, fr_issuer);
        assert_eq!(
            full_reserve_spent - pure_credit_spent,
            LINE as i128,
            "the line itself was never escrowed: pureCredit spends exactly \
             LINE less than fullReserve (pure={pure_credit_spent}, \
             full={full_reserve_spent})"
        );

        // Draws move ONLY the credit registers (Lean §12b stepC): no hard
        // value moves at draw — the ±drawn pair is DERIVED (§11).
        tl.draw(&runtime, digest(1), 30).expect("draw 30");
        let s = tl.status(&runtime).unwrap();
        assert_eq!(s.drawn, 30);
        assert_eq!(s.escrow, 0, "draw moved no hard value into/out of the cell");
        assert_eq!(
            balance(&runtime, holder),
            holder_before,
            "holder hard column unmoved"
        );

        // The line bound bites identically at this point of the axis.
        let err = tl.draw(&runtime, digest(2), LINE).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)), "{err:?}");
        // And the mode is PINNED: flipping slot 7 back is refused in-protocol.
        let res = runtime.execute_on(
            tl.cell,
            vec![Effect::SetField {
                cell: tl.cell,
                index: TL_COLLATERAL_SLOT as usize,
                value: field_from_u64(0),
            }],
        );
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "mode immutable: {res:?}"
        );
    }

    #[test]
    fn pure_credit_settle_agrees_settle_pay_and_conserves() {
        // The `settleC_pureCredit_agrees_settlePay` shape: a committed
        // pure-credit settle (i) never touches the escrow column, (ii) moves
        // exactly the outstanding amount holder → issuer, and (iii) unwinds
        // the credit legs (`drawn := settled`, the floored repay) with spent
        // digests staying burned.
        let (mut runtime, holder) = setup_owned_holder();
        let issuer = runtime.cell_id();
        let mut tl = Trustline::open_with_collateral(
            &mut runtime,
            holder,
            LINE,
            [9u8; 32],
            TrustlineCollateral::PureCredit,
        )
        .expect("pureCredit open");

        tl.draw(&runtime, digest(1), 30).expect("draw 30");
        tl.repay(&runtime, 10).expect("repay 10");
        // Net position: 20 outstanding.

        let issuer_before = balance(&runtime, issuer);
        let holder_before = balance(&runtime, holder);
        let moved = tl.settle(&runtime).expect("settle");
        assert_eq!(moved, 20, "settle moves exactly the net position");

        // (i) escrow untouched (it is the zero column at this point).
        assert_eq!(balance(&runtime, tl.cell), 0);
        // (ii) the hard move: the holder paid exactly outstanding + the
        // fixed hard-move turn fee; the issuer RECEIVED the outstanding
        // (its other delta is leg 2's operator turn fee, paid by the same
        // cell — value was moved, never made: settleC_conserves_hard).
        assert_eq!(
            holder_before - balance(&runtime, holder),
            (20 + PURE_CREDIT_SETTLE_FEE) as i128,
            "holder pays the outstanding + the hard-move turn fee"
        );
        assert!(
            balance(&runtime, issuer) - issuer_before <= 20,
            "the issuer never gains more than the moved outstanding (no mint)"
        );
        // (iii) the credit legs unwound: drawn := settled (= 0 here).
        let s = tl.status(&runtime).unwrap();
        assert_eq!(s.drawn, 0, "repayS: the floored unwind");
        assert_eq!(s.settled, 0, "pureCredit settle never marches `settled`");
        assert_eq!(s.remaining, LINE, "the line is restored");
        // Spent digests stay burned across the settle.
        let err = tl.draw(&runtime, digest(1), 5).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)));
        // …but fresh credit flows again.
        tl.draw(&runtime, digest(3), 5)
            .expect("fresh post-settle draw");
        // Nothing further outstanding after a clean settle → no-op.
        tl.repay(&runtime, 5).expect("repay back to clean");
        assert_eq!(tl.settle(&runtime).unwrap(), 0);
    }

    #[test]
    fn pure_credit_close_requires_clean_position_then_goes_inert() {
        let (mut runtime, holder) = setup_owned_holder();
        let mut tl = Trustline::open_with_collateral(
            &mut runtime,
            holder,
            LINE,
            [9u8; 32],
            TrustlineCollateral::PureCredit,
        )
        .expect("pureCredit open");
        tl.draw(&runtime, digest(1), 30).expect("draw");

        // Closing over an outstanding draw refuses: the issuer cannot debit
        // the holder as a side effect of closing.
        let err = tl.close(&runtime).unwrap_err();
        assert!(
            matches!(&err, SdkError::Rejected(m) if m.contains("outstanding")),
            "{err:?}"
        );

        // Settle (holder repays), then close cleanly: no residual to return.
        assert_eq!(tl.settle(&runtime).unwrap(), 30);
        let (settled, residual) = tl.close(&runtime).expect("clean close");
        assert_eq!((settled, residual), (0, 0));
        let status = tl.status(&runtime).unwrap();
        assert!(!status.open);
        // Inert forever (no row out of CLOSED).
        let err = tl.draw(&runtime, digest(2), 1).unwrap_err();
        assert!(matches!(err, SdkError::Rejected(_)), "{err:?}");
    }
}
