//! # Flash well — the zero-duration line of credit as an SDK noun
//! (blueprint: `dregg_cell::blueprint` flash-well section; HORIZONLOG
//! product artifact, assessed feasible 2026-06-12).
//!
//! A flash well lends its liquidity for the lifetime of ONE ACTION:
//! borrowing and settlement are the same act. The enforcement is NOT this
//! builder — it is the well cell's installed program, which the executor
//! re-evaluates on every action that touches the well against the action's
//! NET `(old, new)` pair (`turn/src/executor/execute_tree.rs`: the touched-
//! set snapshot at lines 600–624, the per-cell net re-check at lines
//! 770–886). The program demands, per touch of an open well:
//!
//! * the fee ratchet climbs ≥ 1 rung (`StrictMonotonic`, whole-fee rungs
//!   via `MemberOf`) — the fee-evasion tooth;
//! * the post-balance clears the new rung's floor
//!   `principal + (rung−1)·fee` (`BalanceGte` rung ladder) — together:
//!   **post-balance ≥ pre-floor + fee**, the flash-loan invariant.
//!
//! The intra-action dip (the draw out, the caller's ring legs, the
//! repayment in) is invisible to the program by construction — programs see
//! only the net. A ring split across two actions is two nets, and the
//! borrow-only net refuses: the granularity constraint IS the atomicity of
//! the loan.
//!
//! ## Shape (the two-nouns `.turn()` ride)
//!
//! ```text
//! FlashWell::open(runtime, principal, fee, max_draws, token)   // 4-turn funded birth
//! well.borrow(&runtime, 600)?          // FlashRing: the draw leg staged
//!     .pay(me, merchant, 600)          // … the caller's ring legs …
//!     .settle()                        // repayment + ratchet climb appended
//!     .sign()?                         // TurnBuilder — the ordinary noun
//!     .submit()?                       // ONE action; Receipt or refusal
//! ```
//!
//! `settle()` hands back the ordinary [`TurnBuilder`], so the ring rides the
//! same `sign → submit → Receipt` path as every other act — there is no
//! flash-loan-special executor entry.
//!
//! ## Honest scope
//!
//! * VERIFIED 2026-06-12: this module compiles (`cargo check -p dregg-sdk`)
//!   and its 7 executor-path tests pass on the real `TurnExecutor`.
//! * Third-party borrowers reach the well by ATTENUATING the operator's
//!   adopt-time capability holder-side (delegation does not touch the well
//!   cell); a post-open `GrantCapability{from: well}` touches the well and
//!   therefore owes a fee quantum like any touch.
//! * Whole-action revert on refusal is the executor's transactionality;
//!   the tests assert it observationally (balances unchanged after a
//!   refused ring).

use dregg_cell::blueprint::{
    FW_FEE_SLOT, FW_OWNER_SLOT, FW_PRINCIPAL_SLOT, FW_RATCHET_SLOT, FW_STATE_CLOSED, FW_STATE_SLOT,
    FlashWellError, FlashWellTerms, STATE_OPEN, flash_well_accrued_fees,
    flash_well_factory_descriptor,
};
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::program::field_from_u64;
use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CellId, CellMode};
use dregg_turn::Effect;

use crate::error::SdkError;
use crate::factories::ADOPT_TURN_FEE;
use crate::runtime::AgentRuntime;
use crate::turns::TurnBuilder;

/// Decode a slot's trailing big-endian u64 (the cell-program encoding).
fn field_to_u64(f: FieldElement) -> u64 {
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

/// A planned flash well: the published per-well factory + the four turns
/// that birth, fund, adopt, and open it — the settlement-plan lifecycle
/// ([`crate::factories`]) on the flash-well slot schema.
#[derive(Clone, Debug)]
pub struct FlashWellPlan {
    /// The per-well, content-addressed factory descriptor. Deploy BEFORE
    /// executing [`Self::create_effects`].
    pub descriptor: FactoryDescriptor,
    /// `descriptor.factory_vk`, for convenience.
    pub factory_vk: [u8; 32],
    /// The deterministic id of the well cell.
    pub cell_id: CellId,
    /// Turn 1 (operator agent turn): birth the cell from the factory.
    pub create_effects: Vec<Effect>,
    /// Turn 2 (funder agent turn): move `principal + ADOPT_TURN_FEE` into
    /// the well while it is still UNINIT (funding an OPEN well would owe a
    /// fee quantum like any touch — fund first).
    pub fund_effects: Vec<Effect>,
    /// Turn 3 (cell-agent turn, fee [`ADOPT_TURN_FEE`]): the well grants the
    /// operator driving reach (borrowers attenuate from this grant
    /// holder-side; the well cell is untouched by that delegation).
    pub adopt_effects: Vec<Effect>,
    /// Turn 4 (operator turn): write the terms, prime the ratchet at rung 1
    /// (`1·fee`), and step UNINIT → OPEN. The program pins every term to the
    /// descriptor's literals from here on.
    pub open_effects: Vec<Effect>,
}

/// Plan a new flash well. `owner_pubkey` is both the key the executor
/// verifies well-targeted turns against AND the program's lifecycle
/// (`SenderIs`) governor; `token_id` disambiguates wells under one owner.
pub fn plan_flash_well(
    terms: &FlashWellTerms,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<FlashWellPlan, FlashWellError> {
    let descriptor = flash_well_factory_descriptor(terms)?;
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
    let fund_effects = vec![Effect::Transfer {
        from: funder,
        to: cell_id,
        amount: terms.principal + ADOPT_TURN_FEE,
    }];
    let adopt_effects = vec![Effect::GrantCapability {
        from: cell_id,
        to: operator,
        cap: CapabilityRef {
            target: cell_id,
            slot: 0, // assigned by the recipient c-list at install
            permissions: dregg_cell::AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }];
    let set = |index: u8, value: FieldElement| Effect::SetField {
        cell: cell_id,
        index: index as usize,
        value,
    };
    let open_effects = vec![
        set(FW_PRINCIPAL_SLOT, field_from_u64(terms.principal)),
        set(FW_FEE_SLOT, field_from_u64(terms.fee)),
        set(FW_OWNER_SLOT, terms.owner),
        // Rung 1: the priming quantum (the open turn is itself an
        // open-well-ending touch, so the strict tooth demands a climb).
        set(FW_RATCHET_SLOT, field_from_u64(terms.fee)),
        set(FW_STATE_SLOT, field_from_u64(STATE_OPEN)),
    ];
    Ok(FlashWellPlan {
        descriptor,
        factory_vk,
        cell_id,
        create_effects,
        fund_effects,
        adopt_effects,
        open_effects,
    })
}

/// A live flash-well position, read from the cell's registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FlashWellStatus {
    /// The published liquidity floor.
    pub principal: u64,
    /// The published flat fee per use.
    pub fee: u64,
    /// The fee-schedule position (rung × fee).
    pub ratchet: u64,
    /// Redeemable accrued fees: `ratchet − fee` (the priming quantum is the
    /// schedule origin, not income).
    pub accrued_fees: u64,
    /// The well's actual balance (principal + accrued fees + any cushion).
    pub balance: i64,
    /// Whether the well is OPEN (lending).
    pub open: bool,
    /// Rungs left before exhaustion (`max_draws` is content-addressed into
    /// the descriptor; this reads the live headroom from the ratchet).
    pub draws_remaining: u64,
}

/// An open flash-well handle: the lending surface over the owner runtime's
/// normal `.turn()` path.
#[derive(Clone, Debug)]
pub struct FlashWell {
    /// The well cell.
    pub cell: CellId,
    /// The published terms.
    pub terms: FlashWellTerms,
    /// The operator's c-list slot holding the adopt-time capability over the
    /// well. Every well-touching effect (the draw `Transfer{from: well}`, the
    /// ratchet `SetField{cell: well}`, the close `SetField`+sweep) rides
    /// [`Effect::ExerciseViaCapability`] at this slot — a bare cross-cell
    /// `Transfer`/`SetField` is unconditionally denied by the executor
    /// whenever the well's `Send`/`SetState` permission is not `None`
    /// (`turn/src/executor/apply.rs:2338`), and the well defaults to
    /// `Signature` (`dregg_cell::permissions::Permissions::default_user`).
    /// The capability path admits instead via
    /// `cap.permissions.is_narrower_or_equal(target_required)`
    /// (`apply.rs:1293-1324`), which the adopt grant's `Signature` permission
    /// satisfies.
    pub cap_slot: u32,
}

/// Discover the operator's c-list slot holding a capability over `well`
/// (installed by the adopt-time self-grant). The borrower drives every
/// well-touching effect through this slot.
fn well_cap_slot(runtime: &AgentRuntime, operator: CellId, well: CellId) -> Result<u32, SdkError> {
    let ledger = runtime.ledger().lock().unwrap();
    let cell = ledger
        .get(&operator)
        .ok_or_else(|| SdkError::Rejected("operator cell not in ledger".into()))?;
    cell.capabilities
        .iter()
        .find(|cap| cap.target == well)
        .map(|cap| cap.slot)
        .ok_or_else(|| {
            SdkError::Rejected(
                "operator holds no capability over the flash well (adopt grant missing)".into(),
            )
        })
}

impl FlashWell {
    /// **Open a well**: this runtime's agent publishes a flash well of
    /// `principal` at flat `fee`, good for `max_draws` rings. Runs the
    /// four-turn factory lifecycle (create → fund → adopt → open) through
    /// the normal `.turn()` machinery; the executor installs the per-well
    /// program at birth and re-checks it on every touch thereafter.
    pub fn open(
        runtime: &mut AgentRuntime,
        principal: u64,
        fee: u64,
        max_draws: u32,
        token_id: [u8; 32],
    ) -> Result<Self, SdkError> {
        let operator = runtime.cell_id();
        let owner_pubkey = runtime
            .cipherclerk()
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key()
            .0;
        let terms = FlashWellTerms {
            principal,
            fee,
            owner: owner_pubkey,
            max_draws,
        };
        let plan = plan_flash_well(&terms, owner_pubkey, token_id, operator, operator)
            .map_err(|e| SdkError::Rejected(format!("flash-well terms refused: {e}")))?;
        runtime.deploy_factory(plan.descriptor.clone());
        runtime.execute(plan.create_effects.clone())?;
        runtime.execute(plan.fund_effects.clone())?;
        runtime.execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)?;
        runtime.execute_on(plan.cell_id, plan.open_effects.clone())?;
        let cap_slot = well_cap_slot(runtime, operator, plan.cell_id)?;
        Ok(FlashWell {
            cell: plan.cell_id,
            terms,
            cap_slot,
        })
    }

    /// Read the live position from the cell's registers.
    pub fn status(&self, runtime: &AgentRuntime) -> Result<FlashWellStatus, SdkError> {
        let ledger = runtime.ledger().lock().unwrap();
        let cell = ledger
            .get(&self.cell)
            .ok_or_else(|| SdkError::Rejected("flash-well cell not in ledger".into()))?;
        let principal = field_to_u64(cell.state.fields[FW_PRINCIPAL_SLOT as usize]);
        let fee = field_to_u64(cell.state.fields[FW_FEE_SLOT as usize]);
        let ratchet = field_to_u64(cell.state.fields[FW_RATCHET_SLOT as usize]);
        let state = field_to_u64(cell.state.fields[FW_STATE_SLOT as usize]);
        let rung = ratchet.checked_div(fee).unwrap_or(0);
        let top_rung = self.terms.max_draws as u64 + 1;
        Ok(FlashWellStatus {
            principal,
            fee,
            ratchet,
            accrued_fees: flash_well_accrued_fees(ratchet, fee),
            balance: cell.state.balance(),
            open: state == STATE_OPEN,
            draws_remaining: top_rung.saturating_sub(rung),
        })
    }

    /// **Borrow** `amount` from the well: stage the draw leg and return a
    /// [`FlashRing`] the caller extends with ring legs and then
    /// [`settle`](FlashRing::settle)s — ALL within one action's effects.
    /// The drawn value lands in this runtime's agent cell.
    ///
    /// Fail-closed mirrors (the program is the real gate; these only shape
    /// errors): the well must be open, un-exhausted, and hold `amount`.
    pub fn borrow<'rt>(
        &self,
        runtime: &'rt AgentRuntime,
        amount: u64,
    ) -> Result<FlashRing<'rt>, SdkError> {
        let status = self.status(runtime)?;
        if !status.open {
            return Err(SdkError::Rejected("flash well is not open".into()));
        }
        if status.draws_remaining == 0 {
            return Err(SdkError::Rejected(
                "flash well is exhausted (last rung reached) — close and reopen".into(),
            ));
        }
        if i128::from(amount) > i128::from(status.balance) {
            return Err(SdkError::Rejected(format!(
                "draw {amount} exceeds well balance {}",
                status.balance
            )));
        }
        let next_ratchet = status
            .ratchet
            .checked_add(status.fee)
            .ok_or_else(|| SdkError::Rejected("flash-well ratchet overflow".into()))?;
        let borrower = runtime.cell_id();
        // The action targets the OPERATOR AGENT (the default turn), so the
        // agent's own ring legs (the merchant pay, the repayment) are
        // direct sends (`from == action_target`, authorized by the agent's
        // signature). The WELL-touching effects — the draw `Transfer{from:
        // well}` here and the ratchet `SetField{cell: well}` in `settle()` —
        // ride `ExerciseViaCapability` at the operator's adopt-grant slot:
        // a bare cross-cell `Transfer`/`SetField` is unconditionally denied
        // while the well requires `Signature` (`apply.rs:2338`), whereas the
        // capability path admits via `is_narrower_or_equal` (`apply.rs:1293`).
        let builder = runtime.turn().effect(Effect::ExerciseViaCapability {
            cap_slot: self.cap_slot,
            inner_effects: vec![Effect::Transfer {
                from: self.cell,
                to: borrower,
                amount,
            }],
        });
        Ok(FlashRing {
            builder,
            well: self.cell,
            borrower,
            amount,
            fee: status.fee,
            next_ratchet,
            cap_slot: self.cap_slot,
        })
    }

    /// **Close and sweep** (owner): step OPEN → CLOSED and move the entire
    /// balance (principal + accrued fees) to `sweep_to`, in one action.
    /// CLOSED is terminal/inert — the program admits no further touch.
    pub fn close(&self, runtime: &AgentRuntime, sweep_to: CellId) -> Result<(), SdkError> {
        let status = self.status(runtime)?;
        let balance = u64::try_from(status.balance).unwrap_or(0);
        // The state write (OPEN → CLOSED) and the sweep both touch the well,
        // so both ride `ExerciseViaCapability` at the operator's adopt slot
        // (see `borrow`): the action targets the operator agent, and the
        // capability admits the otherwise-denied cross-cell `SetField`/`Send`.
        runtime
            .turn()
            .effect(Effect::ExerciseViaCapability {
                cap_slot: self.cap_slot,
                inner_effects: vec![
                    Effect::SetField {
                        cell: self.cell,
                        index: FW_STATE_SLOT as usize,
                        value: field_from_u64(FW_STATE_CLOSED),
                    },
                    Effect::Transfer {
                        from: self.cell,
                        to: sweep_to,
                        amount: balance,
                    },
                ],
            })
            .sign()?
            .submit()?;
        Ok(())
    }
}

/// One flash ring under assembly: the draw leg is staged; extend with
/// [`leg`](Self::leg)/[`pay`](Self::pay); [`settle`](Self::settle) appends
/// the repayment + the ratchet climb and hands back the ordinary
/// [`TurnBuilder`] for `.sign()?.submit()?`.
///
/// There is deliberately NO way to submit a ring without settling: the only
/// exit from this type is `settle()` (or dropping the ring unsubmitted).
/// And settling is not what makes the ring safe — the well program refuses
/// any net that misses the floor, however the effects were assembled.
#[derive(Debug)]
pub struct FlashRing<'rt> {
    builder: TurnBuilder<'rt>,
    well: CellId,
    borrower: CellId,
    amount: u64,
    fee: u64,
    next_ratchet: u64,
    cap_slot: u32,
}

impl<'rt> FlashRing<'rt> {
    /// The cell the drawn value landed in (this runtime's agent cell) —
    /// the `from` for ring legs spending the borrowed liquidity.
    pub fn borrower(&self) -> CellId {
        self.borrower
    }

    /// The repayment owed at settlement: `amount + fee`.
    pub fn owed(&self) -> u64 {
        self.amount + self.fee
    }

    /// Append one arbitrary ring leg (any effect; the executor's gates and
    /// every touched cell's program apply identically).
    pub fn leg(mut self, effect: Effect) -> Self {
        self.builder = self.builder.effect(effect);
        self
    }

    /// Sugar: a value-moving ring leg.
    pub fn pay(mut self, from: CellId, to: CellId, amount: u64) -> Self {
        self.builder = self.builder.transfer_from(from, to, amount);
        self
    }

    /// Append the settlement legs — repay `amount + fee` from the borrower
    /// back into the well and climb the ratchet one rung — and return the
    /// ordinary [`TurnBuilder`]. Everything staged so far rides ONE action:
    /// the program admits or refuses the whole ring on its net.
    ///
    /// The repayment is a direct agent send (`from == action_target`, the
    /// borrower IS the acting agent). The ratchet climb is a `SetField` on
    /// the well, so it rides `ExerciseViaCapability` at the operator's adopt
    /// slot like the draw (a bare cross-cell `SetField` would be denied).
    pub fn settle(self) -> TurnBuilder<'rt> {
        self.builder
            .transfer_from(self.borrower, self.well, self.amount + self.fee)
            .effect(Effect::ExerciseViaCapability {
                cap_slot: self.cap_slot,
                inner_effects: vec![Effect::SetField {
                    cell: self.well,
                    index: FW_RATCHET_SLOT as usize,
                    value: field_from_u64(self.next_ratchet),
                }],
            })
    }
}

// =============================================================================
// Executor-path tests: the four flash-well laws on the REAL TurnExecutor
// (the per-action snapshot + net re-check of
// `turn/src/executor/execute_tree.rs:600-624` / `:770-886`). The
// executor-independent program-level twins live in
// `dregg_cell::blueprint::flash_well_tests`.
//
// VERIFIED 2026-06-12: all 7 pass on the real TurnExecutor. The well-touching
// effects ride `ExerciseViaCapability` (a bare cross-cell Transfer/SetField is
// unconditionally denied while the well requires Signature — apply.rs:2338);
// the refusal tests drive that SAME capability path so the verdict is the
// program's net-floor (`ProgramViolation`), not the permission gate.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::AgentCipherclerk;

    const PRINCIPAL: u64 = 1_000;
    const FEE: u64 = 10;
    const DRAW: u64 = 600;
    const FUNDING: u64 = 1_000_000;

    /// A funded owner/borrower runtime + a merchant cell on the same ledger
    /// (the trustline-test fixture shape).
    fn setup() -> (AgentRuntime, CellId) {
        let cclerk = AgentCipherclerk::new();
        let owner_pk = cclerk.public_key().0;
        let runtime = AgentRuntime::new_simple(cclerk, "flashwell-test");
        let merchant_pk = blake3::derive_key("flashwell-test-merchant-v1", b"merchant");
        let merchant_cell = dregg_cell::Cell::with_balance(merchant_pk, [0u8; 32], 500);
        let merchant = merchant_cell.id();
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger.insert_cell(merchant_cell).unwrap();
            let agent = runtime.cell_id();
            if ledger.get(&agent).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let cell = dregg_cell::Cell::with_balance(owner_pk, token, 0);
                assert_eq!(cell.id(), agent, "derivation must match runtime");
                ledger.insert_cell(cell).unwrap();
            }
            assert!(
                ledger
                    .get_mut(&agent)
                    .unwrap()
                    .state
                    .credit_balance(FUNDING),
                "agent accepts funding"
            );
        }
        (runtime, merchant)
    }

    fn balance(runtime: &AgentRuntime, cell: CellId) -> i64 {
        runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    }

    fn open_well(runtime: &mut AgentRuntime) -> FlashWell {
        FlashWell::open(runtime, PRINCIPAL, FEE, 4, [0x11u8; 32]).expect("open well")
    }

    /// Hand-assemble a one-action ring on the well WITHOUT the SDK builder,
    /// so the refusal tests exercise the well-touching effects through the
    /// SAME capability path the honest ring uses (the action targets the
    /// agent; the well legs ride `ExerciseViaCapability`). This is what makes
    /// the refusals land on the PROGRAM's net-floor verdict
    /// (`TurnError::ProgramViolation`) rather than the permission gate — a
    /// bare `.on(well)` transfer is denied for the wrong reason
    /// (`PermissionDenied`) and would launder the law into a vacuous pass.
    ///
    /// `draw` is moved well→agent; each `(to, amt)` in `repays` is an agent
    /// send; `new_ratchet` (if `Some`) writes the ratchet via the cap.
    fn raw_ring(
        runtime: &AgentRuntime,
        well: &FlashWell,
        draw: u64,
        repays: &[(CellId, u64)],
        new_ratchet: Option<u64>,
    ) -> Result<(), SdkError> {
        let me = runtime.cell_id();
        let mut builder = runtime.turn().effect(Effect::ExerciseViaCapability {
            cap_slot: well.cap_slot,
            inner_effects: vec![Effect::Transfer {
                from: well.cell,
                to: me,
                amount: draw,
            }],
        });
        for (to, amt) in repays {
            builder = builder.transfer_from(me, *to, *amt);
        }
        if let Some(r) = new_ratchet {
            builder = builder.effect(Effect::ExerciseViaCapability {
                cap_slot: well.cap_slot,
                inner_effects: vec![Effect::SetField {
                    cell: well.cell,
                    index: FW_RATCHET_SLOT as usize,
                    value: field_from_u64(r),
                }],
            });
        }
        builder.sign()?.submit()?;
        Ok(())
    }

    #[test]
    fn open_funds_the_well_at_the_principal() {
        let (mut runtime, _merchant) = setup();
        let well = open_well(&mut runtime);
        // Funded birth: fund moved principal + ADOPT_TURN_FEE; adopt burned
        // its fee; exactly the principal remains.
        assert_eq!(balance(&runtime, well.cell), PRINCIPAL as i64);
        let s = well.status(&runtime).unwrap();
        assert!(s.open);
        assert_eq!((s.principal, s.fee, s.ratchet), (PRINCIPAL, FEE, FEE));
        assert_eq!(s.accrued_fees, 0, "the priming quantum is not income");
        assert_eq!(s.draws_remaining, 4);
    }

    /// LAW 1 — the honest ring succeeds: borrow, use the liquidity, repay
    /// `+fee`, all in ONE action. The program admits the NET (the executor
    /// snapshots the well before the action's effects and re-checks on the
    /// (pre, post) pair — execute_tree.rs:600-624 / :770-886); the
    /// intra-action dip below the floor is invisible by construction.
    #[test]
    fn honest_ring_succeeds() {
        let (mut runtime, merchant) = setup();
        let well = open_well(&mut runtime);
        let merchant_before = balance(&runtime, merchant);

        let ring = well.borrow(&runtime, DRAW).expect("borrow");
        let me = ring.borrower();
        assert_eq!(ring.owed(), DRAW + FEE);
        ring.pay(me, merchant, DRAW) // the use: spend the borrowed liquidity
            .settle()
            .sign()
            .expect("sign")
            .submit()
            .expect("the honest ring must commit");

        // The well netted +fee; the merchant really got paid.
        assert_eq!(balance(&runtime, well.cell), (PRINCIPAL + FEE) as i64);
        assert_eq!(balance(&runtime, merchant), merchant_before + DRAW as i64);
        let s = well.status(&runtime).unwrap();
        assert_eq!(s.accrued_fees, FEE);
        assert_eq!(s.draws_remaining, 3);
    }

    /// LAW 2 — a ring missing its repayment leg refuses WHOLE: not only does
    /// the well stay intact, the merchant leg is reverted with it (one
    /// action, one verdict — `TurnError::ProgramViolation` for the net).
    #[test]
    fn missing_repayment_reverts_the_whole_ring() {
        let (mut runtime, merchant) = setup();
        let well = open_well(&mut runtime);
        let merchant_before = balance(&runtime, merchant);

        // Hand-assembled malicious ring (through the SAME capability path the
        // honest ring uses, so the refusal is the PROGRAM's net verdict, not
        // the permission gate): draw + spend at the merchant + the dutiful
        // ratchet climb, but NO repayment to the well.
        let result = raw_ring(&runtime, &well, DRAW, &[(merchant, DRAW)], Some(2 * FEE));
        assert!(result.is_err(), "a ring without repayment must refuse");

        // WHOLE-action revert: neither the well nor the merchant moved.
        assert_eq!(balance(&runtime, well.cell), PRINCIPAL as i64);
        assert_eq!(balance(&runtime, merchant), merchant_before);
        assert_eq!(well.status(&runtime).unwrap().accrued_fees, 0);
    }

    /// LAW 3 — an under-fee ring refuses; the exact fee is the boundary.
    #[test]
    fn under_fee_refuses() {
        let (mut runtime, _merchant) = setup();
        let well = open_well(&mut runtime);

        // Repay one unit short of the fee: refused by the rung-2 floor.
        let short = raw_ring(
            &runtime,
            &well,
            DRAW,
            &[(well.cell, DRAW + FEE - 1)],
            Some(2 * FEE),
        );
        assert!(short.is_err(), "one unit under the fee must refuse");
        assert_eq!(balance(&runtime, well.cell), PRINCIPAL as i64);

        // The boundary: exactly +fee commits (and is what settle() builds).
        well.borrow(&runtime, DRAW)
            .expect("borrow")
            .settle()
            .sign()
            .expect("sign")
            .submit()
            .expect("the exact-fee ring must commit");
        assert_eq!(balance(&runtime, well.cell), (PRINCIPAL + FEE) as i64);
    }

    /// LAW 4 — THE GRANULARITY CONSTRAINT: the same ring split across TWO
    /// actions refuses. The program evaluates per ACTION over the net
    /// (old, new) pair — `execute_tree.rs` snapshots every touched cell
    /// before one action's effects (lines 600–624, over
    /// `collect_touched_cells`, authorize.rs:2127) and re-checks each
    /// touched cell's program after them (lines 770–886). The borrow action
    /// alone nets the well down `DRAW`; no credit carries to a later action.
    #[test]
    fn ring_split_across_two_actions_refuses() {
        let (mut runtime, _merchant) = setup();
        let well = open_well(&mut runtime);

        // Action 1 of the split: the draw (with the dutiful ratchet climb)
        // and NO repayment leg — refused by the rung-2 floor on this action's
        // own net (a program verdict, via the capability path).
        let action1 = raw_ring(&runtime, &well, DRAW, &[], Some(2 * FEE));
        assert!(
            action1.is_err(),
            "the borrow half of a split ring must refuse (rung floor on THIS action's net)"
        );
        // And without the climb it refuses on the fee-evasion tooth instead.
        let action1_sneaky = raw_ring(&runtime, &well, DRAW, &[], None);
        assert!(action1_sneaky.is_err());
        assert_eq!(balance(&runtime, well.cell), PRINCIPAL as i64);
        // (The fused single-action twin of these legs is exactly
        // `honest_ring_succeeds` — granularity is the only difference.)
    }

    /// The fee-evasion tooth: borrow and repay EXACTLY (net-zero, no climb)
    /// refuses — every action touching an open well pays the fee.
    #[test]
    fn fee_evasion_refused() {
        let (mut runtime, _merchant) = setup();
        let well = open_well(&mut runtime);

        // Borrow and repay EXACTLY (net-zero), no ratchet climb: refused by
        // the strict-on-touch tooth (the program, via the capability path).
        let freeloader = raw_ring(&runtime, &well, DRAW, &[(well.cell, DRAW)], None);
        assert!(
            freeloader.is_err(),
            "a net-zero use without the ratchet climb must refuse (StrictMonotonic on touch)"
        );
        assert_eq!(balance(&runtime, well.cell), PRINCIPAL as i64);
    }

    /// Owner exit: close sweeps principal + accrued fees in one action and
    /// the well is inert thereafter.
    #[test]
    fn close_sweeps_and_well_goes_inert() {
        let (mut runtime, merchant) = setup();
        let well = open_well(&mut runtime);
        // One honest ring so there is an accrued fee to sweep.
        well.borrow(&runtime, DRAW)
            .expect("borrow")
            .settle()
            .sign()
            .expect("sign")
            .submit()
            .expect("ring");
        // Sweep to the merchant (a third-party payout cell) so the assertion
        // isolates the sweep economics from the agent's orthogonal turn-fee
        // payment: the merchant receives EXACTLY principal + accrued fee.
        let merchant_before = balance(&runtime, merchant);
        well.close(&runtime, merchant).expect("close");
        assert_eq!(balance(&runtime, well.cell), 0);
        assert_eq!(
            balance(&runtime, merchant),
            merchant_before + (PRINCIPAL + FEE) as i64
        );

        // CLOSED is terminal/inert: no more rings, no reopening.
        assert!(
            well.borrow(&runtime, 1).is_err(),
            "closed well refuses borrows"
        );
        let reopen = runtime
            .turn()
            .on(well.cell)
            .write_u64(FW_STATE_SLOT as usize, STATE_OPEN)
            .sign()
            .expect("sign")
            .submit();
        assert!(reopen.is_err(), "a closed well admits no transition out");
    }
}
