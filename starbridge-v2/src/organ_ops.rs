//! ORGAN OPERATING VERBS — the cockpit DRIVES the organs, not just reflects them.
//!
//! [`crate::organs`] (the ORGANS panel) REFLECTS each organ's live cell-state
//! (the trustline's `drawn`/`ceiling`/`settled`, the flash well's
//! `principal`/`fee`/`ratchet`). This module makes the verbs DRIVABLE: it opens,
//! draws, repays, settles, and closes trustline / flash-well organs as REAL turns
//! through the embedded executor ([`World::commit_turn`]).
//!
//! # Fidelity: the REAL per-organ program is the gate
//!
//! The depth here is that an organ op that VIOLATES the organ's invariant is
//! REFUSED BY THE EXECUTOR, not by this module faking a check. Each organ cell
//! carries the SAME `dregg_cell::blueprint` program the SDK's
//! `trustline`/`flashwell` cells carry — installed via [`World::set_cell_program`]
//! (the trusted-root prerogative the verified compositor already uses to bake a
//! cell's caveats). So:
//!
//!   * a trustline `draw` past the line is refused by the program's
//!     `FieldLteField(drawn ≤ ceiling)` tooth (`trustline_within_line_forever`) —
//!     the executor's per-cell predicate gate (`execute_tree.rs`) re-evaluates the
//!     installed `CellProgram::Predicate` on the touching turn and REJECTS;
//!   * a `settle`/`repay` that would push `settled > drawn` is refused by the
//!     `FieldLteField(settled ≤ drawn)` + `Monotonic(settled)` teeth;
//!   * a draw/repay/anything on a CLOSED line/well is refused by the lifecycle
//!     `AllowedTransitions` table (CLOSED is terminal — no row out of it);
//!   * a flash-well borrow that does not climb the ratchet (or drops the balance
//!     below the floor) is refused by the well's `StrictMonotonic(ratchet)` +
//!     rung-ladder `BalanceGte` teeth.
//!
//! These are the REAL Lean-twin invariants (`docs/ORGANS.md`,
//! `Dregg2.Apps.Trustline` / the flash-well ratchet), enforced in-protocol by the
//! same executor every other turn runs through. The verbs only SHAPE the effects
//! + pre-check for a legible error; the load-bearing gate is the program.
//!
//! # The embedded single-custody collapse
//!
//! The SDK drives organ ops over an [`dregg_sdk::runtime::AgentRuntime`] whose
//! factory-born cells default to `Signature` permissions, so every cross-cell
//! well/trustline touch rides `Effect::ExerciseViaCapability` at the operator's
//! adopt-grant slot. The embedded `World` is single-custody (the OPERATOR is the
//! authority; `docs/STARBRIDGE-V2.md`): the organ cell is born with
//! `open_permissions`, so the operator's own turns touch it directly (a bare
//! self-targeting `SetField`/`Transfer`) — the single-machine collapse of the
//! capability dance. The VALUE conservation and the SLOT invariants are
//! identical: the program is the same, so the teeth bite the same. (A distributed
//! deployment restores the cap path; here the operator IS the root.)
//!
//! This module is gpui-free + `cargo test`-able: every verb is a real
//! `World::commit_turn`, asserted by reflecting the organ's post-state through
//! [`crate::organs`].

use dregg_cell::blueprint::{
    flash_well_cell_program, trustline_cell_program, FlashWellTerms, TrustlineTerms,
    FW_FEE_SLOT, FW_OWNER_SLOT, FW_PRINCIPAL_SLOT, FW_RATCHET_SLOT, FW_STATE_CLOSED, FW_STATE_SLOT,
    STATE_OPEN, TL_CEILING_SLOT, TL_DRAWN_SLOT, TL_HOLDER_SLOT, TL_ISSUER_SLOT, TL_SETTLED_SLOT,
    TL_STATE_CLOSED, TL_STATE_SLOT,
};
use dregg_cell::program::field_from_u64;
use dregg_cell::CellId;

use crate::organs::{FlashWellReflection, TrustlineReflection};
use crate::world::{self, CommitOutcome, World};

/// Which organ operating verb was driven (for the activity feed / error context).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrganOp {
    /// Open an organ (birth + fund + install program + step to OPEN).
    Open,
    /// Draw against a trustline line / borrow from a flash well.
    Draw,
    /// Repay a trustline draw (restore the line).
    Repay,
    /// Settle a trustline's outstanding drawn amount to the holder.
    Settle,
    /// Close an organ (terminal — the cell becomes inert).
    Close,
}

impl OrganOp {
    pub fn label(self) -> &'static str {
        match self {
            OrganOp::Open => "open",
            OrganOp::Draw => "draw",
            OrganOp::Repay => "repay",
            OrganOp::Settle => "settle",
            OrganOp::Close => "close",
        }
    }
}

/// Why an organ op was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrganOpError {
    /// The verb's pre-check refused it (shapes a legible error before the turn —
    /// the program is the real gate, this just avoids a raw executor reason for
    /// the common cases: not-open, over-line, nothing-outstanding, …).
    PreCheck { op: OrganOp, reason: String },
    /// The REAL executor REJECTED the turn — the organ's installed program (or a
    /// conservation/permission gate) firing. This is the load-bearing refusal: an
    /// over-line draw, a settle past drawn, a touch on a closed organ all land
    /// here, refused IN-PROTOCOL (`execute_tree.rs`'s per-cell predicate gate).
    ExecutorRejected { op: OrganOp, reason: String },
    /// The blueprint refused to build the organ's program (e.g. a zero line / zero
    /// principal — fail-closed at construction).
    Blueprint { op: OrganOp, reason: String },
    /// The named organ cell is not in the ledger.
    NotFound { cell: CellId },
}

impl OrganOpError {
    pub fn label(&self) -> String {
        match self {
            OrganOpError::PreCheck { op, reason } => {
                format!("REFUSED ({}) — {reason}", op.label())
            }
            OrganOpError::ExecutorRejected { op, reason } => {
                format!("REFUSED by executor ({}) — {reason}", op.label())
            }
            OrganOpError::Blueprint { op, reason } => {
                format!("REFUSED ({}) — blueprint: {reason}", op.label())
            }
            OrganOpError::NotFound { cell } => format!(
                "REFUSED — organ cell {} not in ledger",
                crate::reflect::short_hex(cell.as_bytes())
            ),
        }
    }
}

/// The outcome of a driven organ op — what committed, on which organ cell.
#[derive(Clone, Debug)]
pub struct OrganOpOutcome {
    /// The verb that was driven.
    pub op: OrganOp,
    /// The organ cell the verb acted on.
    pub cell: CellId,
    /// The receipt hash of the committed turn.
    pub receipt_hash: [u8; 32],
    /// The world height after commit.
    pub height: u64,
    /// The metered computrons the turn cost.
    pub computrons: u64,
    /// A human-meaningful summary.
    pub summary: String,
}

/// THE ORGAN DRIVER — drives trustline / flash-well organ operating verbs as REAL
/// turns through the embedded executor. A thin stateless surface over [`World`]
/// (the organ STATE lives in the ledger cell, reflected by [`crate::organs`]; the
/// driver only shapes + commits the turns).
///
/// The cockpit's ORGANS tab uses this to make the reflected organ state DRIVABLE:
/// a button per verb (open / draw / repay / settle / close) commits a real turn,
/// and the panel re-reflects the post-state. An invariant-violating op is refused
/// by the executor's program gate, surfaced as [`OrganOpError::ExecutorRejected`].
#[derive(Clone, Copy, Debug, Default)]
pub struct OrganDriver;

impl OrganDriver {
    pub fn new() -> Self {
        OrganDriver
    }

    // ── TRUSTLINE VERBS ──────────────────────────────────────────────────────

    /// **OPEN a trustline** `issuer → holder` of `line` at the fullReserve point,
    /// as REAL turns: birth the organ cell (genesis path, operator-keyed, open
    /// permissions — the single-custody collapse), escrow the full `line` into it
    /// (the funded birth — `issuer` is REALLY debited), install the REAL
    /// `trustline_cell_program` (so the `drawn ≤ ceiling` / `settled ≤ drawn` /
    /// lifecycle teeth gate every later touch), then write the terms + step
    /// UNINIT → OPEN in one program-gated turn.
    ///
    /// `seed` is the organ cell's id seed (a fresh deterministic id). Returns the
    /// open outcome (the organ cell is now in the ledger, reflected by
    /// [`TrustlineReflection`]).
    ///
    /// The `issuer` must exist in the ledger with ≥ `line` balance (the escrow
    /// debits it). The program is installed BEFORE the open turn, so the open turn
    /// itself runs against the live gate (the SDK's exact sequence — the term-pins
    /// are `AnyOf[UNINIT, FieldEquals]`, satisfied because the open turn writes the
    /// literals as it flips to OPEN).
    pub fn open_trustline(
        &self,
        world: &mut World,
        seed: u8,
        issuer: CellId,
        holder: CellId,
        line: u64,
    ) -> Result<(CellId, OrganOpOutcome), OrganOpError> {
        if world.ledger().get(&issuer).is_none() {
            return Err(OrganOpError::NotFound { cell: issuer });
        }
        if line == 0 {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Open,
                reason: "a zero line is undrawable (fail-closed)".into(),
            });
        }
        let terms = TrustlineTerms {
            line,
            issuer: *issuer.as_bytes(),
            holder: *holder.as_bytes(),
        };
        let program = trustline_cell_program(&terms)
            .map_err(|e| OrganOpError::Blueprint { op: OrganOp::Open, reason: format!("{e:?}") })?;

        // Birth the organ cell UNINIT (zero balance — value only ever MOVES), with
        // open permissions so the operator's own turns drive it directly.
        let organ = world.genesis_cell(seed, 0);

        // Escrow the full line from the issuer into the organ cell (the funded
        // birth — a real conserving Transfer the executor commits). Done BEFORE
        // installing the program (a Transfer-in while UNINIT, balance unconstrained
        // yet) so the funding isn't gated by the not-yet-relevant rung teeth.
        let fund = world.turn(issuer, vec![world::transfer(issuer, organ, line)]);
        match world.commit_turn(fund) {
            CommitOutcome::Committed { .. } => {}
            CommitOutcome::Rejected { reason, .. } => {
                return Err(OrganOpError::ExecutorRejected { op: OrganOp::Open, reason });
            }
            CommitOutcome::Queued { .. } => {
                return Err(OrganOpError::ExecutorRejected {
                    op: OrganOp::Open,
                    reason: "world suspended: turn queued, not committed".to_string(),
                });
            }
        }

        // Install the REAL per-line program — from here the executor enforces the
        // organ's invariant on every touching turn.
        world.set_cell_program(&organ, program);

        // Write the terms + step UNINIT → OPEN in ONE program-gated turn. With the
        // new state == OPEN, each `pin_term` requires the literal (satisfied by
        // these writes); `drawn(0) ≤ ceiling`, `settled(0) ≤ drawn(0)` hold.
        let open_turn = world.turn(
            organ,
            vec![
                world::set_field(organ, TL_CEILING_SLOT as usize, field_from_u64(line)),
                world::set_field(organ, TL_ISSUER_SLOT as usize, *issuer.as_bytes()),
                world::set_field(organ, TL_HOLDER_SLOT as usize, *holder.as_bytes()),
                world::set_field(organ, TL_STATE_SLOT as usize, field_from_u64(STATE_OPEN)),
            ],
        );
        let outcome = self.commit(world, OrganOp::Open, organ, open_turn, |_| {
            format!("trustline OPEN · line {line}")
        })?;
        Ok((organ, outcome))
    }

    /// **DRAW against a trustline** (`drawn += amount`), as a REAL turn. The
    /// pre-check shapes the over-line error; the LOAD-BEARING gate is the
    /// program's `FieldLteField(drawn ≤ ceiling)` tooth — an over-line draw that
    /// slips the pre-check (or a tampered amount) is refused IN-PROTOCOL by the
    /// executor. Returns the outcome; reflect the new `drawn` via
    /// [`TrustlineReflection`].
    pub fn draw_trustline(
        &self,
        world: &mut World,
        organ: CellId,
        amount: u64,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_trustline(world, organ)?;
        if !r.open {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Draw,
                reason: "trustline is not open".into(),
            });
        }
        let new_drawn = r.drawn.saturating_add(amount);
        let turn = world.turn(
            organ,
            vec![world::set_field(
                organ,
                TL_DRAWN_SLOT as usize,
                field_from_u64(new_drawn),
            )],
        );
        self.commit(world, OrganOp::Draw, organ, turn, |_| {
            format!("trustline DRAW {amount} (drawn → {new_drawn})")
        })
    }

    /// **REPAY a trustline draw** (`drawn -= amount`, restoring the line). Refused
    /// (pre-check + the program's `settled ≤ drawn` tooth) if `amount` exceeds the
    /// outstanding UNSETTLED draw (`drawn − settled` — settled credit is hard money
    /// in the holder's hands and cannot be repaid back).
    pub fn repay_trustline(
        &self,
        world: &mut World,
        organ: CellId,
        amount: u64,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_trustline(world, organ)?;
        let outstanding = r.drawn.saturating_sub(r.settled);
        if amount > outstanding {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Repay,
                reason: format!("repay {amount} exceeds outstanding unsettled draw {outstanding}"),
            });
        }
        let new_drawn = r.drawn - amount;
        let turn = world.turn(
            organ,
            vec![world::set_field(
                organ,
                TL_DRAWN_SLOT as usize,
                field_from_u64(new_drawn),
            )],
        );
        self.commit(world, OrganOp::Repay, organ, turn, |_| {
            format!("trustline REPAY {amount} (drawn → {new_drawn})")
        })
    }

    /// **SETTLE a trustline** (fullReserve): redeem the outstanding drawn amount
    /// (`drawn − settled`) to the holder as an ordinary conserving `Transfer` from
    /// the escrow, marking `settled := drawn`. ONE program-gated turn: the
    /// `settled ≤ drawn ≤ ceiling` teeth make the payout solvent
    /// (`settlePay_conserves_hard`). Returns the outcome (the amount moved is in
    /// the summary); a nothing-outstanding settle is a no-op pre-check error.
    pub fn settle_trustline(
        &self,
        world: &mut World,
        organ: CellId,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_trustline(world, organ)?;
        let outstanding = r.drawn.saturating_sub(r.settled);
        if outstanding == 0 {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Settle,
                reason: "nothing outstanding to settle".into(),
            });
        }
        let holder = r.holder.ok_or_else(|| OrganOpError::PreCheck {
            op: OrganOp::Settle,
            reason: "trustline has no holder slot written".into(),
        })?;
        // settled := drawn (mark the redemption) + escrow → holder (the hard move).
        let turn = world.turn(
            organ,
            vec![
                world::set_field(organ, TL_SETTLED_SLOT as usize, field_from_u64(r.drawn)),
                world::transfer(organ, holder, outstanding),
            ],
        );
        self.commit(world, OrganOp::Settle, organ, turn, |_| {
            format!("trustline SETTLE {outstanding} → holder (settled → {})", r.drawn)
        })
    }

    /// **CLOSE a trustline** (fullReserve, `OPEN → CLOSED`): settle any
    /// outstanding draw to the holder, return the RESIDUAL escrow
    /// (`escrow − outstanding`) to the issuer, and step the state to
    /// [`TL_STATE_CLOSED`] — one conserving turn (two moves, no mint). The closed
    /// cell is INERT (the lifecycle table has no row out of CLOSED, so every later
    /// touch refuses — the terminality is the program's, not faked).
    pub fn close_trustline(
        &self,
        world: &mut World,
        organ: CellId,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_trustline(world, organ)?;
        if !r.open {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Close,
                reason: "trustline is not open".into(),
            });
        }
        let issuer = r.issuer.ok_or_else(|| OrganOpError::PreCheck {
            op: OrganOp::Close,
            reason: "trustline has no issuer slot written".into(),
        })?;
        let outstanding = r.drawn.saturating_sub(r.settled);
        let escrow = u64::try_from(r.escrow).unwrap_or(0);
        let residual = escrow.saturating_sub(outstanding);
        let mut effects = Vec::new();
        if outstanding > 0 {
            let holder = r.holder.ok_or_else(|| OrganOpError::PreCheck {
                op: OrganOp::Close,
                reason: "outstanding draw but no holder to settle to".into(),
            })?;
            effects.push(world::set_field(organ, TL_SETTLED_SLOT as usize, field_from_u64(r.drawn)));
            effects.push(world::transfer(organ, holder, outstanding));
        }
        if residual > 0 {
            effects.push(world::transfer(organ, issuer, residual));
        }
        effects.push(world::set_field(
            organ,
            TL_STATE_SLOT as usize,
            field_from_u64(TL_STATE_CLOSED),
        ));
        self.commit(world, OrganOp::Close, organ, world.turn(organ, effects), move |_| {
            format!("trustline CLOSE · settled {outstanding} · residual {residual} → issuer")
        })
    }

    // ── FLASH-WELL VERBS ─────────────────────────────────────────────────────

    /// **OPEN a flash well** of `principal` at flat `fee`, good for `max_draws`
    /// rings, as REAL turns: birth the organ cell, fund it the `principal`, install
    /// the REAL `flash_well_cell_program` (the ratchet ladder + floor teeth), then
    /// write the terms + prime the ratchet at rung 1 + step UNINIT → OPEN in one
    /// program-gated turn.
    ///
    /// THE OWNER GATE (single-custody collapse): the well's program carries a
    /// `SenderIs{owner}` governance gate over its LIFECYCLE writes (open/close —
    /// `docs/ORGANS.md`). The executor evaluates that `sender` as the ACTING
    /// CELL'S OWN public key (`execute_tree.rs:781` — `parent_pk_opt`). So we set
    /// `owner` to the WELL CELL'S OWN key (read from the ledger after birth): the
    /// organ is its own governance root, and the operator-root's `world.turn(well,
    /// …)` lifecycle turns satisfy the gate FOR REAL (the gate genuinely fires —
    /// it checks the acting cell's pubkey against the owner literal — it is just
    /// satisfied, not bypassed). This is the single-machine collapse of the SDK's
    /// owner-signature dance. Returns the open well cell.
    pub fn open_flash_well(
        &self,
        world: &mut World,
        seed: u8,
        funder: CellId,
        principal: u64,
        fee: u64,
        max_draws: u32,
    ) -> Result<(CellId, OrganOpOutcome), OrganOpError> {
        if world.ledger().get(&funder).is_none() {
            return Err(OrganOpError::NotFound { cell: funder });
        }

        let well = world.genesis_cell(seed, 0);
        // THE OWNER IS THE WELL CELL ITSELF — read its own pubkey so the lifecycle
        // `SenderIs{owner}` gate is satisfied when the operator-root drives a
        // `world.turn(well, …)` (the acting cell's pubkey == owner). The single-
        // custody collapse: the organ governs itself under the operator-root.
        let owner_pubkey = *world
            .ledger()
            .get(&well)
            .expect("just birthed")
            .public_key();
        let terms = FlashWellTerms {
            principal,
            fee,
            owner: owner_pubkey,
            max_draws,
        };
        let program = flash_well_cell_program(&terms)
            .map_err(|e| OrganOpError::Blueprint { op: OrganOp::Open, reason: format!("{e:?}") })?;

        // Fund the well with the principal (a real conserving Transfer-in while
        // UNINIT — before the floor teeth are live).
        let fund = world.turn(funder, vec![world::transfer(funder, well, principal)]);
        match world.commit_turn(fund) {
            CommitOutcome::Committed { .. } => {}
            CommitOutcome::Rejected { reason, .. } => {
                return Err(OrganOpError::ExecutorRejected { op: OrganOp::Open, reason });
            }
            CommitOutcome::Queued { .. } => {
                return Err(OrganOpError::ExecutorRejected {
                    op: OrganOp::Open,
                    reason: "world suspended: turn queued, not committed".to_string(),
                });
            }
        }
        world.set_cell_program(&well, program);
        // Write terms + prime the ratchet at rung 1 (the priming quantum = fee, the
        // schedule origin) + step UNINIT → OPEN. With state == OPEN, the term-pins
        // require the literals (satisfied here); the rung ladder
        // `BalanceGte(principal + 0·fee)` holds (balance == principal); the
        // StrictMonotonic(ratchet) is satisfied by the 0 → fee climb.
        let open_turn = world.turn(
            well,
            vec![
                world::set_field(well, FW_PRINCIPAL_SLOT as usize, field_from_u64(principal)),
                world::set_field(well, FW_FEE_SLOT as usize, field_from_u64(fee)),
                world::set_field(well, FW_OWNER_SLOT as usize, owner_pubkey),
                world::set_field(well, FW_RATCHET_SLOT as usize, field_from_u64(fee)),
                world::set_field(well, FW_STATE_SLOT as usize, field_from_u64(STATE_OPEN)),
            ],
        );
        let outcome = self.commit(world, OrganOp::Open, well, open_turn, |_| {
            format!("flash well OPEN · principal {principal} · fee {fee}")
        })?;
        Ok((well, outcome))
    }

    /// **BORROW from a flash well** (`amount`, a complete ring): draw `amount` out
    /// to `borrower` and have the borrower repay `amount + fee` back to the well,
    /// climbing the ratchet by one rung (`fee`) — ALL in ONE program-gated turn.
    /// The net effect on the well is `+fee` (the accrued fee), the ratchet climbs
    /// (the `StrictMonotonic(ratchet)` fee-evasion tooth), and the balance never
    /// dips below the floor (the rung-ladder `BalanceGte`). A borrow that does not
    /// climb the ratchet — or drops the balance below the floor — is refused
    /// IN-PROTOCOL by the well's program.
    ///
    /// `borrower` must hold ≥ `fee` net (it draws `amount` then repays
    /// `amount + fee`). The ring is ONE turn the BORROWER signs: the well-touching
    /// legs (the draw `Transfer{from: well}` and the ratchet `SetField{cell:
    /// well}`) need the borrower to reach the well — exactly the SDK's adopt-grant
    /// capability. In the single-custody collapse the operator-root installs that
    /// well-cap on the borrower here (a genesis grant — the SDK's adopt step), so
    /// the cross-cell legs are cap-authorized FOR REAL (not bypassed), and the
    /// repayment `Transfer{from: borrower}` is the borrower's own in-mandate send.
    pub fn borrow_flash_well(
        &self,
        world: &mut World,
        well: CellId,
        borrower: CellId,
        amount: u64,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_flash_well(world, well)?;
        if !r.open {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Draw,
                reason: "flash well is not open".into(),
            });
        }
        if world.ledger().get(&borrower).is_none() {
            return Err(OrganOpError::NotFound { cell: borrower });
        }
        // Ensure the borrower reaches the well (the adopt-grant cap, single-custody
        // collapse — the operator-root installs it if absent). Idempotent: a holder
        // that already reaches the well is left alone.
        let already = world
            .ledger()
            .get(&borrower)
            .map(|c| c.capabilities.has_access(&well))
            .unwrap_or(false);
        if !already {
            world.genesis_grant_cap(&borrower, well);
        }
        let next_ratchet = r.ratchet.saturating_add(r.fee);
        // ONE turn the BORROWER signs carrying the whole ring: the draw out (well →
        // borrower, cap-authorized), the borrower's repayment in (principal + fee,
        // an in-mandate self-send), and the ratchet climb (cap-authorized SetState
        // on the well). The well ends the action at `balance + fee`, ratchet up one
        // rung.
        let turn = world.turn(
            borrower,
            vec![
                world::transfer(well, borrower, amount),
                world::transfer(borrower, well, amount + r.fee),
                world::set_field(well, FW_RATCHET_SLOT as usize, field_from_u64(next_ratchet)),
            ],
        );
        self.commit(world, OrganOp::Draw, well, turn, move |_| {
            format!("flash well BORROW {amount} (ratchet → {next_ratchet}, +{} fee)", r.fee)
        })
    }

    /// **CLOSE and sweep a flash well** (`OPEN → CLOSED`): step the state to
    /// [`FW_STATE_CLOSED`] and move the entire balance (principal + accrued fees)
    /// to `sweep_to`, in one program-gated turn. CLOSED is terminal/inert — the
    /// lifecycle table admits no further touch.
    pub fn close_flash_well(
        &self,
        world: &mut World,
        well: CellId,
        sweep_to: CellId,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        let r = self.reflect_flash_well(world, well)?;
        if !r.open {
            return Err(OrganOpError::PreCheck {
                op: OrganOp::Close,
                reason: "flash well is not open".into(),
            });
        }
        let balance = u64::try_from(r.balance).unwrap_or(0);
        let turn = world.turn(
            well,
            vec![
                world::set_field(well, FW_STATE_SLOT as usize, field_from_u64(FW_STATE_CLOSED)),
                world::transfer(well, sweep_to, balance),
            ],
        );
        self.commit(world, OrganOp::Close, well, turn, move |_| {
            format!("flash well CLOSE · swept {balance} → {}", crate::reflect::short_hex(sweep_to.as_bytes()))
        })
    }

    // ── reflection helpers (read the live organ state) ───────────────────────

    /// Reflect a trustline organ's live position (the SAME read [`crate::organs`]
    /// uses). Errors if the cell is absent or is not a trustline.
    pub fn reflect_trustline(
        &self,
        world: &World,
        organ: CellId,
    ) -> Result<TrustlineReflection, OrganOpError> {
        let cell = world
            .ledger()
            .get(&organ)
            .ok_or(OrganOpError::NotFound { cell: organ })?;
        TrustlineReflection::from_cell(&organ, cell).ok_or(OrganOpError::PreCheck {
            op: OrganOp::Draw,
            reason: "cell is not a trustline organ".into(),
        })
    }

    /// Reflect a flash-well organ's live position. Errors if absent / not a well.
    pub fn reflect_flash_well(
        &self,
        world: &World,
        organ: CellId,
    ) -> Result<FlashWellReflection, OrganOpError> {
        let cell = world
            .ledger()
            .get(&organ)
            .ok_or(OrganOpError::NotFound { cell: organ })?;
        FlashWellReflection::from_cell(&organ, cell).ok_or(OrganOpError::PreCheck {
            op: OrganOp::Draw,
            reason: "cell is not a flash-well organ".into(),
        })
    }

    // ── the one commit seam ──────────────────────────────────────────────────

    /// Commit one organ-op turn through the REAL executor, mapping the outcome to
    /// [`OrganOpOutcome`] / [`OrganOpError::ExecutorRejected`]. EVERY verb routes
    /// here — the single seam where the program gate fires.
    fn commit(
        &self,
        world: &mut World,
        op: OrganOp,
        cell: CellId,
        turn: dregg_turn::turn::Turn,
        summarize: impl FnOnce(&OrganOpOutcome) -> String,
    ) -> Result<OrganOpOutcome, OrganOpError> {
        match world.commit_turn(turn) {
            CommitOutcome::Committed { ref receipt, .. } => {
                let mut outcome = OrganOpOutcome {
                    op,
                    cell,
                    receipt_hash: receipt.receipt_hash(),
                    height: world.height(),
                    computrons: receipt.computrons_used,
                    summary: String::new(),
                };
                outcome.summary = summarize(&outcome);
                Ok(outcome)
            }
            CommitOutcome::Rejected { reason, .. } => {
                Err(OrganOpError::ExecutorRejected { op, reason })
            }
            CommitOutcome::Queued { .. } => Err(OrganOpError::ExecutorRejected {
                op,
                reason: "world suspended: turn queued, not committed".to_string(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A world with an issuer/operator cell holding a big balance and a holder
    /// cell. The organ-ops driver opens organs against these.
    fn world_with_parties() -> (World, CellId, CellId) {
        let mut world = World::new();
        let issuer = world.genesis_cell(0xC0, 1_000_000);
        let holder = world.genesis_cell(0xB0, 1_000_000);
        (world, issuer, holder)
    }

    // ── TRUSTLINE: open / draw / repay / settle / close as REAL turns ────────

    #[test]
    fn open_trustline_drives_a_real_turn_and_reflects_open() {
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let issuer_before = world.ledger().get(&issuer).unwrap().state.balance();
        let (organ, outcome) = d
            .open_trustline(&mut world, 0x71, issuer, holder, 100)
            .expect("open must commit through the real executor");
        assert_eq!(outcome.op, OrganOp::Open);
        // The organ reflects OPEN with the right line.
        let r = d.reflect_trustline(&world, organ).expect("reflects");
        assert!(r.open, "the trustline is OPEN");
        assert_eq!(r.line, 100);
        assert_eq!(r.drawn, 0);
        assert_eq!(r.escrow, 100, "the full line is escrowed (funded birth)");
        // Conservation: the issuer was REALLY debited the line.
        assert_eq!(
            world.ledger().get(&issuer).unwrap().state.balance(),
            issuer_before - 100
        );
    }

    #[test]
    fn draw_within_the_line_commits_and_moves_the_drawn_counter() {
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (organ, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        let o = d.draw_trustline(&mut world, organ, 40).expect("a draw within the line commits");
        assert_eq!(o.op, OrganOp::Draw);
        let r = d.reflect_trustline(&world, organ).unwrap();
        assert_eq!(r.drawn, 40, "the drawn counter moved");
        assert_eq!(r.remaining, 60, "remaining = line − drawn");
    }

    #[test]
    fn an_over_line_draw_is_refused_by_the_executors_program_gate_not_faked() {
        // THE LOAD-BEARING TOOTH: draw past the line. We bypass the pre-check by
        // first drawing to the line, then attempting one more unit DIRECTLY as a
        // SetField(drawn := line+1) turn — the program's `FieldLteField(drawn ≤
        // ceiling)` tooth must REJECT it IN-PROTOCOL.
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (organ, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        // Draw the whole line legitimately.
        d.draw_trustline(&mut world, organ, 100).expect("drawing exactly the line is fine");
        assert_eq!(d.reflect_trustline(&world, organ).unwrap().drawn, 100);
        let h_before = world.height();
        // Now attempt drawn := 101 DIRECTLY (the driver's pre-check would catch
        // it, so we forge the raw turn to prove the EXECUTOR refuses it).
        let over = world.turn(
            organ,
            vec![world::set_field(organ, TL_DRAWN_SLOT as usize, field_from_u64(101))],
        );
        let outcome = world.commit_turn(over);
        assert!(
            !outcome.is_committed(),
            "an over-line draw must be REFUSED by the installed trustline program"
        );
        // Fail-closed: no commit, drawn unchanged, height unmoved.
        assert_eq!(world.height(), h_before, "the refused over-line draw did not commit");
        assert_eq!(d.reflect_trustline(&world, organ).unwrap().drawn, 100, "drawn held at the line");
    }

    #[test]
    fn draw_then_repay_round_trips_the_line() {
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (organ, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        d.draw_trustline(&mut world, organ, 70).unwrap();
        d.repay_trustline(&mut world, organ, 30).expect("a repay within outstanding commits");
        let r = d.reflect_trustline(&world, organ).unwrap();
        assert_eq!(r.drawn, 40, "drawn restored by the repay (70 − 30)");
        assert_eq!(r.remaining, 60);
    }

    #[test]
    fn settle_redeems_the_outstanding_draw_to_the_holder_and_conserves() {
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (organ, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        d.draw_trustline(&mut world, organ, 60).unwrap();
        let holder_before = world.ledger().get(&holder).unwrap().state.balance();
        let escrow_before = world.ledger().get(&organ).unwrap().state.balance();
        let o = d.settle_trustline(&mut world, organ).expect("settle commits");
        assert_eq!(o.op, OrganOp::Settle);
        let r = d.reflect_trustline(&world, organ).unwrap();
        assert_eq!(r.settled, 60, "settled := drawn");
        assert_eq!(r.outstanding, 0, "nothing outstanding after settle");
        // The holder received the outstanding amount; the escrow shrank by it
        // (conservation — the hard move).
        assert_eq!(world.ledger().get(&holder).unwrap().state.balance(), holder_before + 60);
        assert_eq!(world.ledger().get(&organ).unwrap().state.balance(), escrow_before - 60);
    }

    #[test]
    fn close_returns_the_residual_and_makes_the_cell_inert() {
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (organ, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        d.draw_trustline(&mut world, organ, 40).unwrap();
        let issuer_before = world.ledger().get(&issuer).unwrap().state.balance();
        let holder_before = world.ledger().get(&holder).unwrap().state.balance();
        let o = d.close_trustline(&mut world, organ).expect("close commits");
        assert_eq!(o.op, OrganOp::Close);
        let r = d.reflect_trustline(&world, organ).unwrap();
        assert!(r.closed, "the line is CLOSED");
        // The outstanding 40 went to the holder; the residual 60 returned to the
        // issuer (escrow was 100). Total conserved.
        assert_eq!(world.ledger().get(&holder).unwrap().state.balance(), holder_before + 40);
        assert_eq!(world.ledger().get(&issuer).unwrap().state.balance(), issuer_before + 60);
        // INERT: a draw on the closed line is refused by the lifecycle table.
        let h_before = world.height();
        let r2 = d.draw_trustline(&mut world, organ, 1);
        assert!(r2.is_err(), "a draw on a CLOSED line must be refused");
        assert_eq!(world.height(), h_before, "no turn committed on the closed organ");
    }

    // ── FLASH WELL: open / borrow / close as REAL turns ──────────────────────

    #[test]
    fn open_flash_well_drives_a_real_turn_and_reflects_open() {
        let (mut world, funder, _holder) = world_with_parties();
        let d = OrganDriver::new();
        let (well, outcome) = d
            .open_flash_well(&mut world, 0x72, funder, 1_000, 5, 4)
            .expect("open well must commit");
        assert_eq!(outcome.op, OrganOp::Open);
        let r = d.reflect_flash_well(&world, well).expect("reflects");
        assert!(r.open, "the well is OPEN");
        assert_eq!(r.principal, 1_000);
        assert_eq!(r.fee, 5);
        assert_eq!(r.ratchet, 5, "primed at rung 1 (the priming quantum = fee)");
        assert_eq!(r.balance, 1_000, "funded with the principal");
    }

    #[test]
    fn borrow_climbs_the_ratchet_and_accrues_the_fee_a_real_ring() {
        let (mut world, funder, borrower) = world_with_parties();
        let d = OrganDriver::new();
        let (well, _) = d
            .open_flash_well(&mut world, 0x72, funder, 1_000, 5, 4)
            .unwrap();
        let borrower_before = world.ledger().get(&borrower).unwrap().state.balance();
        let o = d.borrow_flash_well(&mut world, well, borrower, 600).expect("a borrow ring commits");
        assert_eq!(o.op, OrganOp::Draw);
        let r = d.reflect_flash_well(&world, well).unwrap();
        assert_eq!(r.ratchet, 10, "the ratchet climbed one rung (5 → 10)");
        assert_eq!(r.accrued_fees, 5, "accrued = ratchet − fee = 10 − 5");
        assert_eq!(r.balance, 1_005, "the well accrued the fee (principal + fee)");
        // The borrower paid the fee net (drew 600, repaid 605).
        assert_eq!(world.ledger().get(&borrower).unwrap().state.balance(), borrower_before - 5);
    }

    #[test]
    fn a_borrow_that_would_not_climb_the_ratchet_is_refused_by_the_program() {
        // THE FEE-EVASION TOOTH: forge an OTHERWISE-VALID well-touching ring (draw
        // + repay, fully cap-authorized) that does NOT climb the ratchet — the
        // ONLY missing leg is the ratchet climb, so the `StrictMonotonic(ratchet)`
        // tooth (every OPEN-ending touch must climb ≥1 rung) is exactly what must
        // REJECT it IN-PROTOCOL. We grant the borrower the well-cap first (as a
        // real borrow does) to isolate the ratchet tooth from the cap gate.
        let (mut world, funder, borrower) = world_with_parties();
        let d = OrganDriver::new();
        let (well, _) = d
            .open_flash_well(&mut world, 0x72, funder, 1_000, 5, 4)
            .unwrap();
        // The borrower reaches the well (the adopt-grant — so the cross-cell draw
        // is cap-authorized and the ONLY thing missing is the ratchet climb).
        world.genesis_grant_cap(&borrower, well);
        let h_before = world.height();
        let ratchet_before = d.reflect_flash_well(&world, well).unwrap().ratchet;
        // A draw + repay, BORROWER-signed, well-touching, but leaving the ratchet
        // UNCHANGED (no SetField on the ratchet). The draw and repay alone are
        // valid; only the strict-climb tooth is violated.
        let evade = world.turn(
            borrower,
            vec![
                world::transfer(well, borrower, 100),
                world::transfer(borrower, well, 105),
                // (deliberately NO ratchet climb — the fee-evasion attempt)
            ],
        );
        let outcome = world.commit_turn(evade);
        assert!(
            !outcome.is_committed(),
            "a well-touch that does not climb the ratchet must be REFUSED (StrictMonotonic)"
        );
        // The refusal is the PROGRAM's (a constraint violation), not a cap/balance
        // error — the borrower reaches the well and holds the funds, so the ONLY
        // thing wrong is the missing ratchet climb.
        if let crate::world::CommitOutcome::Rejected { reason, .. } = outcome {
            assert!(
                !reason.contains("CapabilityNotHeld") && !reason.contains("InsufficientBalance"),
                "the refusal must be the ratchet program tooth, not a cap/balance gate; got: {reason}"
            );
        }
        assert_eq!(world.height(), h_before, "the fee-evading touch did not commit");
        assert_eq!(
            d.reflect_flash_well(&world, well).unwrap().ratchet,
            ratchet_before,
            "the ratchet held"
        );
    }

    #[test]
    fn close_flash_well_sweeps_the_balance_and_makes_the_cell_inert() {
        let (mut world, funder, borrower) = world_with_parties();
        let d = OrganDriver::new();
        let (well, _) = d
            .open_flash_well(&mut world, 0x72, funder, 1_000, 5, 4)
            .unwrap();
        // One borrow so there's an accrued fee in the sweep.
        d.borrow_flash_well(&mut world, well, borrower, 200).unwrap();
        let sweep_to = funder;
        let funder_before = world.ledger().get(&sweep_to).unwrap().state.balance();
        let well_balance = world.ledger().get(&well).unwrap().state.balance();
        let o = d.close_flash_well(&mut world, well, sweep_to).expect("close+sweep commits");
        assert_eq!(o.op, OrganOp::Close);
        let r = d.reflect_flash_well(&world, well).unwrap();
        assert!(r.closed, "the well is CLOSED");
        // The whole balance was swept to the sweep target (conservation).
        assert_eq!(
            world.ledger().get(&sweep_to).unwrap().state.balance(),
            funder_before + well_balance
        );
        // INERT: a borrow on the closed well is refused.
        let h_before = world.height();
        assert!(d.borrow_flash_well(&mut world, well, borrower, 1).is_err());
        assert_eq!(world.height(), h_before, "no turn committed on the closed well");
    }

    #[test]
    fn an_open_then_a_closed_organ_survey_reflects_the_driven_state() {
        // The driver's verbs change LIVE organ state the ORGANS panel reflects:
        // open two organs, drive them, and confirm OrganSurvey sees the result.
        let (mut world, issuer, holder) = world_with_parties();
        let d = OrganDriver::new();
        let (tl, _) = d.open_trustline(&mut world, 0x71, issuer, holder, 100).unwrap();
        d.draw_trustline(&mut world, tl, 30).unwrap();
        let (_well, _) = d.open_flash_well(&mut world, 0x72, issuer, 1_000, 5, 4).unwrap();

        let survey = crate::organs::OrganSurvey::build(&world);
        assert_eq!(survey.trustlines.len(), 1, "the driven trustline is in the survey");
        assert_eq!(survey.trustlines[0].drawn, 30, "the survey reflects the driven draw");
        assert_eq!(survey.flash_wells.len(), 1, "the driven flash well is in the survey");
        assert!(survey.flash_wells[0].open);
    }
}
