//! # The protocol-native run-credit rail — a dungeon RUN charged as a CONSERVED transfer.
//!
//! A RUN starts at `POST /session/start` (the run boundary — NOT each move; a move is a
//! free executor turn). On the [`RunSettlementMode::ProtocolNative`] rail, starting a run
//! debits **exactly one** run-credit from the player cell via
//! [`dregg_pay::RunBudgetLedger::charge_run`] — the one verified desugar to a single
//! conserving `Effect::Transfer` the player authorizes (per-asset Σδ=0, kernel-checked).
//! No operator custody key and no deposit sweep are reachable from this path (that is
//! `dregg-pay`'s rung-2a falsifier: grep this module for the custodial types and find
//! nothing). On an empty budget the charge **fails closed**: nothing moves, and the run
//! does not start (no deploy, no narration).
//!
//! The [`RunSettlementMode::Custodial`] rail is the existing free/mock demo path — no
//! protocol-native charge. It is kept ADDITIVE and config-selected, so the devnet demo
//! runs the no-custody loop with zero real money and zero custody key, while the free
//! path (and every existing test) stays exactly as it was.
//!
//! Selected by operator env:
//! * `REAL_DUNGEON_SETTLEMENT=protocol-native` → the conserved run-credit rail.
//!   (Anything else / unset → the free custodial-mock rail, the unchanged default.)
//! * `REAL_DUNGEON_RUN_BUDGET=N` → the player's starting run-credit budget (default 3).

use std::collections::HashMap;

use dregg_pay::{
    CellId, ChargeError, DEFAULT_RUN_PRICE_CREDITS, InvokeAuthority, RunBudgetLedger, RunReceipt,
    RunSettlementMode,
};

/// The demo player cell that authorizes the run charge — a fixed, distinct 32-byte id.
/// This is a devnet demo cell (no real key material); the charge is a real conserving
/// transfer in the run-credit read-model, carrying zero bridged value.
pub fn demo_player_cell() -> CellId {
    CellId::from_bytes([0x11; 32])
}

/// The demo operator cell a run-credit transfers TO (devnet demo).
pub fn demo_operator_cell() -> CellId {
    CellId::from_bytes([0x22; 32])
}

/// The service's run-credit rail: the settlement mode, the run-budget ledger (a
/// read-model of conserved balances in ONE internal run-credit asset), the player +
/// operator cells, and the run price. Its only mutation is [`Self::charge_one_run`],
/// which applies a single conserving transfer.
pub struct RunCreditRail {
    mode: RunSettlementMode,
    ledger: RunBudgetLedger,
    player: CellId,
    operator: CellId,
    price: u64,
    /// The run receipts settled this process (audit trail; each carries the conserving
    /// transfer action the player authorized).
    receipts: Vec<RunReceipt>,
}

/// The outcome of charging one dungeon run at the run boundary.
pub enum ChargeOutcome {
    /// Custodial/mock rail: no protocol-native charge (the existing free demo path).
    Skipped,
    /// Protocol-native: exactly one run-credit debited as a conserving transfer. The
    /// receipt carries the single `Effect::Transfer` from the player cell.
    Charged(RunReceipt),
    /// Fail-closed: the charge was refused (empty budget / unauthorized). Nothing moved,
    /// so the run must NOT start.
    Refused(ChargeError),
}

impl RunCreditRail {
    /// The protocol-native rail: a run-budget ledger holding the player's starting
    /// budget in the internal run-credit asset. Balances only ever move by conserving
    /// transfer thereafter (there is no mint and no set-balance authority).
    pub fn protocol_native(player_budget: u64) -> Self {
        let player = demo_player_cell();
        let operator = demo_operator_cell();
        let mut balances = HashMap::new();
        balances.insert(player, player_budget);
        RunCreditRail {
            mode: RunSettlementMode::ProtocolNative,
            ledger: RunBudgetLedger::run_credits(balances),
            player,
            operator,
            price: DEFAULT_RUN_PRICE_CREDITS,
            receipts: Vec::new(),
        }
    }

    /// The custodial/mock rail: the existing free demo path — no protocol-native charge.
    /// The default so every existing route (and test) behaves exactly as before.
    pub fn custodial() -> Self {
        RunCreditRail {
            mode: RunSettlementMode::Custodial,
            ledger: RunBudgetLedger::run_credits(HashMap::new()),
            player: demo_player_cell(),
            operator: demo_operator_cell(),
            price: DEFAULT_RUN_PRICE_CREDITS,
            receipts: Vec::new(),
        }
    }

    /// Build the rail from the operator environment. Defaults to the free custodial rail
    /// so the demo's existing behavior is unchanged unless the operator opts into the
    /// protocol-native no-custody loop.
    pub fn from_env() -> Self {
        let native = matches!(
            std::env::var("REAL_DUNGEON_SETTLEMENT").as_deref(),
            Ok("protocol-native") | Ok("protocol_native") | Ok("native")
        );
        if native {
            let budget = std::env::var("REAL_DUNGEON_RUN_BUDGET")
                .ok()
                .and_then(|v| v.trim().parse::<u64>().ok())
                .unwrap_or(3);
            RunCreditRail::protocol_native(budget)
        } else {
            RunCreditRail::custodial()
        }
    }

    /// `true` on the conserved-transfer rail.
    pub fn is_protocol_native(&self) -> bool {
        self.mode == RunSettlementMode::ProtocolNative
    }

    /// The player cell that authorizes the run charge.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn player(&self) -> CellId {
        self.player
    }

    /// The operator cell a run-credit transfers to.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn operator(&self) -> CellId {
        self.operator
    }

    /// The player's current run-credit balance.
    pub fn balance(&self) -> u64 {
        self.ledger.balance(&self.player)
    }

    /// The operator's accrued run-credit balance.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn operator_balance(&self) -> u64 {
        self.ledger.balance(&self.operator)
    }

    /// The per-asset conserved total across all cells. A correct charge leaves this
    /// **unchanged** (Σδ = 0); a refused charge leaves it unchanged too.
    pub fn total(&self) -> u128 {
        self.ledger.total()
    }

    /// How many runs this rail has settled (each with a conserving-transfer receipt).
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn charges(&self) -> usize {
        self.receipts.len()
    }

    /// **Charge one dungeon run at the run boundary.**
    ///
    /// On the protocol-native rail this debits exactly one run-credit from the player
    /// cell as a single conserving `Effect::Transfer` ([`RunBudgetLedger::charge_run`]),
    /// authorized by the player's `Signature`. Fail-closed: an empty (or insufficient)
    /// budget refuses and moves nothing — the caller must NOT start the run. On the
    /// custodial rail this is a no-op ([`ChargeOutcome::Skipped`]) — the free demo path.
    pub fn charge_one_run(&mut self) -> ChargeOutcome {
        if self.mode == RunSettlementMode::Custodial {
            return ChargeOutcome::Skipped;
        }
        match self.ledger.charge_run(
            self.player,
            self.operator,
            self.price,
            InvokeAuthority::Signature,
        ) {
            Ok(receipt) => {
                self.receipts.push(receipt.clone());
                ChargeOutcome::Charged(receipt)
            }
            Err(e) => ChargeOutcome::Refused(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A funded protocol-native run debits exactly one credit as a conserving transfer:
    /// the per-asset total is unchanged, the player loses one, the operator gains one.
    #[test]
    fn charge_debits_one_conserving_credit() {
        let mut rail = RunCreditRail::protocol_native(3);
        let total_before = rail.total();
        match rail.charge_one_run() {
            ChargeOutcome::Charged(receipt) => {
                assert_eq!(receipt.debited, 1);
                assert_eq!(receipt.remaining, 2);
                let (from, to, amount) = receipt.transfer().expect("one conserving transfer");
                assert_eq!(from, rail.player());
                assert_eq!(to, rail.operator());
                assert_eq!(amount, 1);
            }
            _ => panic!("a funded budget must settle one run"),
        }
        assert_eq!(
            rail.total(),
            total_before,
            "per-asset Σδ=0 across the charge"
        );
        assert_eq!(rail.balance(), 2);
        assert_eq!(rail.operator_balance(), 1);
        assert_eq!(rail.charges(), 1);
    }

    /// An empty budget refuses the run fail-closed and moves nothing.
    #[test]
    fn empty_budget_refuses_and_moves_nothing() {
        let mut rail = RunCreditRail::protocol_native(0);
        let total_before = rail.total();
        assert!(matches!(rail.charge_one_run(), ChargeOutcome::Refused(_)));
        assert_eq!(rail.total(), total_before, "a refused run moves nothing");
        assert_eq!(rail.balance(), 0);
        assert_eq!(rail.operator_balance(), 0);
        assert_eq!(rail.charges(), 0);
    }

    /// The custodial rail never charges (the free demo path).
    #[test]
    fn custodial_rail_skips_the_charge() {
        let mut rail = RunCreditRail::custodial();
        assert!(matches!(rail.charge_one_run(), ChargeOutcome::Skipped));
        assert_eq!(rail.charges(), 0);
    }
}
