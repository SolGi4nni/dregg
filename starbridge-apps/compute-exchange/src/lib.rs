//! # Compute marketplace (Starbridge organ-composition app)
//!
//! A requester needs a unit of work done; a provider has spare compute. They
//! transact a job neither trusts the other over. The requester **posts a job**
//! with a promised **budget**; a provider **bids** a price (which must fit the
//! budget); the job **settles atomically** — the accepted price is PAID to the
//! provider by a real conserving `Effect::Transfer` in the same turn as the
//! `STATE = SETTLED` advance. No escrow-agent, no off-chain coordinator: the job
//! is a single factory-born cell whose installed `CellProgram` IS the rules,
//! re-checked by the verified executor on every turn that touches it.
//!
//! This app exists to show the system is **not a toy**: it composes — in one
//! cell's slot-caveat program — the guarantees of four of the night's organs.
//!
//! | Organ      | Guarantee                                | How this cell enforces it |
//! |------------|------------------------------------------|---------------------------|
//! | BUDGET     | the bid can never exceed the budget      | `FieldLteField { BID <= BUDGET }` — the accepted price is a bounded draw (the AffineLe budget gate) |
//! | ACCEPTED   | the accepted price, bound exactly once   | `WriteOnce(BID)` — the requester accepts a price once; tamper-evident |
//! | FLASHWELL  | atomic, conserving settlement            | `AffineEq { PAID + REFUNDED - BUDGET = 0 }` (settle) + the universal no-mint `AffineLe` — the RECORD splits the budget with no mint/burn |
//! | LIFECYCLE  | one-way, no replay, no double-settle      | `StrictMonotonic(STATE)` — `POSTED->BID->SETTLED` |
//!
//! ## ⚑ A SETTLEMENT MOVES VALUE, and the budget is a PROMISE, not an escrow
//!
//! Until 2026-07-28 every settle builder here was `SetField` + `EmitEvent` and
//! carried no [`Effect::Transfer`] at all. A job rendered a green `SETTLED` pill
//! and a live `paid ·` amount, emitted `job-settled`, advanced `STATE`, and moved
//! **no balance anywhere**. The provider held a receipt for a payment that never
//! happened, which is worse than a failure because the next reader trusts it.
//!
//! The four organ caveats were all true and all about the RECORD: an `AffineEq`
//! over `PAID + REFUNDED - BUDGET` relates three FIELD SLOTS, and three numbers
//! agreeing is not money moving.
//!
//! [`build_settle_actions`] now carries the conserving kernel [`Effect::Transfer`]
//! — produced by the shared `Payable` desugar
//! ([`dregg_app_framework::pay_effects`], the one every `Payable` app pays through
//! — in the SAME TURN as the `STATE = SETTLED` advance. They are roots of one call
//! forest, so they commit or roll back together: **there is no accepted turn in
//! which the job reads SETTLED and the provider was not paid the accepted bid.** A
//! requester who cannot cover the bid is a `TurnError::InsufficientBalance`
//! refusal that takes the SETTLED stamp down with it.
//!
//! ### ⚠ The budget is NOT held in escrow, and this crate no longer says it is
//!
//! The requester pays at settle time, out of its own balance. The job cell CANNOT
//! hold the budget, and the reason is its own program. Measured on this crate's
//! own factory-born cell, three ways, all refused:
//!
//!   1. one action targeting the REQUESTER, carrying `Transfer(requester -> job)`
//!      plus the post `SetField`s on the job — `permission denied on cell <job>
//!      for action 'SetState': requires Signature` (a cross-cell `SetField` needs
//!      the destination's `set_state` to be [`AuthRequired::None`]);
//!   2. one action targeting the JOB, carrying `Transfer(requester -> job)` —
//!      `permission denied on cell <requester> for action 'Send': requires
//!      Signature` (`apply_transfer` skips its cross-cell `Send` check only when
//!      the transfer's `from` IS the action target);
//!   3. two actions in ONE turn (fund, then post) — `program violation on cell
//!      <job>: field[9] did not strictly increase; StrictMonotonic requires new >
//!      old`. The executor evaluates a touched cell's `CellProgram` per ACTION
//!      over every cell any effect touches, INCLUDING a `Transfer` destination, so
//!      `StrictMonotonic(STATE)` demands that any action crediting the job cell
//!      also strictly advance its `STATE`.
//!
//! Those rules have no common solution, so a self-escrowing job cell is not
//! expressible, and pretending otherwise would be a second false label rather than
//! a fix.
//!
//! What that costs, stated plainly: between `post` and `settle` nothing stops the
//! requester spending the money, so a provider is protected against a settlement
//! that LIES, not against a requester who goes broke. Real escrow needs a separate
//! holding cell with no `StrictMonotonic` on it — which is a design fork (who
//! mints it, who holds its cap, what happens to an abandoned job) rather than
//! wiring.
//!
//! And `REFUNDED` is the part of the budget **never drawn**, not a return: it never
//! left the requester, so no refund transfer exists or could exist.
//!
//! Built from dregg primitives only: `FactoryDescriptor`, `Effect::SetField` /
//! `Effect::EmitEvent` / `Effect::Transfer`, `Authorization::Signature` from
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
//!   description), `STATE = POSTED`. Nothing moves: the budget is a ceiling the
//!   requester promises, and [`build_settle_actions`] is what pays.
//! - **bid**    — a provider bids `price <= BUDGET` into `BID`, binds
//!   `PROVIDER_HASH`, `STATE -> BID`.
//! - **settle** — the deal closes: the provider is PAID `PAID` out of the
//!   requester's balance, the record reads `PAID + REFUNDED == BUDGET`, and
//!   `STATE -> SETTLED`. Provider paid in full ⇒ `PAID == BID,
//!   REFUNDED == BUDGET - BID` (the undrawn remainder, which never left the
//!   requester).
//!
//! ## The shared compute FUND ([`ComputeFundVault`]) — the pooled-deposit headline
//!
//! A single requester promises a single job's budget above and pays it at settle
//! out of its own balance. The *fund* is the pooled face, and the one place in
//! this crate where value is genuinely HELD: many sponsors pool a common budget
//! asset into ONE vault (a real custody cell, credited on deposit) and each
//! holds **shares** proportional to its contribution, redeemable for its
//! proportional slice of the pool at any time. The fund IS the protocol-proven
//! [`ShareVault`](dregg_cell::vault) house-capacity — a real *witnessed*
//! committed-counter vault, not hand-rolled slot arithmetic. A deposit of `d`
//! assets mints `d · total_shares / total_assets` shares (the ERC-4626
//! share-price relation; `d` shares on the empty bootstrap), and a withdrawal of
//! `s` shares redeems `s · total_assets / total_shares` assets. Its soundness is
//! the no-dilution keystone (`Vault.deposit_no_dilution`,
//! `metatheory/Dregg2/Deos/Vault.lean`): a deposit can NEVER decrease an existing
//! holder's price-per-share, and the classic ERC-4626 first-depositor
//! **inflation attack** is structurally defeated — the committed `total_assets`
//! is an internal counter no raw donation can skew (donation immunity), and a
//! positive deposit that would mint ZERO shares is REFUSED (the zero-mint tooth).
//!
//! What [`ComputeFundVault`] genuinely does — each proven in `tests/compute_fund.rs`:
//!   1. **Proportional shares** — two sponsors deposit into one fund; shares are
//!      minted by the committed share-price relation, value held in custody.
//!   2. **No dilution** — a later deposit never decreases an earlier holder's
//!      price-per-share; a withdrawal redeems the redeemer's fair slice and no
//!      more (the remaining holders are not diluted).
//!   3. **Conservation** — pooled value moves sponsor↔custody, never created.
//!   4. **The inflation attack defeated** — a raw donation cannot skew the share
//!      ratio (the committed counter is internal), and a zero-mint deposit is
//!      refused by the capacity.

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, pay_effects, symbol,
};

/// The deos-view CARD: the app's UI as a renderer-independent `deos.ui.*` view-tree.
pub mod card;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// method dispatch over the compute-job lifecycle.
pub mod service;

// =============================================================================
// THE SHARED COMPUTE FUND — the proven `ShareVault` capacity, as a pooled fund.
// =============================================================================

use dregg_cell::Cell;
use dregg_cell::vault::{
    ShareVaultError, ShareVaultState, deposit_shares, is_share_vault, open_share_vault,
    withdraw_shares,
};
use std::collections::HashMap;

/// The public key of the fund custodian cells (the vault host + its budget custody
/// wallet). A fixed sentinel — the custodian holds the pooled value only and is
/// never a sponsor with a share claim of its own.
pub const FUND_CUSTODIAN_PK: [u8; 32] = *b"starbridge-compute-fund-custody!";
/// The vault host cell's token id (it carries no balance of its own — it hosts the
/// committed `(total_assets, total_shares)` share-vault counters in its heap).
pub const FUND_VAULT_TOKEN: [u8; 32] = *b"starbridge-compute-fund-vault!!!";
/// The pooled budget asset's token id (the custody wallet and every sponsor wallet
/// hold THIS asset — the fungible value the fund pools).
pub const FUND_BUDGET_TOKEN: [u8; 32] = *b"starbridge-compute-fund-budget!!";

/// Why a [`ComputeFundVault`] operation could not complete.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FundError {
    /// The share-vault capacity refused (non-positive amount, a forged share
    /// count, a zero-mint inflation-attack deposit, insufficient supply, …) — the
    /// forge/inflation-rejecting protocol check bit.
    Vault(ShareVaultError),
    /// The depositing sponsor wallet cannot cover the deposit.
    InsufficientFunds {
        /// The wallet's balance.
        have: i64,
        /// The deposit it must cover.
        need: i64,
    },
    /// The sponsor wallet's asset is not the fund's pooled budget asset.
    AssetMismatch,
    /// The sponsor asked to redeem more shares than it holds in this fund.
    InsufficientShares {
        /// The shares the sponsor holds.
        have: i64,
        /// The shares it asked to redeem.
        want: i64,
    },
}

impl std::fmt::Display for FundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FundError::Vault(e) => write!(f, "share-vault refused: {e}"),
            FundError::InsufficientFunds { have, need } => {
                write!(f, "insufficient funds: have {have}, need {need}")
            }
            FundError::AssetMismatch => write!(f, "wallet asset is not the fund's budget asset"),
            FundError::InsufficientShares { have, want } => {
                write!(f, "insufficient shares: hold {have}, want to redeem {want}")
            }
        }
    }
}

impl std::error::Error for FundError {}

impl From<ShareVaultError> for FundError {
    fn from(e: ShareVaultError) -> Self {
        FundError::Vault(e)
    }
}

/// Debit `amount` (`> 0`) from `from`, credit it to `to`. Returns `false` if
/// `from` cannot cover it (no value is created or destroyed). The role the app
/// plays around the vault's *authorization* — the capacity decides *how many
/// shares* a deposit mints (or *how much value* a redemption draws); the value
/// move itself is an ordinary conserving transfer.
///
/// ⚠ **Read this at its real resolution.** Value genuinely moves here — these are
/// balance writes on real [`Cell`]s and `tests/compute_fund.rs` asserts the
/// per-asset total across wallets plus custody — but it moves **in this process,
/// not on the ledger**. There is no [`Effect::Transfer`], no signed action, no
/// turn and no receipt, so nothing a light client witnesses. That is a weaker
/// claim than the job lifecycle's settlement, which routes its value leg through
/// the verified executor, and the difference is not cosmetic. Routing the fund
/// through turns is real work, named here rather than implied.
pub fn move_value(from: &mut Cell, to: &mut Cell, amount: i64) -> bool {
    if amount <= 0 {
        return false;
    }
    let amt = amount as u64;
    if !from.state.debit_balance(amt) {
        return false;
    }
    assert!(
        to.state.credit_balance(amt),
        "credit must succeed after debit"
    );
    true
}

/// **A shared compute fund, as a self-contained conserving share vault.**
///
/// Owns the vault host cell (whose committed heap binds `total_assets` and
/// `total_shares` — the proven [`ShareVault`](dregg_cell::vault) counters) plus a
/// custody cell holding the pooled budget value. Many sponsors
/// [`deposit`](Self::deposit) a common budget asset and receive **shares** minted
/// by the committed share-price relation; a sponsor [`withdraw`](Self::withdraw)s
/// by redeeming its shares for the proportional value. The vault commits only the
/// TOTAL supply; the fund tracks which sponsor owns which slice. Value is
/// conserved per asset at every step, and the no-dilution / inflation-attack teeth
/// are the capacity's, imaged by `metatheory/Dregg2/Deos/Vault.lean`.
#[derive(Clone, Debug)]
pub struct ComputeFundVault {
    /// The vault host cell — its committed heap binds `(total_assets,
    /// total_shares)`; a light client witnesses every counter move.
    pub vault: Cell,
    /// Custody of the pooled budget value (held while shares are outstanding).
    custody: Cell,
    /// Per-sponsor share holdings. The vault commits only the total supply; this
    /// maps each sponsor's wallet cell to the share slice it owns of the pool.
    shares: HashMap<CellId, i64>,
}

impl ComputeFundVault {
    /// **Open** a fresh fund: born a vault host cell with empty committed counters
    /// (`total_assets = total_shares = 0` via [`open_share_vault`]) and an empty
    /// budget custody cell. The first deposit bootstraps shares 1:1.
    pub fn open() -> Self {
        let mut vault = Cell::with_balance(FUND_CUSTODIAN_PK, FUND_VAULT_TOKEN, 0);
        open_share_vault(&mut vault);
        ComputeFundVault {
            vault,
            custody: Cell::with_balance(FUND_CUSTODIAN_PK, FUND_BUDGET_TOKEN, 0),
            shares: HashMap::new(),
        }
    }

    /// **Deposit** `amount` budget from a sponsor's wallet, minting proportional
    /// shares. The committed share-price relation (the proven [`ShareVaultState`])
    /// decides the minted count: `d · S / T` on an established fund, `d` 1:1 on the
    /// bootstrap. The capacity's forge/inflation gate runs FIRST: a non-positive
    /// deposit, a positive deposit that would mint ZERO shares (the ERC-4626
    /// first-depositor inflation attack), or a forged claimed count is refused with
    /// nothing moved. On success value LEAVES the sponsor's wallet into custody
    /// (conservation: in transit, never created) and the minted shares are credited
    /// to the sponsor. Returns the minted share count.
    pub fn deposit(&mut self, sponsor: &mut Cell, amount: i64) -> Result<i64, FundError> {
        if sponsor.asset() != self.custody.asset() {
            return Err(FundError::AssetMismatch);
        }
        if sponsor.state.balance() < amount {
            return Err(FundError::InsufficientFunds {
                have: sponsor.state.balance(),
                need: amount,
            });
        }
        let sponsor_id = sponsor.id();
        // The committed counters decide the fair minted count (the share-price
        // relation); the capacity re-checks it and refuses a zero-mint/forge.
        let st = ShareVaultState::read(&self.vault)?;
        let claimed = st.shares_for_deposit(amount);
        let minted = deposit_shares(&mut self.vault, amount, claimed)?;
        assert!(
            move_value(sponsor, &mut self.custody, amount),
            "the funds check above guarantees the move succeeds"
        );
        *self.shares.entry(sponsor_id).or_insert(0) += minted;
        Ok(minted)
    }

    /// **Withdraw** by redeeming `shares` the sponsor holds, returning the
    /// proportional value. The committed share-price relation decides the redeemed
    /// assets (`s · T / S`); the capacity refuses a non-positive/forged/over-supply
    /// redemption. The sponsor may never redeem more shares than it holds in this
    /// fund. On success the redeemed value LEAVES custody back to the sponsor and
    /// its share slice is debited. Returns the redeemed asset count.
    pub fn withdraw(&mut self, sponsor: &mut Cell, shares: i64) -> Result<i64, FundError> {
        if sponsor.asset() != self.custody.asset() {
            return Err(FundError::AssetMismatch);
        }
        let sponsor_id = sponsor.id();
        let held = self.shares.get(&sponsor_id).copied().unwrap_or(0);
        if shares <= 0 || held < shares {
            return Err(FundError::InsufficientShares {
                have: held,
                want: shares,
            });
        }
        let st = ShareVaultState::read(&self.vault)?;
        let claimed = st.assets_for_withdraw(shares);
        let redeemed = withdraw_shares(&mut self.vault, shares, claimed)?;
        assert!(
            move_value(&mut self.custody, sponsor, redeemed),
            "custody holds the pooled value backing every share"
        );
        let remaining = held - shares;
        if remaining == 0 {
            self.shares.remove(&sponsor_id);
        } else {
            self.shares.insert(sponsor_id, remaining);
        }
        Ok(redeemed)
    }

    /// The committed `total_assets` (the internal accounting counter — NOT the raw
    /// custody balance; a raw donation cannot move this, the donation-immunity that
    /// closes the ERC-4626 inflation attack).
    pub fn total_assets(&self) -> i64 {
        ShareVaultState::read(&self.vault)
            .map(|s| s.total_assets)
            .unwrap_or(0)
    }

    /// The committed `total_shares` supply outstanding across all sponsors.
    pub fn total_shares(&self) -> i64 {
        ShareVaultState::read(&self.vault)
            .map(|s| s.total_shares)
            .unwrap_or(0)
    }

    /// The share slice a sponsor wallet holds of this fund.
    pub fn shares_of(&self, sponsor: CellId) -> i64 {
        self.shares.get(&sponsor).copied().unwrap_or(0)
    }

    /// The pooled value held in custody (the raw balance backing the shares).
    pub fn pooled_value(&self) -> i64 {
        self.custody.state.balance()
    }

    /// The vault host cell's canonical commitment — moves when the counters
    /// advance on a deposit or withdrawal (a light client witnesses every change).
    pub fn commitment(&self) -> [u8; 32] {
        self.vault.state_commitment()
    }

    /// Whether the host cell carries a share-vault binding (it does after [`open`](Self::open)).
    pub fn is_open(&self) -> bool {
        is_share_vault(&self.vault)
    }
}

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
///
/// ⚑ The `BUDGET` slot is a `WriteOnce` PROMISE, not a holding: nothing moves
/// here, and nothing can (see the crate docs for the three measured executor
/// refusals). [`build_settle_actions`] is what pays, out of the requester's own
/// balance, and it is an `InsufficientBalance` refusal if that balance cannot
/// cover the accepted bid.
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
            index: REQUESTER_HASH_SLOT as u64,
            value: requester_h,
        },
        Effect::SetField {
            cell: job_cell,
            index: BUDGET_SLOT as u64,
            value: budget_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: SPEC_HASH_SLOT as u64,
            value: *spec,
        },
        Effect::SetField {
            cell: job_cell,
            index: STATE_SLOT as u64,
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
            index: PROVIDER_HASH_SLOT as u64,
            value: provider_h,
        },
        Effect::SetField {
            cell: job_cell,
            index: BID_SLOT as u64,
            value: price_f,
        },
        Effect::SetField {
            cell: job_cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_BID),
        },
        Effect::EmitEvent {
            cell: job_cell,
            event: Event::new(symbol("job-bid"), vec![provider_h, price_f]),
        },
    ];
    cclerk.make_action(job_cell, "bid", effects)
}

/// **settle** — close the deal: **the provider is PAID `paid`** out of the
/// requester's balance, `refunded` is the undrawn remainder of the budget, and
/// `STATE` advances to SETTLED. Returns one or two [`Action`]s to be submitted as
/// roots of **ONE** turn ([`AppCipherclerk::make_turn_with_actions`], the node's
/// multi-action ingress).
///
/// They are one atomic outcome: a requester who cannot cover `paid` rolls the
/// `STATE = SETTLED` stamp back with the transfer, so no surface can ever show a
/// settled job over a payment that did not happen.
///
///   * the PAYMENT action targets the payer (`cclerk`'s own cell) and carries the
///     conserving [`Effect::Transfer`] from [`payment_effects`] — it MUST target
///     the payer, because `apply_transfer` only skips its cross-cell `Send` check
///     when the transfer's `from` IS the action target, and that check demands
///     `send == AuthRequired::None`, which a user cell's is not;
///   * the SETTLE action targets the job and writes `PAID` / `REFUNDED` /
///     `STATE -> SETTLED`, emitting `job-settled` with the amount, the remainder
///     and the payee so the event names the value that moved and not only a flag.
///
/// When the payer IS the job cell (the deos composition surface and the service
/// face both drive a job that is the agent's own cell) the two collapse into ONE
/// action ([`settlement_effects`]), which is strictly stronger: one action cannot
/// half-commit at all.
///
/// - Provider paid in full: `build_settle_actions(.., provider, bid, budget - bid)`.
/// - Full refund (job cancelled): `build_settle_actions(.., provider, 0, budget)` —
///   a CANCELLATION. It carries no payment leg because nothing is owed, and the
///   record reads `paid = 0`, which is what the card then shows.
///
/// ⚠ Nothing here binds `provider` to the job's committed `PROVIDER_HASH`, nor the
/// transfer's amount to the `PAID` slot. No `StateConstraint` relates a `Transfer`
/// destination or amount to a state slot, so those checks belong to whoever can
/// read the slots until the constraint language grows atoms for them, which is
/// Lean-authored work.
pub fn build_settle_actions(
    cclerk: &AppCipherclerk,
    job_cell: CellId,
    provider: CellId,
    paid: u64,
    refunded: u64,
) -> Vec<Action> {
    let payer = cclerk.cell_id();
    if payer == job_cell {
        return vec![cclerk.make_action(
            job_cell,
            "settle",
            settlement_effects(job_cell, provider, paid, refunded),
        )];
    }
    let settle = cclerk.make_action(
        job_cell,
        "settle",
        settle_effects(job_cell, provider, paid, refunded),
    );
    let payment = payment_effects(payer, provider, paid);
    if payment.is_empty() {
        return vec![settle];
    }
    vec![
        cclerk.make_action(payer, "pay_job_settlement", payment),
        settle,
    ]
}

// =============================================================================
// Convenience encoders (mirror what the executor + CLI see)
// =============================================================================

/// `blake3(party)` — the value written into `REQUESTER_HASH_SLOT` /
/// `PROVIDER_HASH_SLOT`.
pub fn party_hash(party: &str) -> FieldElement {
    field_from_bytes(party.as_bytes())
}

/// **The same named party AS A CELL ID** — the payee [`settle_effects`] writes into
/// the `job-settled` payload, for the surfaces whose parties are NAMES rather than
/// funded cells (the desktop exchange floor, the wired-card bakes). A blake3
/// derive-key over the name, so one name is one stable id everywhere.
///
/// ⚠ **Paired with [`party_hash`], NOT equal to it, and NOT a funded cell.**
/// `party_hash` is the field-encoded value in the cell's `*_HASH` slot;
/// this is a 32-byte id in the event payload. Both derive from the same string, so
/// they name the same party, but a caller that only has these has an IDENTITY and
/// no balance — [`payment_effects`] needs a real cell holding value. A surface
/// using this is emitting the settlement RECORD only; see the ⚠ on
/// [`build_settle_actions`] for the leg that moves the money.
pub fn party_id(party: &str) -> CellId {
    let mut h = blake3::Hasher::new_derive_key("dregg compute-exchange party id v1");
    h.update(party.as_bytes());
    CellId(*h.finalize().as_bytes())
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
//      (`AffineEq`/`AffineLe`), a non-advancing/rewinding STATE (`StrictMonotonic`)
//      and a settlement the requester cannot fund (`InsufficientBalance` on the
//      settle's `Effect::Transfer`) are REAL executor refusals in the SUBMISSION
//      path — the half the floor's `evaluate`-only tests never exercised through a
//      real signed turn (see `tests/deos_seam.rs` and
//      `tests/settlement_conservation.rs`).

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
///   - `settle` — a [`GatedAffordance`] (the REQUESTER pays and closes the job):
///     `None`, a live-state PRECONDITION (the job is BID); the real fire
///     ([`fire_settle`]) reads live `BID` + `BUDGET`, **transfers `BID` to the
///     provider** and writes PAID := BID, REFUNDED := BUDGET - BID, STATE->SETTLED
///     in one action, so the executor's installed FLASHWELL `AffineEq(PAID +
///     REFUNDED == BUDGET)` holds on the honest path and a requester who cannot
///     cover the bid takes the SETTLED stamp down with the payment.
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
                index: STATE_SLOT as u64,
                value: field_from_u64(STATE_BID),
            },
        ),
        posted_precondition(),
    );
    // `settle` — the REQUESTER pays the provider and closes the job. The decisive
    // effect shown on the surface is the STATE->SETTLED advance; gated on the BID
    // precondition ([`bid_precondition`]). The FIRE carries more than this
    // representative: `fire_settle` adds the conserving `Effect::Transfer` of the
    // accepted bid. The executor re-enforces the installed FLASHWELL
    // `AffineEq(PAID + REFUNDED == BUDGET)` (a value-conjuring split is refused)
    // and refuses the whole action if the requester cannot cover the payment.
    let settle = GatedAffordance::new(
        CellAffordance::new(
            "settle",
            REQUESTER_RIGHTS,
            Effect::SetField {
                cell,
                index: STATE_SLOT as u64,
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
            index: PROVIDER_HASH_SLOT as u64,
            value: provider_h,
        },
        Effect::SetField {
            cell,
            index: BID_SLOT as u64,
            value: price_f,
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_BID),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-bid"), vec![provider_h, price_f]),
        },
    ]
}

/// **The PAYMENT leg** — the conserving kernel [`Effect::Transfer`] moving `paid`
/// from `payer` to `provider`, produced by [`pay_effects`]: the shared `Payable`
/// desugar `resolve_pay` / `Payable::pay` resolve to, so this crate has no private
/// notion of moving money.
///
/// EMPTY when `paid == 0`, which is the CANCELLATION case (`build_settle_actions(..,
/// 0, budget)`): a full-refund settlement owes the provider nothing, so it moves
/// nothing and the record says so. That is the one honest way this crate emits a
/// settlement with no transfer, and the `PAID` slot the card binds reads `0`.
pub fn payment_effects(payer: CellId, provider: CellId, paid: u64) -> Vec<Effect> {
    if paid == 0 {
        return Vec::new();
    }
    pay_effects(payer, provider, paid)
}

/// **The RECORD leg** — write `PAID := paid`, `REFUNDED := refunded`, advance
/// `STATE -> SETTLED`, and emit `job-settled` carrying the amount, the undrawn
/// remainder and the PAYEE, so the receipt names the value that moved rather than
/// only a flag having flipped.
///
/// The FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)` requires `paid + refunded ==
/// budget`, and it constrains exactly these three slots — the RECORD, not the
/// balances. The value is moved by [`payment_effects`], and the two are bound
/// together only by the builder that emits both: see the ⚠ on
/// [`build_settle_actions`].
pub fn settle_effects(cell: CellId, provider: CellId, paid: u64, refunded: u64) -> Vec<Effect> {
    let paid_f = field_from_u64(paid);
    let refunded_f = field_from_u64(refunded);
    let mut payee = [0u8; 32];
    payee.copy_from_slice(provider.as_bytes());
    vec![
        Effect::SetField {
            cell,
            index: PAID_SLOT as u64,
            value: paid_f,
        },
        Effect::SetField {
            cell,
            index: REFUNDED_SLOT as u64,
            value: refunded_f,
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_SETTLED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-settled"), vec![paid_f, refunded_f, payee]),
        },
    ]
}

/// **`settle` effects, for a job cell that IS the payer** — the payment leg and the
/// record leg in ONE action body, which the executor admits because the transfer's
/// `from` is the action target AND the same action strictly advances `STATE` (a
/// `StrictMonotonic` cell refuses any action that touches it without advancing,
/// including a bare credit — see the crate docs).
///
/// THIS is the turn [`fire_settle`] submits, and the single-action arm of
/// [`build_settle_actions`].
pub fn settlement_effects(cell: CellId, provider: CellId, paid: u64, refunded: u64) -> Vec<Effect> {
    let mut effects = payment_effects(cell, provider, paid);
    effects.extend(settle_effects(cell, provider, paid, refunded));
    effects
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
///
/// The amount is READ OFF THE LIVE CELL — the committed `BID` slot, which is
/// `WriteOnce` and therefore exactly the price the requester accepted. The fire
/// **PAYS `provider` that amount** with the conserving [`Effect::Transfer`] and
/// writes `PAID := BID`, `REFUNDED := BUDGET - BID`, `STATE -> SETTLED`, all in ONE
/// action, so the FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)` holds on the
/// honest path and neither leg can land without the other. A caller cannot name a
/// different figure.
///
/// On this surface the job cell IS the agent's own cell, so the payment and the
/// record ride one action ([`settlement_effects`]). The executor is the verified
/// second gate twice over: `StrictMonotonic(STATE)` on the one-way advance, and
/// `InsufficientBalance` on a requester that cannot cover the accepted bid. Use
/// after a successful [`fire_bid`].
pub fn fire_settle(
    app: &DeosApp,
    held: &AuthRequired,
    provider: CellId,
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
        settlement_effects(target, provider, bid, refunded)
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
