//! # `dregg-pay` — accept `$DREGG` (SPL token on Solana) for real-AI dungeon runs.
//!
//! The **"B" (custodial HD-deposit) model** payment backend, and the reusable
//! foundation the discord-bot + demo dungeon services consume. It has four pieces
//! behind clean, pluggable traits:
//!
//! 1. [`DepositAddressProvider`] — a per-user deposit address.
//!    [`HdDeposit`] is the "B" impl: SLIP-0010 ed25519 hardened derivation from one
//!    [`Seed`] (`m/44'/501'/index'`), so one seed fans out into a deterministic,
//!    per-user Solana address. A future "C" impl (a per-user PDA under an on-chain
//!    program) implements the same trait and swaps in.
//! 2. [`Watcher`] — detect an inbound payment to a deposit address, attributed to
//!    the user automatically. [`MockWatcher`] (driven) and [`SolanaWatcher`] (the
//!    real path, reusing the bridge proof-of-holdings SPL decode + consensus verify).
//! 3. [`CreditLedger`] — per-user RUN credits, minted from payments at a configured
//!    price, spent one-per-run, **idempotent per payment reference**, over a
//!    pluggable [`CreditStore`] (the bot persists via sqlite).
//! 4. [`Sweeper`] — move a deposit balance to the treasury. [`MockSweeper`] (driven)
//!    and [`SolanaSweeper`] (signs with the derived custody key). The sweeper is the
//!    custody point — it holds the seed.
//!
//! [`PayConfig`] holds all operator config (mint, treasury, seed, price-per-run,
//! RPC, network). **Nothing mainnet is hardcoded**: the mint + treasury + seed come
//! from the environment in production and from throwaway fixtures in tests. The
//! default network is [`Network::Devnet`]; mainnet is a deliberate operator flip.
//!
//! ## Dual-asset economics (`$DREGG` + USDC)
//!
//! The backend accepts EITHER asset ([`Asset::Usdc`] or [`Asset::Dregg`]) and both
//! credit runs:
//!
//! * **USDC is the FUEL, `$DREGG` is the PILE.** A real-AI run costs real USD, drawn
//!   from the [`Treasury`]'s `usdc_balance` ([`Treasury::spend_inference_usd`], which
//!   fails closed on empty — the "must refuel" signal). USDC payments fill the fuel
//!   tank; `$DREGG` payments accumulate in the illiquid pile (a `$DREGG`-paid run
//!   still burns USD fuel but only grows the pile).
//! * **Pricing** ([`pricing`]): a run is [`PayConfig::price_usd_per_run`] (default
//!   `$0.10`). USDC pays that flat; `$DREGG` pays a price-fed rate at a 20% holder
//!   discount ([`PayConfig::dregg_discount_bps`]) via a [`PriceOracle`]
//!   ([`JupiterPriceOracle`] real / [`MockOracle`] tests). [`runs_for_payment`] does
//!   the conversion.
//! * **OTC** ([`otc`]): [`otc_quote`] lets a user bring USDC and buy `$DREGG` out of
//!   the pile at a 10% discount ([`PayConfig::otc_discount_bps`]) — quote + accounting
//!   only, the transfer executes behind the operator's signer.
//!
//! ## Honest scope
//!
//! * **Custodial.** The "B" model holds the HD seed; whoever runs the sweeper can
//!   move every user's deposit. On ed25519 there is no watch-only (xpub) trick —
//!   deriving a deposit address requires the secret seed. This is named in
//!   [`hd`], not hidden.
//! * **Devnet / mock by default.** The driven tests use a throwaway seed and a mock
//!   mint over a simulated chain; the real Solana path is structured and its crypto
//!   (derivation, signing, SPL decode, consensus verify) is genuine, but hitting
//!   mainnet is an operator-config flip, never done in tests.
//! * **The endgame is protocol-native settlement** — run budget as a conserved
//!   on-chain `Effect::Transfer` balance, so no operator holds user funds. This
//!   backend is the pragmatic bridge to that.
//! * **Signer-gated edges — built here, behind the operator's signer.** The
//!   collective-governed **liquidity vote** ([`governance`]), the pile→fuel **swap
//!   execution** ([`swap`] — the real Jupiter v6 `$DREGG`→SOL→USDC quote + swap-tx
//!   build, over injected [`HttpGet`]/[`HttpPost`] seams), and the **OTC transfer
//!   settlement** ([`otc::otc_settle`]) all land in this crate. Each verifies a
//!   governance/vote gate and signs behind an operator-held [`Signer`]; `dregg-pay`
//!   holds no key. What a LIVE swap still needs is a real HTTP transport bound to the
//!   seams, the operator's secured signer over the built tx, and broadcast (splice the
//!   signature, `sendTransaction`, read realized-out) — mainnet is a config flip on
//!   ember's go; custody remains the seed/signer.

pub mod config;
pub mod governance;
pub mod hd;
pub mod ledger;
pub mod multichain;
pub mod nft_mint;
pub mod otc;
pub mod pricing;
// Track C rung 2a — the protocol-native run-budget rail: a conserved cell balance
// in an internal asset, spent by one conserving `Effect::Transfer` the user
// authorizes. Additive over the custodial rail; it holds NO custody key and NO
// sweeper (`docs/deos/PROTOCOL-NATIVE-ECONOMY.md` §4 rung 2a).
pub mod protocol_native;
pub mod swap;
pub mod sweeper;
pub mod treasury;
pub mod watcher;

pub use config::{
    Asset, ConfigError, DEFAULT_DREGG_DECIMALS, DEFAULT_DREGG_DISCOUNT_BPS,
    DEFAULT_OTC_DISCOUNT_BPS, DEFAULT_PRICE_USD_PER_RUN, DEFAULT_USDC_DECIMALS, DepositAddress,
    Network, PayConfig, PayRole, SPL_TOKEN_PROGRAM_ID, Seed, UserId, parse_pubkey_base58,
};
pub use governance::{
    APPROVE_OPTION, GovernanceError, LiquidityGovernance, LiquidityProposal, REJECT_OPTION,
};
pub use hd::{
    DepositAddressBook, DepositAddressProvider, HdDeposit, derive_deposit_address,
    derive_signing_key, user_index,
};
pub use ledger::{
    CreditLedger, CreditOutcome, CreditStore, DebitError, InMemoryStore, StoreCreditOutcome,
};
pub use multichain::{
    HoldingRejection, MultichainHoldings, ProvenChainHolding, RejectedHolding, TreasurySlot,
    TreasuryView,
};
// The cross-chain read primitives the multichain treasury view binds against —
// re-exported so a consumer (the discord-bot) can declare treasury positions and
// ingest proof-of-holdings facts through `dregg-pay` alone, without taking a direct
// `dregg-governance` dependency (the light-client lanes render these; the treasury
// view points them at the treasury's own addresses).
pub use dregg_governance::proven_foreign_holding::{ChainId, ProvenForeignHolding};
pub use nft_mint::{
    ATA_PROGRAM_ID, BuiltNftMint, CompiledInstruction, DreggAchievementProof, MEMO_PROGRAM_ID,
    MINT_RENT_LAMPORTS, MintNftRequest, NftMintError, NftMinter, NftTxSubmitter, SPL_MINT_LEN,
    SYSTEM_PROGRAM_ID, build_mint_nft, find_associated_token_address,
};
pub use otc::{
    OtcError, OtcQuote, OtcSettleError, OtcSettlement, otc_dregg_out, otc_quote, otc_settle,
    otc_settle_message,
};
pub use pricing::{
    HttpGet, JupiterPriceOracle, MockOracle, PriceError, PriceOracle, discount_factor,
    parse_jupiter_price, runs_for_payment,
};
pub use protocol_native::{
    ChargeError, DEFAULT_RUN_PRICE_CREDITS, RUN_CREDIT_ASSET_DOMAIN, RunBudgetLedger, RunReceipt,
    RunSettlementMode, run_credit_asset,
};
// The value-id and pay-authority types the protocol-native `charge_run` signature
// requires ([`RunBudgetLedger::charge_run`]), re-exported so a consumer (the demo
// dungeon service) can drive the conserved run charge through `dregg-pay` alone —
// without taking a direct `dregg-payable` / `dregg-types` dependency.
pub use dregg_payable::{InvokeAuthority, InvokeRefused};
pub use dregg_types::CellId;
pub use swap::{
    BuiltSwap, GovernanceAuthority, HttpPost, JupiterQuote, JupiterSwap, JupiterVenue, MockSigner,
    MockSwapVenue, RouteHop, Signer, SignerError, SwapAuthorization, SwapError, SwapOutcome,
    SwapRoute, SwapVenue, UnsignedSwapTx, parse_jupiter_quote, solana_sign_target, swap_message,
};
pub use sweeper::{
    MockSweeper, SolanaSweeper, SweepError, SweepOutcome, SweepRequest, Sweeper, TxSubmitter,
    sweep_message,
};
pub use treasury::{InMemoryTreasuryStore, Treasury, TreasuryError, TreasuryStore};
pub use watcher::{
    AccountFetcher, FetchedAccount, MockChain, MockWatcher, PaymentReceived, PaymentRef,
    SolanaWatcher, WatchError, Watcher,
};
