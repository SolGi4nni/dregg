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

pub mod config;
pub mod hd;
pub mod ledger;
pub mod sweeper;
pub mod watcher;

pub use config::{
    ConfigError, DepositAddress, Network, PayConfig, SPL_TOKEN_PROGRAM_ID, Seed, UserId,
    parse_pubkey_base58,
};
pub use hd::{
    DepositAddressProvider, HdDeposit, derive_deposit_address, derive_signing_key, user_index,
};
pub use ledger::{CreditLedger, CreditOutcome, CreditStore, DebitError, InMemoryStore};
pub use sweeper::{
    MockSweeper, SolanaSweeper, SweepError, SweepOutcome, SweepRequest, Sweeper, TxSubmitter,
    sweep_message,
};
pub use watcher::{
    AccountFetcher, FetchedAccount, MockChain, MockWatcher, PaymentReceived, PaymentRef,
    SolanaWatcher, WatchError, Watcher,
};
