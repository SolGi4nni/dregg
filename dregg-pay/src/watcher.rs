//! [`Watcher`] — detect inbound `$DREGG` payments to a user's deposit address.
//!
//! # RESTART SEMANTICS (`docs/reference/RESTART-SEMANTICS.md`)
//!
//! **The production credit path holds NO in-RAM cursor.** [`SignatureWatcher`] is the
//! selected real watcher and it is *process-stateless*: it re-observes the recent
//! transfer history on every poll and mints one [`PaymentRef`] per **transaction
//! signature**, a property of the CHAIN rather than of this process. Deduplication is
//! entirely the durable [`CreditLedger`](crate::ledger::CreditLedger)'s job, which is
//! answer **2 (REBUILD)** in its strongest form — the durable source needs no new store,
//! because the already-durable `pay_processed` table *is* the cursor.
//!
//! This is deliberate, and it is the repair of a real wound: the balance-total key
//! `sol:{addr}:{slot}:{amount}` bound the RPC's **current** slot, which advances every
//! ~400ms, so the key was fresh on every poll and the durable table could never
//! recognise a repeat. The only thing making that path idempotent was an in-RAM
//! `last_seen` map — empty at boot — so **every restart re-credited every standing
//! balance**. Persisting `last_seen` would have made the OPPOSITE bug durable (a sweep
//! plus a same-total re-deposit between two polls loses that credit permanently, and a
//! restart is today the only thing that heals it). The key had to change, not the store.
//!
//! # The impls
//!
//! * [`SignatureWatcher`] — **the production credit path.** One
//!   [`PaymentReceived`] per finalized inbound transfer, keyed on the transaction
//!   signature (`soltx:{signature}`). Restart-stable, sweep-stable, unique per
//!   transfer. The signature-history transport is the injected [`TransferFetcher`]
//!   seam, so the fail-closed attribution logic is exercised with no network.
//! * [`MockWatcher`] over a [`MockChain`] — a simulated devnet ledger, fully driven
//!   in tests (no network, no funds). Balance-total based, and therefore NOT
//!   restart-safe; see its `RESTART:` declaration for why that is a deliberate
//!   answer 3 rather than an oversight.
//! * [`SolanaWatcher`] — **no longer a [`Watcher`]**. It keeps the two things that
//!   were always sound: the bridge crate's
//!   [`decode_spl_token_account`](dregg_bridge::solana_holdings::decode_spl_token_account)
//!   balance read ([`SolanaWatcher::read_balance`]) and, for a trustless read, the
//!   bridge's **anchored** verifier
//!   [`prove_holding_consensus_anchored`](dregg_bridge::solana_holdings::prove_holding_consensus_anchored)
//!   (authorized-voter-bound ≥ 2/3 supermajority over a stake table DERIVED from
//!   bank state, trusted only back to the operator's governance-pinned
//!   [`WeakSubjectivityAnchor`] — never a caller-supplied stake table, which an
//!   attacker could fabricate). Its `impl Watcher` and its `last_seen` map are
//!   DELETED: a balance total is not an idempotency key, so nothing should be able
//!   to hand a balance-total watcher to something that credits money.
//!
//! **Attribution is automatic**: a payment landing on user X's derived deposit
//! address IS X's payment, because the address derivation is deterministic and the
//! caller polls with the `(user, address)` pair it derived.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use dregg_bridge::solana_consensus::PohAnchorPolicy;
use dregg_bridge::solana_holdings::{
    HoldingProof, HoldingProofError, ProvenHolding, decode_spl_token_account,
    prove_holding_consensus_anchored,
};
use dregg_bridge::solana_provenance::WeakSubjectivityAnchor;

use crate::config::{Asset, DepositAddress, PayConfig, UserId};

/// A unique reference for an observed payment — the idempotency key the
/// [`CreditLedger`](crate::ledger::CreditLedger) dedups on.
///
/// **The key must be a property of the CHAIN, not of this process.** The production
/// [`SignatureWatcher`] mints `soltx:{signature}` from the transaction signature: the
/// same transfer yields the same reference from any process, at any slot, before or
/// after a sweep, forever. A reference built from the RPC's current slot, or from a
/// process-local counter, is fresh on every poll and makes the durable dedupe table
/// dedupe nothing — that was the wound this type's doc used to describe.
///
/// The [`MockWatcher`] still mints a balance-total + in-RAM-sequence reference, which
/// is honest only because its chain is process-local (see its `RESTART:` declaration).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PaymentRef(pub String);

impl std::fmt::Display for PaymentRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// An inbound payment attributed to a user, in one of the two accepted assets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentReceived {
    /// The user the payment is attributed to (owner of the deposit address).
    pub user: UserId,
    /// The deposit address the payment landed on.
    pub deposit_address: DepositAddress,
    /// Which asset the payment was in ([`Asset::Dregg`] the pile, [`Asset::Usdc`] the
    /// fuel) — determines both how the run is priced and which treasury balance it
    /// fills.
    pub asset: Asset,
    /// The amount received, in atomic units of [`PaymentReceived::asset`].
    pub amount: u64,
    /// The idempotency key — crediting this reference twice never double-credits.
    pub reference: PaymentRef,
}

/// Why a watch failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WatchError {
    /// The RPC/transport failed.
    Rpc(String),
    /// The fetched account was not a decodable SPL token account, held the wrong
    /// mint, or was not owned by the SPL Token program (fail closed — reuses the
    /// bridge's [`HoldingProofError`]).
    Holding(HoldingProofError),
    /// The fetched SPL account's embedded token owner was not the deposit wallet.
    /// RPC selection is not trusted as proof of attribution.
    WrongTokenOwner {
        expected: [u8; 32],
        actual: [u8; 32],
    },
}

impl std::fmt::Display for WatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WatchError::Rpc(e) => write!(f, "rpc error: {e}"),
            WatchError::Holding(e) => write!(f, "holding decode refused: {e}"),
            WatchError::WrongTokenOwner { expected, actual } => write!(
                f,
                "token-account owner mismatch: expected {}, got {}",
                bs58::encode(expected).into_string(),
                bs58::encode(actual).into_string()
            ),
        }
    }
}

impl std::error::Error for WatchError {}

/// Detect inbound payments to a user's deposit address.
///
/// **Idempotency lives at the LEDGER, by [`PaymentReceived::reference`] — never at the
/// watcher.** An impl is explicitly permitted (and, for [`SignatureWatcher`], required)
/// to re-report a payment it has already reported: what it must guarantee is that
/// re-reporting the same on-chain event yields the same `reference`. Watcher-level
/// "I already reported that" is in-RAM state, and in-RAM state is empty at boot; a
/// watcher that relies on it is a watcher that re-credits everything after a deploy.
/// Callers MUST route every returned payment through
/// [`CreditLedger::credit`](crate::ledger::CreditLedger::credit) (or `credit_runs`) and
/// act only on a `Credited` / `BelowOneRun` outcome.
pub trait Watcher {
    /// Poll for payments to `address` (owned by `user`). Returns every payment
    /// currently observable in the watcher's window (empty if none) — including ones
    /// a previous poll already returned. The ledger deduplicates.
    fn poll(
        &self,
        user: &UserId,
        address: &DepositAddress,
    ) -> Result<Vec<PaymentReceived>, WatchError>;
}

// ─────────────────────────────────────────────────────────────────────────────
// MOCK / devnet path
// ─────────────────────────────────────────────────────────────────────────────

/// A simulated on-chain balance ledger for driven tests — maps a deposit address
/// to its `$DREGG` balance. Shared (`Arc`) between the [`MockWatcher`] (which reads
/// balances) and the [`MockSweeper`](crate::sweeper::MockSweeper) (which moves them
/// to the treasury), exactly as a real chain is the shared source of truth for both.
#[derive(Clone, Default)]
pub struct MockChain {
    /// RESTART: **PROCEED, deliberately (answer 3).** This is the simulated CHAIN, not
    /// a guard — it is the thing a restart is supposed to be able to read back, and it
    /// cannot, because it is a `HashMap` in this process. That is sound only because
    /// the mock chain is *unreachable from outside the process*: the sole writer is
    /// [`MockChain::credit_onchain`], which is called exclusively from test code that
    /// already holds this handle. In every deployed configuration the mock chain is
    /// constructed empty by
    /// `select_watcher`, never written, and therefore observes nothing across a restart
    /// because it observed nothing before one. An adversary who forces a restart gains
    /// an empty map, which is what they had.
    balances: Arc<Mutex<HashMap<[u8; 32], u64>>>,
}

impl MockChain {
    /// A fresh empty chain.
    pub fn new() -> Self {
        Self::default()
    }

    /// Simulate an inbound `$DREGG` payment landing on `address` (increments its
    /// on-chain balance) — the test's "someone paid".
    pub fn credit_onchain(&self, address: &DepositAddress, amount: u64) {
        let mut b = self.balances.lock().unwrap();
        *b.entry(address.to_bytes()).or_insert(0) += amount;
    }

    /// The current on-chain balance of `address`.
    pub fn balance(&self, address: &DepositAddress) -> u64 {
        *self
            .balances
            .lock()
            .unwrap()
            .get(&address.to_bytes())
            .unwrap_or(&0)
    }

    /// Move the ENTIRE balance of `from` to `to` (the sweep). Returns the amount
    /// moved.
    pub fn transfer_all(&self, from: &DepositAddress, to: &DepositAddress) -> u64 {
        let mut b = self.balances.lock().unwrap();
        let amount = b.get(&from.to_bytes()).copied().unwrap_or(0);
        if amount > 0 {
            b.insert(from.to_bytes(), 0);
            *b.entry(to.to_bytes()).or_insert(0) += amount;
        }
        amount
    }
}

/// The mock watcher: observes balance increases on a [`MockChain`] and emits an
/// attributed [`PaymentReceived`] for each new increment. It tracks the last-seen
/// balance per address, so re-polling without a new payment returns nothing.
///
/// # Not restart-safe, and that is an argued answer 3
///
/// Both fields below are in-RAM guards with the SAME defect the production watcher had
/// (`docs/reference/RESTART-SEMANTICS.md`), and they are deliberately left transient.
/// The argument — which the rule doc demands be stated, not assumed — is that the mock
/// chain this watcher reads is **process-local and unwritable from outside the
/// process**. `select_watcher` builds `MockWatcher::new(MockChain::new())`: a fresh,
/// empty chain that only test code holding the same handle can ever credit. A deployed
/// mock watcher therefore observes zero payments, and re-observing zero payments after
/// a restart credits zero runs. **What an adversary gains by forcing the restart is
/// nothing, because there is nothing on the chain to re-observe.**
///
/// If the mock is ever pointed at a chain an outsider can write, this argument dies and
/// the fix is [`SignatureWatcher`]'s shape: give the chain its own per-transfer identity
/// and key the reference on it.
pub struct MockWatcher {
    chain: MockChain,
    asset: Asset,
    /// RESTART: **PROCEED, deliberately (answer 3)** — see the type doc. Absence means
    /// "no balance seen yet", so after a restart the whole standing mock balance is
    /// re-observed as one fresh delta. On a real chain that is a double-credit; on the
    /// process-local [`MockChain`] the standing balance is always `0`.
    last_seen: Mutex<HashMap<[u8; 32], u64>>,
    /// RESTART: **PROCEED, deliberately (answer 3)** — see the type doc. This counter
    /// exists because balance totals repeat after a sweep and so are not an idempotency
    /// key; a restart resets it to `0`, which means a re-observed balance can mint a
    /// reference the ledger has already processed (silently correct) *or* a fresh one
    /// (a double-credit). Neither is reachable while the chain is empty.
    next_reference: Mutex<u64>,
}

impl MockWatcher {
    /// A watcher over the given chain, tagging observed payments as [`Asset::Dregg`]
    /// (the default single-asset path). Use [`MockWatcher::for_asset`] to watch the
    /// USDC deposit stream.
    pub fn new(chain: MockChain) -> Self {
        Self::for_asset(chain, Asset::Dregg)
    }

    /// A watcher over the given chain tagging observed payments as `asset` — run one
    /// per accepted mint (one for `$DREGG`, one for USDC) to cover both assets.
    pub fn for_asset(chain: MockChain, asset: Asset) -> Self {
        MockWatcher {
            chain,
            asset,
            last_seen: Mutex::new(HashMap::new()),
            next_reference: Mutex::new(0),
        }
    }

    /// The chain this watcher observes.
    pub fn chain(&self) -> &MockChain {
        &self.chain
    }

    /// The asset this watcher tags payments with.
    pub fn asset(&self) -> Asset {
        self.asset
    }
}

impl Watcher for MockWatcher {
    fn poll(
        &self,
        user: &UserId,
        address: &DepositAddress,
    ) -> Result<Vec<PaymentReceived>, WatchError> {
        let current = self.chain.balance(address);
        let mut seen = self.last_seen.lock().unwrap();
        let prev = *seen.get(&address.to_bytes()).unwrap_or(&0);
        if current < prev {
            // A sweep/outbound transfer lowered the account. Rebase the balance
            // cursor; otherwise every later deposit at or below the old high-water
            // mark is ignored forever.
            seen.insert(address.to_bytes(), current);
            return Ok(vec![]);
        }
        if current == prev {
            return Ok(vec![]);
        }
        let delta = current - prev;
        seen.insert(address.to_bytes(), current);
        // Balance totals repeat after a sweep, so they are not an idempotency key.
        // Give every emitted mock-chain observation a monotone synthetic sequence.
        let mut next_reference = self.next_reference.lock().unwrap();
        *next_reference = next_reference
            .checked_add(1)
            .expect("mock payment reference sequence exhausted");
        let reference = PaymentRef(format!(
            "mock:{}:{}:{current}",
            address.to_base58(),
            *next_reference
        ));
        Ok(vec![PaymentReceived {
            user: user.clone(),
            deposit_address: *address,
            asset: self.asset,
            amount: delta,
            reference,
        }])
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// REAL Solana path — reuses the bridge proof-of-holdings core
// ─────────────────────────────────────────────────────────────────────────────

/// A token account fetched from an RPC — the raw material the real watcher decodes.
#[derive(Clone, Debug)]
pub struct FetchedAccount {
    /// The SPL token account's `data` (the 165-byte `mint ‖ owner ‖ amount ‖ …`
    /// layout decoded by [`decode_spl_token_account`]).
    pub data: Vec<u8>,
    /// The on-chain owner *program* — must be the SPL Token program (fail closed).
    pub owner_program: [u8; 32],
    /// The finalized slot the read was reported at (bound into the payment ref).
    pub slot: u64,
}

/// The RPC seam. A production impl issues `getTokenAccountsByOwner(deposit_address,
/// {mint})` against the configured endpoint and returns the token account's base64
/// `data`. This is the same injected-transport shape the bridge uses for its Solana
/// relayer (so no reqwest/tokio is forced into the verified core). Tests supply a
/// mock fetcher returning real SPL-layout bytes.
pub trait AccountFetcher {
    /// Fetch the SPL token account owned by `owner` for `mint`, or `None` if the
    /// owner has no token account for that mint yet.
    fn fetch_token_account(
        &self,
        owner: &DepositAddress,
        mint: &[u8; 32],
    ) -> Result<Option<FetchedAccount>, WatchError>;
}

/// The Solana **balance reader** + anchored proof-of-holdings verifier.
///
/// # This is NOT the credit path, by construction
///
/// It has no `impl Watcher` and no cursor. It used to have both, and the pair was the
/// wound: a balance total is not an idempotency key (it repeats after a sweep), so the
/// reference was padded with the RPC's *current* slot to make it unique — which made it
/// unique on every poll, which made the durable dedupe table useless, which left an
/// in-RAM `last_seen` map as the only thing standing between a deploy and re-crediting
/// every user's whole standing balance. Deleting the `impl Watcher` is what makes that
/// unrepeatable: there is no longer any way to hand a balance-total observer to
/// something that credits money. Crediting goes through [`SignatureWatcher`].
///
/// What remains is the part that was always sound and is still used:
///
/// * [`SolanaWatcher::read_balance`] — the bridge's exact SPL token-account decode with
///   its full fail-closed forgery defense (SPL-program ownership, mint match, embedded
///   token-owner attribution). A *balance*, honestly typed as a balance.
/// * [`SolanaWatcher::verify_consensus`] — the anchored, consensus-verified holding.
pub struct SolanaWatcher<F: AccountFetcher> {
    fetcher: F,
    mint: [u8; 32],
    asset: Asset,
    spl_token_program: [u8; 32],
    /// The operator's governance-pinned weak-subjectivity anchor — the ONLY trust
    /// root [`SolanaWatcher::verify_consensus`] accepts. `None` (not configured)
    /// fails closed: no consensus-verified holding can be produced, and there is
    /// NO fallback to a caller-supplied stake table.
    pinned_anchor: Option<WeakSubjectivityAnchor>,
    /// The bounded PoH anchor policy paired with the pinned anchor (required to
    /// verify any PoH segment on the anchored path).
    poh_policy: Option<PohAnchorPolicy>,
}

impl<F: AccountFetcher> SolanaWatcher<F> {
    /// Build from a [`PayConfig`] + an RPC fetcher, watching the `$DREGG` mint (the
    /// default). Use [`SolanaWatcher::for_asset`] to watch USDC (its mint + tag).
    pub fn new(config: &PayConfig, fetcher: F) -> Self {
        Self::for_asset(config, fetcher, Asset::Dregg)
    }

    /// Build a watcher for a specific `asset` — it watches that asset's mint
    /// ([`PayConfig::mint_for`]) and tags observed payments with it. Run one per
    /// accepted asset for the dual-asset stream.
    pub fn for_asset(config: &PayConfig, fetcher: F, asset: Asset) -> Self {
        SolanaWatcher {
            fetcher,
            mint: config.mint_for(asset),
            asset,
            spl_token_program: config.spl_token_program,
            pinned_anchor: None,
            poh_policy: None,
        }
    }

    /// The asset whose mint this reader watches.
    pub fn asset(&self) -> Asset {
        self.asset
    }

    /// The mint this reader watches.
    pub fn mint(&self) -> [u8; 32] {
        self.mint
    }

    /// Pin the operator's governance-chosen [`WeakSubjectivityAnchor`] (+ the
    /// bounded PoH policy) — the trust root every [`Self::verify_consensus`]
    /// call verifies back to. Operator configuration, NEVER prover input: the
    /// stake table an attacker would need to control is *derived from bank
    /// state* and must reconstruct exactly this anchor's pinned root.
    pub fn with_pinned_anchor(
        mut self,
        anchor: WeakSubjectivityAnchor,
        poh_policy: Option<PohAnchorPolicy>,
    ) -> Self {
        self.pinned_anchor = Some(anchor);
        self.poh_policy = poh_policy;
        self
    }

    /// **Trustless upgrade**: verify a full [`HoldingProof`] (the holder's account +
    /// Solana Tower-BFT consensus evidence + bank-state stake provenance) against
    /// the watcher's **governance-pinned anchor**, returning a consensus-verified
    /// [`ProvenHolding`]. This is the bridge's ANCHORED verifier
    /// ([`prove_holding_consensus_anchored`]) — the stake table is derived from
    /// the proof's own bank-state provenance and trusted only back to the pinned
    /// anchor; it is NEVER a caller/prover-supplied table (a prover who supplies
    /// both the proof and a fabricated 1-key table is refused: the derived root
    /// cannot match the pinned anchor, and votes must be signed by the proven
    /// on-chain authorized voters).
    ///
    /// Fail closed: any verification failure — including no pinned anchor being
    /// configured ([`HoldingProofError::AnchorNotPinned`]) — returns `Err`,
    /// never a trusted holding.
    pub fn verify_consensus(
        &self,
        proof: &HoldingProof,
        require_poh: bool,
    ) -> Result<ProvenHolding, HoldingProofError> {
        let anchor = self
            .pinned_anchor
            .as_ref()
            .ok_or(HoldingProofError::AnchorNotPinned)?;
        prove_holding_consensus_anchored(
            proof,
            &self.mint,
            &self.spl_token_program,
            anchor,
            require_poh,
            self.poh_policy.as_ref(),
        )
    }
}

impl<F: AccountFetcher> SolanaWatcher<F> {
    /// **Read the deposit address's finalized token balance**, fail-closed.
    ///
    /// `Ok(None)` = the wallet has no token account for this mint yet (nothing landed —
    /// not an error). `Ok(Some(n))` = `n` atomic units, decoded from the real SPL layout
    /// and attributed to THIS wallet. Every forgery defense from proof-of-holdings is
    /// applied before the number is believed:
    ///
    /// 1. the account must be owned by the **SPL Token program**, else
    ///    [`HoldingProofError::NotSplTokenProgram`] — an attacker's own program can
    ///    write `mint ‖ wallet ‖ u64::MAX` into an account it controls;
    /// 2. the bytes must decode as an SPL token account
    ///    ([`HoldingProofError::NotTokenAccount`]);
    /// 3. the embedded **mint** must be the watched mint ([`HoldingProofError::WrongMint`]);
    /// 4. the embedded **token owner** must be the deposit wallet
    ///    ([`WatchError::WrongTokenOwner`]) — RPC *selection* is not trusted as proof of
    ///    attribution.
    ///
    /// This returns a BALANCE and is typed as one. It is deliberately not a payment: a
    /// balance total repeats after a sweep, so it is not an idempotency key and must
    /// never be turned into one (see the type doc). Credit flows through
    /// [`SignatureWatcher`].
    pub fn read_balance(&self, address: &DepositAddress) -> Result<Option<u64>, WatchError> {
        let fetched = match self.fetcher.fetch_token_account(address, &self.mint)? {
            Some(a) => a,
            None => return Ok(None),
        };
        // Fail closed: the account must be owned by the SPL Token program, or its
        // bytes are not an authoritative balance (the proof-of-holdings forgery
        // defense — an attacker's own program can write `mint ‖ wallet ‖ u64::MAX`).
        if fetched.owner_program != self.spl_token_program {
            return Err(WatchError::Holding(HoldingProofError::NotSplTokenProgram {
                owner_program: fetched.owner_program,
            }));
        }
        // Reuse the bridge's exact SPL layout decode.
        let (mint, owner, amount) = decode_spl_token_account(&fetched.data)
            .ok_or(WatchError::Holding(HoldingProofError::NotTokenAccount))?;
        if mint != self.mint {
            return Err(WatchError::Holding(HoldingProofError::WrongMint));
        }
        if owner != address.to_bytes() {
            return Err(WatchError::WrongTokenOwner {
                expected: address.to_bytes(),
                actual: owner,
            });
        }
        Ok(Some(amount))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The PRODUCTION credit path — one payment per TRANSACTION, keyed on the chain's
// own idempotency key.
// ─────────────────────────────────────────────────────────────────────────────

/// One finalized inbound token transfer, identified by the CHAIN's own idempotency key.
///
/// The three attribution fields (`mint`, `token_owner`, `token_program`) are the
/// fetcher's **claim** about the transfer, not a fact:
/// [`SignatureWatcher::poll`] re-checks each of them against operator config and
/// refuses fail-closed on a mismatch. That is the same discipline
/// [`SolanaWatcher::read_balance`] applies to `getTokenAccountsByOwner` — the RPC's
/// word is transport, not proof — carried onto the signature path so that the
/// forgery defenses live in the crate that credits money, not only in whichever
/// transport happens to be plugged in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedTransfer {
    /// The base58 transaction signature — restart-stable, sweep-stable, unique per
    /// transfer. THIS is the idempotency key.
    pub signature: String,
    /// The finalized slot it landed in (reported for operator diagnostics, and
    /// deliberately NEVER part of the idempotency key).
    pub slot: u64,
    /// Atomic units this transaction ADDED to the watched token account (`post − pre`).
    /// Always positive: a zero or negative delta is not a payment and is not reported.
    pub amount: u64,
    /// The mint the transferred units are denominated in, as claimed by the transport.
    pub mint: [u8; 32],
    /// The wallet that owns the credited token account, as claimed by the transport.
    pub token_owner: [u8; 32],
    /// The token program that owns the credited token account, as claimed by the
    /// transport.
    pub token_program: [u8; 32],
}

/// How many recent signatures a poll looks back over by default.
///
/// **This is a real bound, not a tuning knob.** The watcher holds no cursor, so a
/// transfer that has fallen out of this window is never credited. It is safe because a
/// per-user deposit address sees very few transactions and the window is re-read every
/// poll (default 60s); it stops being safe if one deposit address can receive more than
/// this many transfers between two polls. Raise it with
/// [`SignatureWatcher::with_history_limit`] before raising the poll interval.
pub const DEFAULT_TRANSFER_HISTORY_LIMIT: usize = 25;

/// The signature-history seam (the twin of [`AccountFetcher`], same injected-transport
/// shape). A production impl issues `getTokenAccountsByOwner` → `getSignaturesForAddress`
/// → `getTransaction` against the configured endpoint; tests supply a fixture returning
/// real-shaped [`ObservedTransfer`]s (including hostile ones).
pub trait TransferFetcher {
    /// Finalized transfers INTO `owner`'s token account for `mint`, most recent first,
    /// bounded by `limit`. An owner with no token account for `mint` has no transfers:
    /// that is `Ok(vec![])`, NOT an error.
    fn fetch_transfers(
        &self,
        owner: &DepositAddress,
        mint: &[u8; 32],
        limit: usize,
    ) -> Result<Vec<ObservedTransfer>, WatchError>;
}

/// **The production payment watcher.** One [`PaymentReceived`] per finalized inbound
/// transaction, with `reference = soltx:{signature}`.
///
/// # RESTART: nothing to declare, because nothing is held
///
/// This struct has **no in-RAM guard, no cursor, and no interior mutability at all** —
/// that is the point, and it is checkable by reading the field list. Every poll
/// re-observes the same window of chain history and mints the same references, so a
/// fresh process is indistinguishable from a long-running one. Deduplication is
/// answer **2 (REBUILD)** performed by the durable
/// [`CreditLedger`](crate::ledger::CreditLedger): `pay_processed` has
/// `reference TEXT PRIMARY KEY`, the reference is now the chain's own transaction
/// signature, and so the durable table finally recognises a repeat. No new store was
/// needed; only a key that the process does not invent.
///
/// # Fail-closed attribution
///
/// The transport's claims are re-checked here, per transfer, against operator config —
/// wrong token program, wrong mint, or a token owner that is not the polled deposit
/// wallet are each REFUSED (`Err`), never skipped. A refusal fails the whole poll on
/// purpose: the sweep counts a watcher error and retries, no money is credited, and the
/// operator sees it. Silently dropping a bad entry would let a transport that is
/// half-wrong look healthy.
pub struct SignatureWatcher<F: TransferFetcher> {
    fetcher: F,
    mint: [u8; 32],
    asset: Asset,
    spl_token_program: [u8; 32],
    history_limit: usize,
}

impl<F: TransferFetcher> SignatureWatcher<F> {
    /// Build from a [`PayConfig`] + a signature-history fetcher, watching the `$DREGG`
    /// mint (the default). Use [`SignatureWatcher::for_asset`] to watch USDC.
    pub fn new(config: &PayConfig, fetcher: F) -> Self {
        Self::for_asset(config, fetcher, Asset::Dregg)
    }

    /// Build a watcher for a specific `asset` — it watches that asset's mint
    /// ([`PayConfig::mint_for`]) and tags observed payments with it. Run one per
    /// accepted asset for the dual-asset stream.
    pub fn for_asset(config: &PayConfig, fetcher: F, asset: Asset) -> Self {
        SignatureWatcher {
            fetcher,
            mint: config.mint_for(asset),
            asset,
            spl_token_program: config.spl_token_program,
            history_limit: DEFAULT_TRANSFER_HISTORY_LIMIT,
        }
    }

    /// Override how far back each poll looks. See
    /// [`DEFAULT_TRANSFER_HISTORY_LIMIT`] for why this is a correctness bound.
    ///
    /// # Panics
    /// On `0` — a zero-length window observes nothing, which is a silent outage.
    pub fn with_history_limit(mut self, limit: usize) -> Self {
        assert!(limit >= 1, "history_limit must be >= 1");
        self.history_limit = limit;
        self
    }

    /// The asset this watcher tags payments with.
    pub fn asset(&self) -> Asset {
        self.asset
    }

    /// The mint this watcher watches.
    pub fn mint(&self) -> [u8; 32] {
        self.mint
    }

    /// How far back each poll looks.
    pub fn history_limit(&self) -> usize {
        self.history_limit
    }
}

impl<F: TransferFetcher> Watcher for SignatureWatcher<F> {
    fn poll(
        &self,
        user: &UserId,
        address: &DepositAddress,
    ) -> Result<Vec<PaymentReceived>, WatchError> {
        let transfers = self
            .fetcher
            .fetch_transfers(address, &self.mint, self.history_limit)?;
        let mut payments = Vec::with_capacity(transfers.len());
        for t in transfers {
            // Fail closed, in the same order and with the same errors the balance read
            // uses — the transport's claims are re-checked against operator config.
            if t.token_program != self.spl_token_program {
                return Err(WatchError::Holding(HoldingProofError::NotSplTokenProgram {
                    owner_program: t.token_program,
                }));
            }
            if t.mint != self.mint {
                return Err(WatchError::Holding(HoldingProofError::WrongMint));
            }
            if t.token_owner != address.to_bytes() {
                return Err(WatchError::WrongTokenOwner {
                    expected: address.to_bytes(),
                    actual: t.token_owner,
                });
            }
            // A zero-delta entry is not a payment. It is not an error either (a
            // transaction can touch the account without adding to it).
            if t.amount == 0 {
                continue;
            }
            payments.push(PaymentReceived {
                user: user.clone(),
                deposit_address: *address,
                asset: self.asset,
                // The CHAIN's key: the same transfer yields this same string from any
                // process, at any slot, before or after a sweep.
                reference: PaymentRef(format!("soltx:{}", t.signature)),
                amount: t.amount,
            });
        }
        Ok(payments)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SPL_TOKEN_PROGRAM_ID;

    #[test]
    fn mock_watcher_attributes_and_dedups() {
        let chain = MockChain::new();
        let watcher = MockWatcher::new(chain.clone());
        let alice = UserId::from("alice");
        let addr = DepositAddress([1u8; 32]);

        // No payment yet.
        assert!(watcher.poll(&alice, &addr).unwrap().is_empty());

        // Payment lands.
        chain.credit_onchain(&addr, 500);
        let got = watcher.poll(&alice, &addr).unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].amount, 500);
        assert_eq!(got[0].user, alice);

        // Re-poll with no new payment ⇒ nothing (watcher-level dedup).
        assert!(watcher.poll(&alice, &addr).unwrap().is_empty());
    }

    #[test]
    fn watcher_rebases_after_sweep_and_observes_the_next_deposit() {
        let chain = MockChain::new();
        let watcher = MockWatcher::new(chain.clone());
        let alice = UserId::from("alice");
        let addr = DepositAddress([1u8; 32]);
        let treasury = DepositAddress([2u8; 32]);

        chain.credit_onchain(&addr, 500);
        let first = watcher.poll(&alice, &addr).unwrap();
        assert_eq!(first[0].amount, 500);
        assert_eq!(chain.transfer_all(&addr, &treasury), 500);
        assert!(watcher.poll(&alice, &addr).unwrap().is_empty());
        chain.credit_onchain(&addr, 500);
        let second = watcher.poll(&alice, &addr).unwrap();
        assert_eq!(
            second[0].amount, 500,
            "a post-sweep deposit at the old 500-unit high-water mark is new money"
        );
        assert_ne!(second[0].reference, first[0].reference);
    }

    /// Build a real 165-byte SPL token account layout: `mint(32) ‖ owner(32) ‖
    /// amount_le(8) ‖ zero-pad`.
    fn spl_account_bytes(mint: &[u8; 32], owner: &[u8; 32], amount: u64) -> Vec<u8> {
        let mut data = vec![0u8; 165];
        data[0..32].copy_from_slice(mint);
        data[32..64].copy_from_slice(owner);
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        data
    }

    struct MockFetcher {
        acct: Option<FetchedAccount>,
    }
    impl AccountFetcher for MockFetcher {
        fn fetch_token_account(
            &self,
            _owner: &DepositAddress,
            _mint: &[u8; 32],
        ) -> Result<Option<FetchedAccount>, WatchError> {
            Ok(self.acct.clone())
        }
    }

    #[test]
    fn solana_watcher_decodes_real_spl_layout() {
        let mint = [9u8; 32];
        let owner = [1u8; 32];
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([2u8; 32]),
            100,
        );
        let fetcher = MockFetcher {
            acct: Some(FetchedAccount {
                data: spl_account_bytes(&mint, &owner, 750),
                owner_program: SPL_TOKEN_PROGRAM_ID,
                slot: 42,
            }),
        };
        let watcher = SolanaWatcher::new(&cfg, fetcher);
        let got = watcher.read_balance(&DepositAddress(owner)).unwrap();
        assert_eq!(got, Some(750));
    }

    #[test]
    fn solana_watcher_fails_closed_on_wrong_program_owner() {
        let mint = [9u8; 32];
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([2u8; 32]),
            100,
        );
        let fetcher = MockFetcher {
            acct: Some(FetchedAccount {
                data: spl_account_bytes(&mint, &[1u8; 32], u64::MAX),
                owner_program: [0xAAu8; 32], // attacker's own program, not SPL Token
                slot: 1,
            }),
        };
        let watcher = SolanaWatcher::new(&cfg, fetcher);
        let err = watcher
            .read_balance(&DepositAddress([1u8; 32]))
            .unwrap_err();
        assert!(matches!(
            err,
            WatchError::Holding(HoldingProofError::NotSplTokenProgram { .. })
        ));
    }

    #[test]
    fn solana_watcher_fails_closed_on_wrong_mint() {
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            [9u8; 32],
            DepositAddress([2u8; 32]),
            100,
        );
        let fetcher = MockFetcher {
            acct: Some(FetchedAccount {
                data: spl_account_bytes(&[0xEEu8; 32], &[1u8; 32], 100), // different mint
                owner_program: SPL_TOKEN_PROGRAM_ID,
                slot: 1,
            }),
        };
        let watcher = SolanaWatcher::new(&cfg, fetcher);
        let err = watcher
            .read_balance(&DepositAddress([1u8; 32]))
            .unwrap_err();
        assert!(matches!(
            err,
            WatchError::Holding(HoldingProofError::WrongMint)
        ));
    }

    // ── anchored consensus-verified holdings (the production trustless read) ──

    use dregg_bridge::solana_holdings::fixtures as hf;

    /// Build a watcher whose mint/spl-program match the anchored fixture, pinned
    /// to `anchor` (+ `policy`).
    fn anchored_watcher(
        mint: [u8; 32],
        anchor: WeakSubjectivityAnchor,
        policy: PohAnchorPolicy,
    ) -> SolanaWatcher<MockFetcher> {
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([2u8; 32]),
            100,
        );
        SolanaWatcher::new(&cfg, MockFetcher { acct: None })
            .with_pinned_anchor(anchor, Some(policy))
    }

    #[test]
    fn watcher_verify_consensus_accepts_honest_anchored_holding() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let (proof, anchor, policy) = hf::anchored_holding_with_cluster(
            &mint,
            &SPL_TOKEN_PROGRAM_ID,
            [0x42u8; 32],
            wallet,
            750,
            &[(11, 700), (12, 300)],
        );
        let watcher = anchored_watcher(mint, anchor, policy);
        let holding = watcher
            .verify_consensus(&proof, true)
            .expect("a genuine holding under the pinned anchor verifies");
        assert!(holding.is_consensus_proven());
        assert_eq!(holding.amount, 750);
        assert_eq!(holding.owner, wallet);
    }

    /// THE FORGERY through the PRODUCTION watcher entry: an attacker submits a
    /// holding proof built over a fabricated 1-key stake table (their key = 100%).
    /// The watcher pins the HONEST governance anchor, so the attacker's derived
    /// distribution cannot match it — `verify_consensus` REJECTS, no weight.
    #[test]
    fn watcher_verify_consensus_rejects_attacker_one_key_stake_table() {
        let mint = [9u8; 32];
        // The honest governance-pinned anchor (700/300 cluster).
        let (_honest, honest_anchor, honest_policy) = hf::anchored_holding_with_cluster(
            &mint,
            &SPL_TOKEN_PROGRAM_ID,
            [0x42u8; 32],
            [1u8; 32],
            1,
            &[(11, 700), (12, 300)],
        );
        // The attacker's proof: a 1-key (100%-self-stake) distribution, forged
        // huge balance.
        let (evil, _evil_anchor, evil_policy) = hf::anchored_holding_with_cluster(
            &mint,
            &SPL_TOKEN_PROGRAM_ID,
            [0x42u8; 32],
            [1u8; 32],
            u64::MAX,
            &[(66, 1_000)],
        );
        let watcher = anchored_watcher(mint, honest_anchor, honest_policy);
        // The watcher pins the honest anchor; the attacker's policy is theirs.
        let _ = evil_policy;
        let err = watcher
            .verify_consensus(&evil, true)
            .expect_err("an attacker-supplied 1-key stake table must not mint weight");
        assert!(
            matches!(
                err,
                HoldingProofError::Provenance(
                    dregg_bridge::solana_provenance::ProvenanceError::AnchorRootMismatch { .. }
                )
            ),
            "refused at the anchor-root binding, got: {err:?}"
        );
    }

    /// With no pinned anchor configured, the production entry fails closed —
    /// there is NO caller-supplied-table fallback.
    #[test]
    fn watcher_verify_consensus_without_pinned_anchor_fails_closed() {
        let mint = [9u8; 32];
        let (proof, _anchor, _policy) = hf::anchored_holding_with_cluster(
            &mint,
            &SPL_TOKEN_PROGRAM_ID,
            [0x42u8; 32],
            [1u8; 32],
            10,
            &[(11, 700), (12, 300)],
        );
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([2u8; 32]),
            100,
        );
        let watcher = SolanaWatcher::new(&cfg, MockFetcher { acct: None });
        assert_eq!(
            watcher.verify_consensus(&proof, true).unwrap_err(),
            HoldingProofError::AnchorNotPinned
        );
    }

    #[test]
    fn solana_watcher_refuses_rpc_account_owned_by_another_wallet() {
        let mint = [9u8; 32];
        let victim = [1u8; 32];
        let attacker = [2u8; 32];
        let cfg = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([3u8; 32]),
            100,
        );
        let watcher = SolanaWatcher::new(
            &cfg,
            MockFetcher {
                acct: Some(FetchedAccount {
                    data: spl_account_bytes(&mint, &attacker, 50_000_000),
                    owner_program: SPL_TOKEN_PROGRAM_ID,
                    slot: 9,
                }),
            },
        );
        assert!(matches!(
            watcher.read_balance(&DepositAddress(victim)),
            Err(WatchError::WrongTokenOwner { expected, actual })
                if expected == victim && actual == attacker
        ));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The PRODUCTION credit path: SignatureWatcher over a fixture chain.
    // ─────────────────────────────────────────────────────────────────────────

    /// A fixture signature-history transport. `slot_clock` advances on every fetch —
    /// exactly what a real RPC does, and exactly what made the old balance-total
    /// reference fresh on every poll. The `SignatureWatcher` reference must be immune
    /// to it.
    struct FixtureTransfers {
        transfers: Vec<ObservedTransfer>,
        /// SHARED with every other fetcher built over the same fixture chain, because a
        /// real cluster's slot clock does not reset when our process does. A per-fetcher
        /// clock would let two "restarted" watchers see the same slot by accident and
        /// silently pass a restart test that a slot-bearing key should fail.
        slot_clock: Arc<Mutex<u64>>,
        seen_limit: Mutex<Option<usize>>,
    }

    impl FixtureTransfers {
        fn new(transfers: Vec<ObservedTransfer>) -> Self {
            Self::on_clock(transfers, Arc::new(Mutex::new(1_000)))
        }

        /// A fetcher over a clock that outlives the process — what "reconnecting to the
        /// same cluster after a restart" actually looks like.
        fn on_clock(transfers: Vec<ObservedTransfer>, slot_clock: Arc<Mutex<u64>>) -> Self {
            FixtureTransfers {
                transfers,
                slot_clock,
                seen_limit: Mutex::new(None),
            }
        }
    }

    impl TransferFetcher for FixtureTransfers {
        fn fetch_transfers(
            &self,
            _owner: &DepositAddress,
            _mint: &[u8; 32],
            limit: usize,
        ) -> Result<Vec<ObservedTransfer>, WatchError> {
            *self.seen_limit.lock().unwrap() = Some(limit);
            let mut clock = self.slot_clock.lock().unwrap();
            *clock += 1;
            let now = *clock;
            Ok(self
                .transfers
                .iter()
                .cloned()
                .map(|mut t| {
                    // The reported slot moves; the signature does not.
                    t.slot = now;
                    t
                })
                .collect())
        }
    }

    fn transfer(sig: &str, amount: u64, owner: [u8; 32], mint: [u8; 32]) -> ObservedTransfer {
        ObservedTransfer {
            signature: sig.to_string(),
            slot: 0,
            amount,
            mint,
            token_owner: owner,
            token_program: SPL_TOKEN_PROGRAM_ID,
        }
    }

    fn sig_cfg(mint: [u8; 32]) -> PayConfig {
        PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            mint,
            DepositAddress([2u8; 32]),
            100,
        )
    }

    /// One transfer ⇒ one payment, keyed on the SIGNATURE — and the reference is
    /// identical across polls even though the reported slot advances between them.
    /// That stability is the whole fix: it is what lets a durable table recognise a
    /// repeat.
    #[test]
    fn signature_watcher_reference_is_the_transaction_signature_and_is_slot_stable() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let cfg = sig_cfg(mint);
        let watcher = SignatureWatcher::new(
            &cfg,
            FixtureTransfers::new(vec![transfer("SiGoNe", 750, wallet, mint)]),
        );
        let alice = UserId::from("alice");
        let addr = DepositAddress(wallet);

        let first = watcher.poll(&alice, &addr).unwrap();
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].amount, 750);
        assert_eq!(first[0].user, alice);
        assert_eq!(first[0].reference, PaymentRef("soltx:SiGoNe".to_string()));

        // Re-poll: the transport reports a NEW slot, and the reference does not move.
        let second = watcher.poll(&alice, &addr).unwrap();
        assert_eq!(
            second[0].reference, first[0].reference,
            "the reference must be a property of the chain, not of the poll"
        );
        assert!(
            !first[0].reference.0.contains("1001") && !first[0].reference.0.contains("1002"),
            "the slot must never appear in the idempotency key: {}",
            first[0].reference
        );
    }

    /// Several transfers in the window ⇒ one payment each, each with its own key. A
    /// zero-delta entry is skipped (a transaction can touch the account without paying
    /// it), and the configured history limit is what reaches the transport.
    #[test]
    fn signature_watcher_emits_one_payment_per_transfer_and_skips_zero_deltas() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let cfg = sig_cfg(mint);
        let fixture = FixtureTransfers::new(vec![
            transfer("SigA", 500, wallet, mint),
            transfer("SigZero", 0, wallet, mint),
            transfer("SigB", 250, wallet, mint),
        ]);
        let watcher = SignatureWatcher::new(&cfg, fixture).with_history_limit(7);
        let got = watcher
            .poll(&UserId::from("alice"), &DepositAddress(wallet))
            .unwrap();
        assert_eq!(got.len(), 2, "the zero-delta entry is not a payment");
        assert_eq!(got[0].reference, PaymentRef("soltx:SigA".to_string()));
        assert_eq!(got[0].amount, 500);
        assert_eq!(got[1].reference, PaymentRef("soltx:SigB".to_string()));
        assert_eq!(got[1].amount, 250);
        assert_eq!(watcher.history_limit(), 7);
    }

    /// **THE RESTART DECISION, at the watcher layer.** Dropping the watcher and
    /// building a new one from the same config over the same chain yields the SAME
    /// references — so a durable ledger recognises the repeat. (The ledger-level
    /// assertion, on the balance, is `tests/watcher_restart_semantics.rs`.)
    #[test]
    fn signature_watcher_is_process_stateless_across_a_restart() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let cfg = sig_cfg(mint);
        let alice = UserId::from("alice");
        let addr = DepositAddress(wallet);

        // The cluster's slot clock outlives our process, so both boots share it.
        let clock = Arc::new(Mutex::new(1_000u64));
        let boot = || {
            SignatureWatcher::new(
                &cfg,
                FixtureTransfers::on_clock(
                    vec![transfer("SigRestart", 500, wallet, mint)],
                    Arc::clone(&clock),
                ),
            )
        };
        let before = {
            let watcher = boot();
            watcher.poll(&alice, &addr).unwrap()
        }; // ← dropped. THIS IS THE RESTART.
        let watcher = boot();
        let after = watcher.poll(&alice, &addr).unwrap();
        assert_ne!(
            *clock.lock().unwrap(),
            1_001,
            "the cluster clock must have moved between the two polls, or this test \
             cannot see a slot leaking into the key"
        );
        assert_eq!(
            before
                .iter()
                .map(|p| p.reference.clone())
                .collect::<Vec<_>>(),
            after
                .iter()
                .map(|p| p.reference.clone())
                .collect::<Vec<_>>(),
            "a brand-new watcher must mint the SAME keys for the same chain state"
        );
    }

    // ── AUTHORITY: the fail-closed forgery defenses on the signature path ────

    /// A transport claiming a transfer on an account owned by an attacker's own
    /// program is REFUSED — the same defense
    /// [`SolanaWatcher::read_balance`] applies to a fetched account.
    #[test]
    fn signature_watcher_fails_closed_on_wrong_program_owner() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let cfg = sig_cfg(mint);
        let mut evil = transfer("SigForged", u64::MAX, wallet, mint);
        evil.token_program = [0xAAu8; 32]; // attacker's own program, not SPL Token
        let watcher = SignatureWatcher::new(&cfg, FixtureTransfers::new(vec![evil]));
        let err = watcher
            .poll(&UserId::from("mallory"), &DepositAddress(wallet))
            .unwrap_err();
        assert!(
            matches!(
                err,
                WatchError::Holding(HoldingProofError::NotSplTokenProgram { .. })
            ),
            "expected NotSplTokenProgram, got {err:?}"
        );
    }

    /// A transfer denominated in a different mint is REFUSED — an unwatched token is
    /// never credited as `$DREGG`.
    #[test]
    fn signature_watcher_fails_closed_on_wrong_mint() {
        let mint = [9u8; 32];
        let wallet = [1u8; 32];
        let cfg = sig_cfg(mint);
        let watcher = SignatureWatcher::new(
            &cfg,
            FixtureTransfers::new(vec![transfer("SigWrongMint", 100, wallet, [0xEEu8; 32])]),
        );
        let err = watcher
            .poll(&UserId::from("alice"), &DepositAddress(wallet))
            .unwrap_err();
        assert!(
            matches!(err, WatchError::Holding(HoldingProofError::WrongMint)),
            "expected WrongMint, got {err:?}"
        );
    }

    /// A transfer into SOMEONE ELSE's token account is REFUSED — transport selection
    /// is not proof of attribution, so a victim is never credited with an attacker's
    /// (or anyone's) balance.
    #[test]
    fn signature_watcher_refuses_a_transfer_owned_by_another_wallet() {
        let mint = [9u8; 32];
        let victim = [1u8; 32];
        let attacker = [2u8; 32];
        let cfg = sig_cfg(mint);
        let watcher = SignatureWatcher::new(
            &cfg,
            FixtureTransfers::new(vec![transfer("SigOther", 50_000_000, attacker, mint)]),
        );
        assert!(
            matches!(
                watcher.poll(&UserId::from("victim"), &DepositAddress(victim)),
                Err(WatchError::WrongTokenOwner { expected, actual })
                    if expected == victim && actual == attacker
            ),
            "a transfer to another wallet must not credit the polled user"
        );
    }
}
