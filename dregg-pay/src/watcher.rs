//! [`Watcher`] — detect inbound `$DREGG` payments to a user's deposit address.
//!
//! Two impls behind one trait:
//! * [`MockWatcher`] over a [`MockChain`] — a simulated devnet ledger, fully driven
//!   in tests (no network, no funds).
//! * [`SolanaWatcher`] — the REAL path. It reuses the bridge crate's
//!   [`decode_spl_token_account`](dregg_bridge::solana_holdings::decode_spl_token_account)
//!   (the exact SPL token-account layout decode the proof-of-holdings verifier uses)
//!   and, for a trustless read, the bridge's **anchored** verifier
//!   [`prove_holding_consensus_anchored`](dregg_bridge::solana_holdings::prove_holding_consensus_anchored)
//!   (authorized-voter-bound ≥ 2/3 supermajority over a stake table DERIVED from
//!   bank state, trusted only back to the operator's governance-pinned
//!   [`WeakSubjectivityAnchor`] — never a caller-supplied stake table, which an
//!   attacker could fabricate). The RPC is an injected seam ([`AccountFetcher`]) —
//!   the same shape bridge uses for its Solana transport — so tests exercise the
//!   real decode/attribution/fail-closed logic without ever hitting mainnet.
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
/// [`CreditLedger`](crate::ledger::CreditLedger) dedups on. For the real watcher
/// this binds the deposit address + finalized slot + observed balance; for the mock
/// it binds the address + the new on-chain total.
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

/// Detect inbound payments to a user's deposit address. Polling is idempotent at
/// the watcher layer (it only reports balance it has not already reported) AND at
/// the ledger layer (by [`PaymentReceived::reference`]) — belt and suspenders.
pub trait Watcher {
    /// Poll for new payments to `address` (owned by `user`). Returns the payments
    /// observed since the last poll (empty if none).
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
pub struct MockWatcher {
    chain: MockChain,
    asset: Asset,
    last_seen: Mutex<HashMap<[u8; 32], u64>>,
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

/// The real Solana watcher. Reuses the bridge's SPL decode for the balance read and
/// the bridge's consensus verifier for a trustless read; fail-closed on a wrong
/// mint / non-SPL-owned account (the exact forgery defense from proof-of-holdings).
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
    last_seen: Mutex<HashMap<[u8; 32], u64>>,
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
            last_seen: Mutex::new(HashMap::new()),
        }
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

impl<F: AccountFetcher> Watcher for SolanaWatcher<F> {
    fn poll(
        &self,
        user: &UserId,
        address: &DepositAddress,
    ) -> Result<Vec<PaymentReceived>, WatchError> {
        let fetched = match self.fetcher.fetch_token_account(address, &self.mint)? {
            Some(a) => a,
            None => return Ok(vec![]),
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

        let mut seen = self.last_seen.lock().unwrap();
        let prev = *seen.get(&address.to_bytes()).unwrap_or(&0);
        if amount < prev {
            seen.insert(address.to_bytes(), amount);
            return Ok(vec![]);
        }
        if amount == prev {
            return Ok(vec![]);
        }
        let delta = amount - prev;
        seen.insert(address.to_bytes(), amount);
        let reference = PaymentRef(format!(
            "sol:{}:{}:{amount}",
            address.to_base58(),
            fetched.slot
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
        let got = watcher
            .poll(&UserId::from("alice"), &DepositAddress(owner))
            .unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].amount, 750);
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
            .poll(&UserId::from("mallory"), &DepositAddress([1u8; 32]))
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
            .poll(&UserId::from("alice"), &DepositAddress([1u8; 32]))
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
            watcher.poll(&UserId::from("victim"), &DepositAddress(victim)),
            Err(WatchError::WrongTokenOwner { expected, actual })
                if expected == victim && actual == attacker
        ));
    }
}
