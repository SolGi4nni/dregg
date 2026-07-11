//! [`Sweeper`] — move a deposit address's balance to the treasury.
//!
//! # Custody
//!
//! The sweeper is THE custody point of the "B" model. To move funds off a deposit
//! address it must SIGN with that address's key, which it derives from the HD
//! [`Seed`](crate::config::Seed). Whoever runs the sweeper holds the seed and can
//! move every user's deposit. This is named, not hidden — it is the honest cost of
//! the custodial HD-deposit model, and the reason the endgame is a
//! dregg-protocol-native settlement where no operator holds user funds.
//!
//! Two impls behind one trait:
//! * [`MockSweeper`] over a [`MockChain`] — moves simulated balances, fully driven.
//! * [`SolanaSweeper`] — the REAL path: reads the deposit balance via the bridge
//!   SPL decode, derives the custody key, and submits a signed SPL transfer to the
//!   treasury through an injected [`TxSubmitter`] (the operator's secured signer).

use ed25519_dalek::SigningKey;

use crate::config::{DepositAddress, PayConfig, UserId};
use crate::hd::{DepositAddressProvider, HdDeposit};
use crate::watcher::{AccountFetcher, WatchError};
use dregg_bridge::solana_holdings::{HoldingProofError, decode_spl_token_account};

/// The result of a sweep.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SweepOutcome {
    /// The user whose deposit was swept.
    pub user: UserId,
    /// The deposit address swept from.
    pub from: DepositAddress,
    /// The treasury address swept to.
    pub to: DepositAddress,
    /// The amount moved, in atomic `$DREGG` units (0 if the address was empty).
    pub amount: u64,
    /// A reference for the sweep (the tx signature on the real path; a synthetic id
    /// on the mock path). `None` when nothing was moved.
    pub reference: Option<String>,
}

/// Why a sweep failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SweepError {
    /// The derived custody key's public key does not match the deposit address —
    /// a derivation/seed mismatch. Refused (never sign for the wrong address).
    KeyMismatch,
    /// Reading the deposit balance failed / was refused (fail closed).
    Read(WatchError),
    /// The transaction submitter failed.
    Submit(String),
}

impl std::fmt::Display for SweepError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SweepError::KeyMismatch => {
                write!(f, "derived custody key does not match deposit address")
            }
            SweepError::Read(e) => write!(f, "deposit balance read refused: {e}"),
            SweepError::Submit(e) => write!(f, "sweep transaction submit failed: {e}"),
        }
    }
}

impl std::error::Error for SweepError {}

/// Sweep a deposit address's full balance to the treasury.
pub trait Sweeper {
    /// Sweep everything on `address` (owned by `user`) to the treasury.
    fn sweep(&self, user: &UserId, address: &DepositAddress) -> Result<SweepOutcome, SweepError>;
}

// ─────────────────────────────────────────────────────────────────────────────
// MOCK / devnet path
// ─────────────────────────────────────────────────────────────────────────────

use crate::watcher::MockChain;

/// The mock sweeper: moves a [`MockChain`] balance to the treasury.
pub struct MockSweeper {
    chain: MockChain,
    treasury: DepositAddress,
}

impl MockSweeper {
    /// A sweeper over `chain` targeting `treasury`.
    pub fn new(chain: MockChain, treasury: DepositAddress) -> Self {
        MockSweeper { chain, treasury }
    }
}

impl Sweeper for MockSweeper {
    fn sweep(&self, user: &UserId, address: &DepositAddress) -> Result<SweepOutcome, SweepError> {
        let amount = self.chain.transfer_all(address, &self.treasury);
        let reference = if amount > 0 {
            Some(format!("mock-sweep:{}:{amount}", address.to_base58()))
        } else {
            None
        };
        Ok(SweepOutcome {
            user: user.clone(),
            from: *address,
            to: self.treasury,
            amount,
            reference,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// REAL Solana path
// ─────────────────────────────────────────────────────────────────────────────

/// A signed sweep request handed to the [`TxSubmitter`]. Carries the CUSTODY
/// signing key for `from` (the derived deposit key) — the submitter needs it to
/// sign the real Solana transaction (whose message includes a recent blockhash the
/// submitter fetches). The submitter is therefore part of the trusted custody
/// boundary; run it in the operator's secured signer.
pub struct SweepRequest<'a> {
    /// The user whose deposit is being swept.
    pub user: &'a UserId,
    /// The deposit address (source).
    pub from: DepositAddress,
    /// The treasury address (destination).
    pub to: DepositAddress,
    /// The `$DREGG` mint being transferred.
    pub mint: [u8; 32],
    /// The amount to transfer, in atomic units.
    pub amount: u64,
    /// The custody signing key for `from` (derived from the seed).
    pub signing_key: &'a SigningKey,
}

/// The transaction-submit seam. A production impl assembles the real SPL transfer
/// instruction (source ATA → treasury ATA, authority = the deposit key), signs the
/// transaction message with [`SweepRequest::signing_key`], and submits it to the
/// configured RPC, returning the transaction signature. Tests supply a mock
/// submitter (no funds, no network) that still exercises real signing.
pub trait TxSubmitter {
    /// Submit the sweep, returning the transaction signature.
    fn submit(&self, request: &SweepRequest) -> Result<String, SweepError>;
}

/// The real Solana sweeper: reads the deposit balance via the bridge SPL decode,
/// derives the custody key from the seed, and submits a signed SPL transfer to the
/// treasury through the injected [`TxSubmitter`].
pub struct SolanaSweeper<F: AccountFetcher, T: TxSubmitter> {
    hd: HdDeposit,
    treasury: DepositAddress,
    mint: [u8; 32],
    spl_token_program: [u8; 32],
    fetcher: F,
    submitter: T,
}

impl<F: AccountFetcher, T: TxSubmitter> SolanaSweeper<F, T> {
    /// Build from a [`PayConfig`] + an RPC fetcher + a tx submitter.
    pub fn new(config: &PayConfig, fetcher: F, submitter: T) -> Self {
        SolanaSweeper {
            hd: HdDeposit::new(config),
            treasury: config.treasury,
            mint: config.mint,
            spl_token_program: config.spl_token_program,
            fetcher,
            submitter,
        }
    }
}

impl<F: AccountFetcher, T: TxSubmitter> Sweeper for SolanaSweeper<F, T> {
    fn sweep(&self, user: &UserId, address: &DepositAddress) -> Result<SweepOutcome, SweepError> {
        // 1. Read the current deposit balance (reuse the bridge SPL decode; fail
        //    closed on wrong program owner / mint).
        let fetched = self
            .fetcher
            .fetch_token_account(address, &self.mint)
            .map_err(SweepError::Read)?;
        let amount = match fetched {
            None => 0,
            Some(a) => {
                if a.owner_program != self.spl_token_program {
                    return Err(SweepError::Read(WatchError::Holding(
                        HoldingProofError::NotSplTokenProgram {
                            owner_program: a.owner_program,
                        },
                    )));
                }
                let (mint, _owner, amt) = decode_spl_token_account(&a.data).ok_or(
                    SweepError::Read(WatchError::Holding(HoldingProofError::NotTokenAccount)),
                )?;
                if mint != self.mint {
                    return Err(SweepError::Read(WatchError::Holding(
                        HoldingProofError::WrongMint,
                    )));
                }
                amt
            }
        };

        if amount == 0 {
            return Ok(SweepOutcome {
                user: user.clone(),
                from: *address,
                to: self.treasury,
                amount: 0,
                reference: None,
            });
        }

        // 2. Derive the custody key and CHECK it controls this address.
        let signing_key = self.hd.signing_key(user);
        if &signing_key.verifying_key().to_bytes() != &address.to_bytes()
            || self.hd.deposit_address(user) != *address
        {
            return Err(SweepError::KeyMismatch);
        }

        // 3. Sign + submit the SPL transfer to the treasury.
        let request = SweepRequest {
            user,
            from: *address,
            to: self.treasury,
            mint: self.mint,
            amount,
            signing_key: &signing_key,
        };
        let signature = self.submitter.submit(&request)?;
        Ok(SweepOutcome {
            user: user.clone(),
            from: *address,
            to: self.treasury,
            amount,
            reference: Some(signature),
        })
    }
}

/// The canonical bytes a sweep signs when the submitter is a bare signer (a devnet
/// / test convenience). A PRODUCTION submitter signs the assembled Solana
/// transaction message instead; this is the minimal message that binds
/// `from ‖ to ‖ mint ‖ amount` for the driven test's custody proof.
pub fn sweep_message(request: &SweepRequest) -> Vec<u8> {
    let mut msg = Vec::with_capacity(32 * 3 + 8 + 16);
    msg.extend_from_slice(b"dregg-pay/sweep/v1");
    msg.extend_from_slice(&request.from.to_bytes());
    msg.extend_from_slice(&request.to.to_bytes());
    msg.extend_from_slice(&request.mint);
    msg.extend_from_slice(&request.amount.to_le_bytes());
    msg
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SPL_TOKEN_PROGRAM_ID;
    use crate::watcher::FetchedAccount;
    use ed25519_dalek::{Signer, Verifier};

    #[test]
    fn mock_sweeper_moves_balance_to_treasury() {
        let chain = MockChain::new();
        let treasury = DepositAddress([0xEEu8; 32]);
        let alice_addr = DepositAddress([1u8; 32]);
        chain.credit_onchain(&alice_addr, 500);

        let sweeper = MockSweeper::new(chain.clone(), treasury);
        let out = sweeper.sweep(&UserId::from("alice"), &alice_addr).unwrap();
        assert_eq!(out.amount, 500);
        assert_eq!(out.to, treasury);
        assert_eq!(chain.balance(&alice_addr), 0);
        assert_eq!(chain.balance(&treasury), 500);

        // Sweeping an empty address moves nothing.
        let out2 = sweeper.sweep(&UserId::from("alice"), &alice_addr).unwrap();
        assert_eq!(out2.amount, 0);
        assert_eq!(out2.reference, None);
    }

    struct OneAccountFetcher {
        data: Vec<u8>,
    }
    impl AccountFetcher for OneAccountFetcher {
        fn fetch_token_account(
            &self,
            _owner: &DepositAddress,
            _mint: &[u8; 32],
        ) -> Result<Option<FetchedAccount>, WatchError> {
            Ok(Some(FetchedAccount {
                data: self.data.clone(),
                owner_program: SPL_TOKEN_PROGRAM_ID,
                slot: 7,
            }))
        }
    }

    /// A test submitter that performs REAL ed25519 signing with the custody key and
    /// verifies it — proving the derived key flows correctly. No funds, no network.
    struct SigningSubmitter;
    impl TxSubmitter for SigningSubmitter {
        fn submit(&self, request: &SweepRequest) -> Result<String, SweepError> {
            let msg = sweep_message(request);
            let sig = request.signing_key.sign(&msg);
            request
                .signing_key
                .verifying_key()
                .verify(&msg, &sig)
                .map_err(|_| SweepError::Submit("signature failed to verify".into()))?;
            Ok(bs58::encode(sig.to_bytes()).into_string())
        }
    }

    #[test]
    fn solana_sweeper_signs_with_derived_custody_key() {
        // Config: mock mint, seed derives alice's deposit key.
        let seed = *b"dregg-pay throwaway sweeper seed 00000000";
        let mint = [9u8; 32];
        let cfg = PayConfig::devnet_mock(seed, mint, DepositAddress([0xEEu8; 32]), 100);
        let hd = HdDeposit::new(&cfg);
        let alice = UserId::from("alice");
        let alice_addr = hd.deposit_address(&alice);

        // The fetched account is owned BY alice's derived address, holding 750.
        let mut data = vec![0u8; 165];
        data[0..32].copy_from_slice(&mint);
        data[32..64].copy_from_slice(&alice_addr.to_bytes());
        data[64..72].copy_from_slice(&750u64.to_le_bytes());

        let sweeper = SolanaSweeper::new(&cfg, OneAccountFetcher { data }, SigningSubmitter);
        let out = sweeper.sweep(&alice, &alice_addr).unwrap();
        assert_eq!(out.amount, 750);
        assert!(out.reference.is_some());
    }
}
