//! Non-custodial **proof-of-holdings** — the dreggic alternative to lock-and-mirror.
//!
//! `solana_mirror` / `solana-lock` implement the *lock* path: a holder moves their
//! `$DREGG` into a vault and dregg mirrors it in. That is legitimate for *importing
//! spendable value* or posting a *slashable bond* — the cases where an escrow
//! genuinely prevents double-spend — but it is the WRONG mechanism for
//! participation. To *vote* or to have *weight*, no one should have to surrender
//! custody. As ember put it: "why should you need to move your DREGG into a special
//! wrap bridge wallet that isn't even your own custody, just to be able to vote with
//! it? there is no reason for this except bad system design."
//!
//! So this module does the full-client thing instead. dregg is already a Solana
//! light client (`solana_consensus`: stake-weighted ≥2/3 Ed25519 supermajority on a
//! bank hash + accounts-Merkle inclusion). That verifier reads ANY finalized account
//! — so we point it at the holder's OWN SPL token account (never a vault), decode the
//! balance, and PROVE "wallet W holds `amount` of mint M at finalized slot S". The
//! holder keeps custody; the tokens never move; dregg grants governance weight /
//! eligibility by proof.
//!
//! This is the "proof-of-holding → eligibility/weight" primitive named as the missing
//! spine in `docs/FINDING-chain-participation-census.md` §5.
//!
//! # Trust
//!
//! A [`ProvenHolding`] carries its [`LockProofTrust`]: only
//! [`LockProofTrust::ConsensusVerified`] (a real supermajority over a finalized bank
//! hash) is trustless. A [`LockProofTrust::StructureOnly`] holding (a plain-RPC read)
//! is NOT proof — the weight-binding layer must refuse to grant weight from it, the
//! same fail-closed rule the mint gate uses.

use crate::solana_trustless::LockProofTrust;

/// The SPL Token `Account` on-chain layout offsets (spl-token `state::Account`,
/// 165 bytes): `mint(32) ‖ owner(32) ‖ amount_le(8) ‖ …`. We read only the three
/// fields proof-of-holdings needs; the account's inclusion under a consensus-verified
/// bank hash is what makes those three bytes trustworthy.
pub const SPL_ACCOUNT_LEN: usize = 165;
/// `mint` pubkey occupies bytes `[0, 32)`.
pub const SPL_MINT_OFFSET: usize = 0;
/// `owner` pubkey (the wallet that controls the account) occupies bytes `[32, 64)`.
pub const SPL_OWNER_OFFSET: usize = 32;
/// `amount` (u64 little-endian) occupies bytes `[64, 72)`.
pub const SPL_AMOUNT_OFFSET: usize = 64;

/// Decode the three proof-of-holdings fields from a finalized SPL token account's
/// `data`: `(mint, owner, amount)`. Returns `None` unless the data is at least a full
/// SPL `Account` (165 bytes) — a shorter blob is not a token account and is refused
/// (fail closed). The account's authenticity comes from the caller having verified its
/// inclusion under a consensus-verified bank hash; this function only reads the layout.
pub fn decode_spl_token_account(data: &[u8]) -> Option<([u8; 32], [u8; 32], u64)> {
    if data.len() < SPL_ACCOUNT_LEN {
        return None;
    }
    let mut mint = [0u8; 32];
    mint.copy_from_slice(&data[SPL_MINT_OFFSET..SPL_MINT_OFFSET + 32]);
    let mut owner = [0u8; 32];
    owner.copy_from_slice(&data[SPL_OWNER_OFFSET..SPL_OWNER_OFFSET + 32]);
    let mut amt = [0u8; 8];
    amt.copy_from_slice(&data[SPL_AMOUNT_OFFSET..SPL_AMOUNT_OFFSET + 8]);
    Some((mint, owner, u64::from_le_bytes(amt)))
}

/// A proven, NON-CUSTODIAL holding: at finalized `slot`, the SPL token account
/// `token_account` (controlled by `owner`) held `amount` of `mint`. The holder never
/// moved anything — this is a snapshot proven over their own account.
///
/// Produced by the consensus-verified observe path (the verifier body is
/// `prove_holding_consensus`, built alongside this type). Consumed by the
/// weight-binding layer, which grants governance weight / eligibility ONLY when
/// `trust` is [`LockProofTrust::ConsensusVerified`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenHolding {
    /// The holder's SPL token account pubkey (their own custody, not a vault).
    pub token_account: [u8; 32],
    /// The wallet that controls the account (SPL `Account.owner`).
    pub owner: [u8; 32],
    /// The SPL mint proven held (`$DREGG` on Solana).
    pub mint: [u8; 32],
    /// The balance proven at `slot`, in atomic units.
    pub amount: u64,
    /// The finalized Solana slot the holding was proven at (the snapshot point).
    pub slot: u64,
    /// How trusted the observation is. Weight is granted ONLY for
    /// [`LockProofTrust::ConsensusVerified`]; [`LockProofTrust::StructureOnly`] is a
    /// plain-RPC read and MUST NOT grant weight (fail closed).
    pub trust: LockProofTrust,
}

impl ProvenHolding {
    /// True iff this holding is backed by a real stake-weighted supermajority over a
    /// finalized bank hash — the only state from which governance weight may be
    /// granted. A `StructureOnly` (RPC-echo) holding returns `false`.
    pub fn is_consensus_proven(&self) -> bool {
        matches!(self.trust, LockProofTrust::ConsensusVerified)
    }
}

use crate::solana_consensus::{
    EpochStakeTable, VoteSetError, verify_poh_segment, verify_supermajority,
};
use crate::solana_trustless::ConsensusEvidence;
use crate::solana_wire::{
    AccountsInclusionProof16, solana_account_hash, verify_account_inclusion_16ary,
};

/// The holder's OWN finalized Solana account — the thing proof-of-holdings observes,
/// with **no vault, no lock, no transfer**. It is a plain SPL token account the holder
/// controls; its `data` is the real 165-byte SPL `Account` layout (`mint ‖ owner ‖
/// amount ‖ …`). The `inclusion` proof opens this account's per-account hash into a
/// finalized accounts hash (the SAME 16-ary fan-out the mint path proves the vault with
/// — [`crate::solana_wire::verify_account_inclusion_16ary`]).
///
/// `owner_program` is the account's on-chain owner *program* — and it MUST be the
/// SPL Token program, or the 165-byte `data` is not an authoritative balance. This is
/// a program-*owner* binding, NOT a custody surrender: every real SPL token account is
/// owned by the SPL Token program, and the holder still controls it via SPL
/// `Account.owner` (that owner is the wallet that gets the weight). The distinction
/// from the vault: the vault must be owned by *our lock program* (custodial — the
/// holder's tokens moved into it); here the account is owned by the *SPL Token program*
/// (non-custodial — every wallet's own token account already is). Drop this check and
/// an attacker forges any balance from an account under their own program — the exact
/// attack `solana_trustless.rs` defends the vault against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoldingAccount {
    /// The holder's SPL token account pubkey (their own custody).
    pub token_account: [u8; 32],
    /// The account's lamports (must be nonzero; a zero-lamport account is absent from
    /// the accounts hash and cannot be proven included).
    pub lamports: u64,
    /// The account's on-chain owner *program* (the SPL Token program), used to
    /// recompute the mainnet per-account hash. This is NOT the token holder.
    pub owner_program: [u8; 32],
    /// Whether the account is executable (part of the per-account hash preimage).
    pub executable: bool,
    /// The account's rent epoch (part of the per-account hash preimage).
    pub rent_epoch: u64,
    /// The account's `data` — the real SPL `Account` layout decoded by
    /// [`decode_spl_token_account`].
    pub data: Vec<u8>,
    /// The 16-ary fan-out inclusion of this account's blake3 per-account hash into the
    /// slot's accounts hash (the SAME primitive the mint path uses for the vault).
    pub inclusion: AccountsInclusionProof16,
}

/// A holder's account plus the Solana Tower-BFT consensus evidence for its finalized
/// slot. Verified by [`prove_holding_consensus`] to a
/// [`LockProofTrust::ConsensusVerified`] [`ProvenHolding`] — the holder's balance over
/// their OWN account, proven by a real stake-weighted super-majority, with nothing
/// moved into custody.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoldingProof {
    /// The holder's own SPL token account + its accounts-hash inclusion.
    pub account: HoldingAccount,
    /// The finality evidence for the account's slot (the same
    /// [`ConsensusEvidence`] bundle the mint path verifies).
    pub consensus: ConsensusEvidence,
}

/// Why a proof-of-holdings observation was refused. A refusal NEVER yields a
/// `ConsensusVerified` [`ProvenHolding`] (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HoldingProofError {
    /// The account `data` is not a full SPL token account (shorter than
    /// [`SPL_ACCOUNT_LEN`], or otherwise undecodable) — [`decode_spl_token_account`]
    /// returned `None`.
    NotTokenAccount,
    /// The account holds a different SPL mint than the configured `$DREGG` mint.
    WrongMint,
    /// The account is NOT owned by the SPL Token program, so its 165-byte `data` is
    /// NOT an authoritative token balance — an attacker can put arbitrary bytes
    /// (`mint ‖ their_wallet ‖ u64::MAX`) in an account owned by their OWN program.
    /// Only accounts owned by the SPL Token program are real token balances, so this
    /// is refused (the exact forgery the vault path also defends against).
    NotSplTokenProgram {
        /// The program that actually owns the account (not the SPL Token program).
        owner_program: [u8; 32],
    },
    /// The evidence epoch does not match the supplied stake table's epoch.
    WrongEpoch {
        /// The epoch the evidence claims.
        evidence: u64,
        /// The epoch the stake table is for.
        table: u64,
    },
    /// The proof is structurally empty (no votes).
    Malformed,
    /// The voted stake does not meet the ≥ 2/3 threshold — the REAL, cryptographically
    /// counted stake against the tracked table (not a claimed hint).
    StakeBelowThreshold {
        /// The real counted voted stake.
        voted: u128,
        /// The total active stake.
        total: u128,
    },
    /// The bank-hash components do not recompute to the voted `bank_hash`.
    BankHashMismatch,
    /// The holder account's per-account hash does not include into the voted accounts
    /// hash via the supplied 16-ary path.
    AccountsInclusionInvalid,
    /// A PoH segment was present but did not verify (bad tick chain, or its tail is not
    /// the slot's blockhash).
    PohInvalid,
    /// PoH verification was required but no segment was supplied.
    PohMissing,
}

impl std::fmt::Display for HoldingProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotTokenAccount => write!(f, "account data is not a decodable SPL token account"),
            Self::WrongMint => write!(f, "account holds a different SPL mint than $DREGG"),
            Self::NotSplTokenProgram { owner_program } => write!(
                f,
                "account owned by program {:02x?} not the SPL Token program — data is not an authoritative balance",
                &owner_program[..4]
            ),
            Self::WrongEpoch { evidence, table } => write!(
                f,
                "evidence epoch {evidence} does not match stake-table epoch {table}"
            ),
            Self::Malformed => write!(f, "holding proof is structurally empty (no votes)"),
            Self::StakeBelowThreshold { voted, total } => write!(
                f,
                "voted stake {voted} does not meet the 2/3 threshold of total stake {total}"
            ),
            Self::BankHashMismatch => {
                write!(f, "bank-hash components do not bind the voted bank hash")
            }
            Self::AccountsInclusionInvalid => write!(
                f,
                "holder account is not included in the voted accounts hash"
            ),
            Self::PohInvalid => write!(f, "PoH segment does not verify against the slot blockhash"),
            Self::PohMissing => write!(f, "PoH verification required but no segment supplied"),
        }
    }
}

impl std::error::Error for HoldingProofError {}

/// **Prove a holder's balance over their OWN Solana account — non-custodially.**
///
/// Reads the holder's own SPL token account (`proof.account`) at a finalized slot,
/// verifies its inclusion under a **consensus-verified** bank hash (the SAME
/// stake-weighted ≥ 2/3 Ed25519 super-majority + 16-ary accounts-hash inclusion the
/// `$DREGG` mint path uses over the vault), decodes the balance via
/// [`decode_spl_token_account`], checks the mint is the configured `$DREGG` mint, and
/// returns a [`ProvenHolding`] with [`LockProofTrust::ConsensusVerified`].
///
/// **No vault, no lock, no transfer.** The holder keeps custody; the tokens never move.
/// Weight is granted by proof over the holder's own account, not by escrow.
///
/// Verification (fail closed — any failure returns `Err`, never a `ConsensusVerified`
/// holding):
/// 1. the account `data` decodes as an SPL token account, and its mint is `dregg_mint`;
/// 2. the evidence epoch matches `stake_table.epoch`;
/// 3. ≥ 2/3 of the epoch's active stake validly voted the `(slot, bank_hash)` — real
///    per-vote Ed25519 + stake-weighted sum ([`verify_supermajority`]);
/// 4. the bank-hash components recompute to the voted `bank_hash` (binding the accounts
///    hash the inclusion opens into to what the super-majority attested);
/// 5. the holder account's per-account hash includes into that accounts hash;
/// 6. if `require_poh` (or a PoH segment is present), the tick chain links to the slot's
///    blockhash.
pub fn prove_holding_consensus(
    proof: &HoldingProof,
    dregg_mint: &[u8; 32],
    spl_token_program: &[u8; 32],
    stake_table: &EpochStakeTable,
    require_poh: bool,
) -> Result<ProvenHolding, HoldingProofError> {
    let consensus = &proof.consensus;
    let acct = &proof.account;

    // (1a) LOAD-BEARING: the account must be owned by the SPL Token program, or its
    //      165-byte `data` is not an authoritative balance — an attacker's own
    //      program can put `mint ‖ their_wallet ‖ u64::MAX` in an account it owns and
    //      get it into a genuine finalized accounts hash, forging arbitrary weight.
    //      Bind the owner program BEFORE trusting the decoded balance.
    if &acct.owner_program != spl_token_program {
        return Err(HoldingProofError::NotSplTokenProgram {
            owner_program: acct.owner_program,
        });
    }

    // (1b) decode the holder's own SPL token account and bind the mint.
    let (mint, owner, amount) =
        decode_spl_token_account(&acct.data).ok_or(HoldingProofError::NotTokenAccount)?;
    if &mint != dregg_mint {
        return Err(HoldingProofError::WrongMint);
    }

    // (2) the stake table must be for the evidence epoch.
    if stake_table.epoch != consensus.epoch {
        return Err(HoldingProofError::WrongEpoch {
            evidence: consensus.epoch,
            table: stake_table.epoch,
        });
    }

    // (3) real stake-weighted Ed25519 super-majority on the voted bank hash.
    match verify_supermajority(
        stake_table,
        consensus.slot,
        &consensus.bank_hash,
        &consensus.votes,
    ) {
        Ok(_tally) => {}
        Err(VoteSetError::EmptyStakeTable) => return Err(HoldingProofError::Malformed),
        Err(VoteSetError::StakeBelowSupermajority { voted, total }) => {
            return Err(HoldingProofError::StakeBelowThreshold { voted, total });
        }
    }

    // (4) bind the accounts hash (and PoH tail) to the voted bank hash.
    if !consensus.bank_components.binds(&consensus.bank_hash) {
        return Err(HoldingProofError::BankHashMismatch);
    }

    // (5) the holder account's per-account hash must include into that accounts hash —
    //     the SAME 16-ary fan-out the mint path proves the vault with.
    let leaf = solana_account_hash(
        acct.lamports,
        &acct.owner_program,
        acct.executable,
        acct.rent_epoch,
        &acct.data,
        &acct.token_account,
    );
    if !verify_account_inclusion_16ary(
        leaf,
        &acct.inclusion,
        &consensus.bank_components.accounts_hash,
    ) {
        return Err(HoldingProofError::AccountsInclusionInvalid);
    }

    // (6) PoH linkage: if present it must verify and tail at the slot blockhash; if
    //     required and absent, refuse.
    match &consensus.poh {
        Some(seg) => {
            if verify_poh_segment(seg).is_err()
                || seg.tail_hash != consensus.bank_components.last_blockhash
            {
                return Err(HoldingProofError::PohInvalid);
            }
        }
        None => {
            if require_poh {
                return Err(HoldingProofError::PohMissing);
            }
        }
    }

    Ok(ProvenHolding {
        token_account: acct.token_account,
        owner,
        mint,
        amount,
        slot: consensus.slot,
        trust: LockProofTrust::ConsensusVerified,
    })
}

/// **A plain-RPC (structure-only) observation of the SAME holder account.**
///
/// Decodes the SPL token account and binds the mint, but runs NO consensus check — this
/// is what a forged/MITM RPC node can fabricate. It returns a [`ProvenHolding`] with
/// [`LockProofTrust::StructureOnly`], so [`ProvenHolding::is_consensus_proven`] is
/// `false` and the weight-binding layer MUST refuse to grant weight from it (fail
/// closed). `observed_slot` is the finalized slot the RPC read reported.
pub fn observe_holding_structure(
    account: &HoldingAccount,
    dregg_mint: &[u8; 32],
    spl_token_program: &[u8; 32],
    observed_slot: u64,
) -> Result<ProvenHolding, HoldingProofError> {
    if &account.owner_program != spl_token_program {
        return Err(HoldingProofError::NotSplTokenProgram {
            owner_program: account.owner_program,
        });
    }
    let (mint, owner, amount) =
        decode_spl_token_account(&account.data).ok_or(HoldingProofError::NotTokenAccount)?;
    if &mint != dregg_mint {
        return Err(HoldingProofError::WrongMint);
    }
    Ok(ProvenHolding {
        token_account: account.token_account,
        owner,
        mint,
        amount,
        slot: observed_slot,
        trust: LockProofTrust::StructureOnly,
    })
}
