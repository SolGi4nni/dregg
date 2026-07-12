//! `dregg-bridge::solana_provenance`: **bank-state provenance** for the trustless
//! Solana bridge — pass 3, the hardest leg.
//!
//! Passes 1–2 made the *consensus cryptography* ([`crate::solana_consensus`]) and
//! the *mainnet wire formats* ([`crate::solana_wire`]) real, but two inputs were
//! still **trusted**: the per-epoch [`EpochStakeTable`] (vote account → stake) and
//! the binding of each vote's signer to the vote account's on-chain authorized
//! voter. This module sources both **from Solana's own bank state**, verified
//! against the accounts hash the super-majority voted, rotated forward from an
//! irreducible weak-subjectivity anchor.
//!
//! # What becomes verified (no longer trusted)
//!
//! 1. **Stake table from bank state** ([`derive_stake_table`]). The active
//!    delegated stake per vote account is *derived* by proving the stake-program
//!    and vote-program accounts are included in the voted accounts hash (reusing
//!    pass-2's [`verify_account_inclusion_16ary`]) and decoding their account
//!    data: each stake account's [`Delegation`] (decoded from the mainnet
//!    `StakeStateV2` layout) contributes its active stake to its delegated vote
//!    account, and each vote account's `VoteState` (decoded with the type-only
//!    `solana-vote-interface`) yields the authorized voter for the epoch. The
//!    resulting [`EpochStakeTable`] is *proven from the bank hash the votes
//!    attest*, not supplied as trusted input.
//! 2. **Authorized-voter binding** ([`VerifiedStakeTable::tally_authorized`]).
//!    Each vote transaction (pass 2) designates a key as the vote authority and
//!    is signature-verified under it; here we additionally require that key to
//!    equal the vote account's on-chain `authorized_voter` for the epoch, decoded
//!    from the proven vote-account state. This closes pass-2's named gap — a
//!    relayer can no longer name an attacker key as authority.
//! 3. **Epoch rotation from a trusted anchor** ([`WeakSubjectivityAnchor`] +
//!    [`rotate`]). The anchor pins one `(epoch, stake_table_root)` checkpoint —
//!    the irreducible weak-subjectivity root every light client has. A later
//!    epoch's table is admitted only when it is (a) derived from bank state and
//!    (b) that bank state is attested by ≥ 2/3 of the *already-trusted* (anchor or
//!    previously-rotated) epoch's stake. Everything after the anchor is verified.
//!
//! # What pass 4 adds (the warmup/cooldown effective-stake curve)
//!
//! The stake summed per vote account is now Solana's **effective stake** — the
//! warmup/cooldown curve, not the coarse `[activation, deactivation)` integer
//! window. [`effective_stake`] runs Solana's own
//! `Delegation::stake_v2(target_epoch, &StakeHistory, new_rate_activation_epoch)`
//! (the upstream integer implementation, type-only `solana-stake-interface`) over
//! the cluster's [`StakeHistory`], so a delegation that is still warming up (or
//! cooling down) contributes its *rate-limited* effective stake, not its full
//! delegated amount. The per-epoch warmup/cooldown allowance is bounded by the
//! cluster rate (`ORIGINAL_WARMUP_COOLDOWN_RATE_BPS = 2_500` / 25%, then
//! `TOWER_WARMUP_COOLDOWN_RATE_BPS = 900` / 9% from the
//! `reduce_stake_warmup_cooldown` feature epoch — `new_rate_activation_epoch`).
//! The `StakeHistory` is itself **proven from the same bank state**: the
//! `SysvarStakeHistory1111111111111111111111111` sysvar account
//! ([`STAKE_HISTORY_SYSVAR_ID`]) is included in the voted accounts hash and
//! decoded ([`decode_stake_history`]), so the effective-stake denominator the
//! ≥ 2/3 super-majority is checked against is derived, not trusted.
//!
//! # What remains trusted (named precisely)
//!
//! - **The weak-subjectivity anchor itself** (`(epoch, stake_table_root)`). This
//!   is irreducible: a from-genesis-trustless Solana light client would have to
//!   replay all of history. Every deployed light client (ETH included) trusts a
//!   recent finalized checkpoint; this is dregg's.
//! - **The two-epoch leader-schedule snapshot offset.** The warmup/cooldown curve
//!   (the *magnitude* of each validator's stake) is now exact; which epoch index
//!   the consensus stake-weight snapshot is taken at (Solana's leader schedule is
//!   the stakes two epochs prior) is a ±1–2 epoch shift in the evaluation point,
//!   not the curve shape — evaluated here at the table's `epoch`.
//! - The **bank-hash version extras** and **account-data lock-record layout**
//!   named in `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md` are unchanged by this pass.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use solana_stake_interface::stake_history::{MAX_ENTRIES, StakeHistory, StakeHistoryEntry};
use solana_stake_interface::state::Delegation as SolDelegation;

use crate::solana_consensus::{
    BankHashComponents, EpochStakeTable, ValidatorVote, verify_supermajority,
};
use crate::solana_wire::{
    AccountsInclusionProof16, parse_verified_vote_tx, solana_account_hash,
    verify_account_inclusion_16ary,
};

// ============================================================================
// Program ids
// ============================================================================

/// The Solana **Stake program** id (`Stake11111111111111111111111111111111111111`)
/// — the owner of every stake account whose delegation we sum. A constant of the
/// protocol (not a deploy-time choice).
pub const STAKE_PROGRAM_ID: [u8; 32] = [
    6, 161, 216, 23, 145, 55, 84, 42, 152, 52, 55, 189, 254, 42, 122, 178, 85, 127, 83, 92, 138,
    120, 114, 43, 104, 164, 157, 192, 0, 0, 0, 0,
];

/// The Solana **Vote program** id — the owner of every vote account whose
/// `VoteState` we decode for the authorized voter. Re-derived from the type-only
/// `solana-vote-interface` so it tracks the crate.
pub fn vote_program_id() -> [u8; 32] {
    solana_vote_interface::program::id().to_bytes()
}

/// The **StakeHistory sysvar** account id
/// (`SysvarStakeHistory1111111111111111111111111`) — the bank-state account whose
/// data is the cluster-wide per-epoch `(effective, activating, deactivating)`
/// stake the warmup/cooldown curve reads. A constant of the protocol. Decoded by
/// [`decode_stake_history`] after proving the account into the voted accounts hash.
pub const STAKE_HISTORY_SYSVAR_ID: [u8; 32] = [
    6, 167, 213, 23, 25, 53, 132, 208, 254, 237, 155, 179, 67, 29, 19, 32, 107, 229, 68, 40, 27,
    87, 184, 86, 108, 197, 55, 95, 244, 0, 0, 0,
];

/// The Solana **Sysvar program** owner id
/// (`Sysvar1111111111111111111111111111111111111`) — the owner of every sysvar
/// account, including the StakeHistory sysvar. The derivation binds the sysvar by
/// its [`STAKE_HISTORY_SYSVAR_ID`] pubkey; this is the realistic owner the
/// per-account hash carries.
pub const SYSVAR_OWNER_ID: [u8; 32] = [
    6, 167, 213, 23, 24, 117, 247, 41, 199, 61, 147, 64, 143, 33, 97, 32, 6, 126, 216, 140, 118,
    224, 140, 40, 127, 193, 148, 96, 0, 0, 0, 0,
];

// ============================================================================
// Stake-account layout (mainnet StakeStateV2 bincode)
// ============================================================================

/// A decoded stake-account delegation (the fields of the mainnet
/// `StakeStateV2::Stake(Meta, Stake, StakeFlags)` variant we need).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Delegation {
    /// The vote account this stake is delegated to (the stake-table key).
    pub voter_pubkey: [u8; 32],
    /// The delegated stake, in lamports.
    pub stake: u64,
    /// The epoch this delegation activated.
    pub activation_epoch: u64,
    /// The epoch this delegation deactivated (`u64::MAX` if still active).
    pub deactivation_epoch: u64,
}

// `StakeStateV2` bincode layout (default bincode: u32 LE enum tag, fixint LE):
//   tag(4) = 2 for the `Stake` variant
//   Meta { rent_exempt_reserve u64(8), authorized {staker(32), withdrawer(32)},
//          lockup { unix_timestamp i64(8), epoch u64(8), custodian(32) } }  = 120
//   Stake { delegation { voter_pubkey(32), stake u64(8), activation_epoch u64(8),
//                        deactivation_epoch u64(8), _reserved[u8;8](8) } (=64),
//           credits_observed u64(8) }
//   StakeFlags u8(1)
// → the delegation begins at offset 4 + 120 = 124.
const STAKE_TAG_STAKE: u32 = 2;
const DELEGATION_OFF: usize = 124;
/// The minimum account-data length to decode a `Stake`-variant delegation.
const STAKE_MIN_LEN: usize = DELEGATION_OFF + 32 + 8 + 8 + 8;

fn read_u32_le(data: &[u8], off: usize) -> Option<u32> {
    let b = data.get(off..off + 4)?;
    Some(u32::from_le_bytes(b.try_into().ok()?))
}

fn read_u64_le(data: &[u8], off: usize) -> Option<u64> {
    let b = data.get(off..off + 8)?;
    Some(u64::from_le_bytes(b.try_into().ok()?))
}

fn read_arr32(data: &[u8], off: usize) -> Option<[u8; 32]> {
    let b = data.get(off..off + 32)?;
    b.try_into().ok()
}

/// Decode a stake account's `data` into its [`Delegation`], following the
/// mainnet `StakeStateV2` bincode layout. Returns `None` unless the account is
/// the `Stake` variant (an `Uninitialized` / `Initialized` / `RewardsPool` stake
/// account carries no delegation and contributes no stake).
pub fn decode_stake_delegation(data: &[u8]) -> Option<Delegation> {
    if data.len() < STAKE_MIN_LEN {
        return None;
    }
    if read_u32_le(data, 0)? != STAKE_TAG_STAKE {
        return None;
    }
    let voter_pubkey = read_arr32(data, DELEGATION_OFF)?;
    let stake = read_u64_le(data, DELEGATION_OFF + 32)?;
    let activation_epoch = read_u64_le(data, DELEGATION_OFF + 40)?;
    let deactivation_epoch = read_u64_le(data, DELEGATION_OFF + 48)?;
    Some(Delegation {
        voter_pubkey,
        stake,
        activation_epoch,
        deactivation_epoch,
    })
}

/// The coarse integer-window model: full `stake` while
/// `activation_epoch ≤ epoch < deactivation_epoch`, otherwise zero. Superseded by
/// [`effective_stake`] (the real warmup/cooldown curve) in [`derive_stake_table`];
/// retained as the upper bound the curve relaxes (effective ≤ window for a
/// (de)activating delegation, equal once fully warmed and not cooling).
pub fn active_stake(d: &Delegation, epoch: u64) -> u64 {
    if d.activation_epoch <= epoch && epoch < d.deactivation_epoch {
        d.stake
    } else {
        0
    }
}

/// The **effective stake** a delegation contributes at `epoch` under Solana's
/// warmup/cooldown curve, computed by Solana's own upstream-integer
/// `Delegation::stake_v2(epoch, &history, new_rate_activation_epoch)`
/// (type-only `solana-stake-interface`). A freshly-activating delegation warms up
/// at no more than the cluster rate per epoch
/// (`ORIGINAL_WARMUP_COOLDOWN_RATE_BPS` 25% → `TOWER_WARMUP_COOLDOWN_RATE_BPS` 9%
/// from `new_rate_activation_epoch`, the `reduce_stake_warmup_cooldown` feature
/// epoch); a deactivating one cools down symmetrically. `history` is the proven
/// cluster [`StakeHistory`] ([`decode_stake_history`]); `new_rate_activation_epoch`
/// is the network constant (`None` ⟹ original 25% forever).
///
/// Only `stake` / `activation_epoch` / `deactivation_epoch` drive the curve (the
/// vote pubkey is irrelevant to the magnitude), so the curve is evaluated on a
/// [`SolDelegation`] carrying exactly those.
pub fn effective_stake(
    d: &Delegation,
    epoch: u64,
    history: &StakeHistory,
    new_rate_activation_epoch: Option<u64>,
) -> u64 {
    let sol = SolDelegation {
        stake: d.stake,
        activation_epoch: d.activation_epoch,
        deactivation_epoch: d.deactivation_epoch,
        ..SolDelegation::default()
    };
    sol.stake_v2(epoch, history, new_rate_activation_epoch)
}

/// Decode the `StakeHistory` sysvar account `data` into a [`StakeHistory`]:
/// Solana serializes it as a bincode `Vec<(Epoch, StakeHistoryEntry)>` — a
/// `u64` LE entry count followed by that many 32-byte records
/// `(epoch u64, effective u64, activating u64, deactivating u64)`, newest-first.
/// Trailing bytes (the sysvar account is allocated to its fixed max size) are
/// ignored. Returns `None` for an entry count beyond [`MAX_ENTRIES`] (512) or a
/// record that runs past the end of `data` (a malformed input).
pub fn decode_stake_history(data: &[u8]) -> Option<StakeHistory> {
    let count = read_u64_le(data, 0)?;
    if count > MAX_ENTRIES as u64 {
        return None;
    }
    let mut history = StakeHistory::default();
    let mut off = 8usize;
    for _ in 0..count {
        let epoch = read_u64_le(data, off)?;
        let effective = read_u64_le(data, off + 8)?;
        let activating = read_u64_le(data, off + 16)?;
        let deactivating = read_u64_le(data, off + 24)?;
        off = off.checked_add(32)?;
        history.add(
            epoch,
            StakeHistoryEntry {
                effective,
                activating,
                deactivating,
            },
        );
    }
    Some(history)
}

// ============================================================================
// Vote-account layout (authorized voter for the epoch)
// ============================================================================

/// Decode a vote account's `data` into its authorized voter for `epoch`, using
/// the type-only `solana-vote-interface` (`VoteStateVersions`, all of V1_14_11 /
/// V3 / V4). Returns `None` for an uninitialized / undecodable vote account.
pub fn decode_authorized_voter(data: &[u8], epoch: u64) -> Option<[u8; 32]> {
    use solana_vote_interface::state::VoteStateVersions;
    let versions = VoteStateVersions::deserialize(data).ok()?;
    let authorized = match &versions {
        VoteStateVersions::V1_14_11(v) => v.authorized_voters.get_authorized_voter(epoch),
        VoteStateVersions::V3(v) => v.authorized_voters.get_authorized_voter(epoch),
        VoteStateVersions::V4(v) => v.authorized_voters.get_authorized_voter(epoch),
        VoteStateVersions::Uninitialized => None,
    }?;
    Some(authorized.to_bytes())
}

// ============================================================================
// A proven bank-state account (inclusion + fields)
// ============================================================================

/// One account proven to be present in a slot's accounts hash: its real fields
/// (so its blake3 per-account hash can be recomputed) plus a 16-ary inclusion
/// proof of that hash into the accounts hash. The same shape pass-2 uses for the
/// vault account, applied here to stake and vote accounts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenAccount {
    /// The account's pubkey (hashed into its per-account leaf).
    pub pubkey: [u8; 32],
    /// The account's lamports (zero-lamport accounts are absent and rejected).
    pub lamports: u64,
    /// The account's owning program (Stake or Vote program for derivation).
    pub owner: [u8; 32],
    /// Whether the account is executable.
    pub executable: bool,
    /// The account's rent epoch.
    pub rent_epoch: u64,
    /// The account's data (the `StakeStateV2` / `VoteStateVersions` bytes).
    pub data: Vec<u8>,
    /// The 16-ary fan-out inclusion proof of the account's blake3 hash into the
    /// accounts hash.
    pub proof: AccountsInclusionProof16,
}

impl ProvenAccount {
    /// Verify this account is included in `accounts_hash` (its real per-account
    /// blake3 hash folds to the root via the 16-ary proof).
    pub fn verify_inclusion(&self, accounts_hash: &[u8; 32]) -> bool {
        let leaf = solana_account_hash(
            self.lamports,
            &self.owner,
            self.executable,
            self.rent_epoch,
            &self.data,
            &self.pubkey,
        );
        verify_account_inclusion_16ary(leaf, &self.proof, accounts_hash)
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Why deriving / rotating a stake table from bank state failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProvenanceError {
    /// A supplied stake/vote account was not included in the accounts hash.
    AccountNotIncluded {
        /// The pubkey of the account whose inclusion proof failed.
        pubkey: [u8; 32],
    },
    /// A vote account's data did not decode to an initialized `VoteState` with an
    /// authorized voter for the epoch.
    UndecodableVoteAccount {
        /// The vote account pubkey.
        pubkey: [u8; 32],
    },
    /// No vote accounts were supplied (the table would have no authorized-voter
    /// bindings, so no witness vote could ever be authorized).
    NoVoteAccounts,
    /// The supplied stake-history account is not the
    /// `SysvarStakeHistory1111111111111111111111111` sysvar — the warmup/cooldown
    /// curve would read an attacker-chosen account.
    WrongStakeHistoryAccount {
        /// The pubkey of the account supplied in the stake-history slot.
        pubkey: [u8; 32],
    },
    /// The stake-history sysvar account's data did not decode to a
    /// [`StakeHistory`] (malformed length prefix or a truncated record).
    UndecodableStakeHistory,
    /// The derived stake table is empty (no active delegated stake) — there is no
    /// 2/3 denominator.
    EmptyDerivedTable,
    /// The derived table's root does not match the weak-subjectivity anchor — the
    /// supplied bank-state accounts do not reconstruct the anchored distribution.
    AnchorRootMismatch {
        /// The root the anchor pins.
        anchor: [u8; 32],
        /// The root derived from the supplied bank-state accounts.
        derived: [u8; 32],
    },
    /// A rotation step's epoch did not advance from the currently-trusted epoch.
    NonMonotonicRotation {
        /// The currently-trusted epoch.
        from: u64,
        /// The (invalid) target epoch.
        to: u64,
    },
    /// The bank state the next epoch's table is derived from is not attested by
    /// ≥ 2/3 of the currently-trusted epoch's stake (the rotation is not anchored
    /// in already-trusted consensus).
    RotationNotAttested,
    /// The next epoch's accounts hash does not bind the attesting bank hash.
    RotationBankHashMismatch,
}

impl std::fmt::Display for ProvenanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AccountNotIncluded { .. } => {
                write!(
                    f,
                    "a stake/vote account is not included in the accounts hash"
                )
            }
            Self::UndecodableVoteAccount { .. } => {
                write!(f, "a vote account has no authorized voter for the epoch")
            }
            Self::NoVoteAccounts => write!(f, "no vote accounts supplied for the derivation"),
            Self::WrongStakeHistoryAccount { .. } => {
                write!(
                    f,
                    "the stake-history account is not the StakeHistory sysvar"
                )
            }
            Self::UndecodableStakeHistory => {
                write!(f, "the stake-history sysvar account did not decode")
            }
            Self::EmptyDerivedTable => write!(f, "the derived stake table has no active stake"),
            Self::AnchorRootMismatch { .. } => {
                write!(f, "derived stake-table root does not match the anchor")
            }
            Self::NonMonotonicRotation { from, to } => {
                write!(f, "rotation epoch {to} does not advance from {from}")
            }
            Self::RotationNotAttested => write!(
                f,
                "the rotation bank state is not attested by 2/3 of the trusted stake"
            ),
            Self::RotationBankHashMismatch => {
                write!(f, "the rotation accounts hash does not bind the bank hash")
            }
        }
    }
}

impl std::error::Error for ProvenanceError {}

// ============================================================================
// Derivation from bank state
// ============================================================================

/// The product of a bank-state derivation: a [`EpochStakeTable`] proven from the
/// accounts hash, plus the `vote_account → authorized_voter` map decoded from the
/// proven vote accounts (used for the authorized-voter binding).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedStakeTable {
    /// The proven per-epoch active stake distribution.
    pub table: EpochStakeTable,
    /// Each proven vote account → its on-chain authorized voter for the epoch.
    pub authorized_voters: BTreeMap<[u8; 32], [u8; 32]>,
}

/// Derive a [`EpochStakeTable`] for `epoch` from bank state: prove each
/// `stake_accounts`, `vote_accounts`, and the `stake_history_account` is included
/// in `accounts_hash`, decode their delegations / authorized voters / cluster
/// stake history, and sum each delegation's **effective stake** (the
/// warmup/cooldown curve, [`effective_stake`]) per vote account.
///
/// Every account must verify-include in `accounts_hash`. `stake_history_account`
/// must be the [`STAKE_HISTORY_SYSVAR_ID`] sysvar; its decoded [`StakeHistory`]
/// drives the curve so a still-warming-up (or cooling-down) delegation
/// contributes its rate-limited effective stake, not its full delegated amount.
/// `new_rate_activation_epoch` is the `reduce_stake_warmup_cooldown` feature epoch
/// (`None` ⟹ the original 25% rate forever). A stake account that is not the
/// `Stake` variant (or whose effective stake is zero at `epoch`) contributes no
/// stake; a vote account that does not decode to an authorized voter is an error.
pub fn derive_stake_table(
    epoch: u64,
    accounts_hash: &[u8; 32],
    stake_accounts: &[ProvenAccount],
    vote_accounts: &[ProvenAccount],
    stake_history_account: &ProvenAccount,
    new_rate_activation_epoch: Option<u64>,
) -> Result<DerivedStakeTable, ProvenanceError> {
    if vote_accounts.is_empty() {
        return Err(ProvenanceError::NoVoteAccounts);
    }

    // Prove + decode the StakeHistory sysvar from the SAME bank state, so the
    // effective-stake denominator is derived, not trusted.
    if stake_history_account.pubkey != STAKE_HISTORY_SYSVAR_ID {
        return Err(ProvenanceError::WrongStakeHistoryAccount {
            pubkey: stake_history_account.pubkey,
        });
    }
    if !stake_history_account.verify_inclusion(accounts_hash) {
        return Err(ProvenanceError::AccountNotIncluded {
            pubkey: stake_history_account.pubkey,
        });
    }
    let history = decode_stake_history(&stake_history_account.data)
        .ok_or(ProvenanceError::UndecodableStakeHistory)?;

    // Authorized voters from the proven vote accounts.
    let mut authorized_voters: BTreeMap<[u8; 32], [u8; 32]> = BTreeMap::new();
    for va in vote_accounts {
        if !va.verify_inclusion(accounts_hash) {
            return Err(ProvenanceError::AccountNotIncluded { pubkey: va.pubkey });
        }
        let voter = decode_authorized_voter(&va.data, epoch)
            .ok_or(ProvenanceError::UndecodableVoteAccount { pubkey: va.pubkey })?;
        authorized_voters.insert(va.pubkey, voter);
    }

    // Effective delegated stake (warmup/cooldown curve), summed per vote account,
    // from the proven stake accounts.
    let mut sums: BTreeMap<[u8; 32], u128> = BTreeMap::new();
    for sa in stake_accounts {
        if !sa.verify_inclusion(accounts_hash) {
            return Err(ProvenanceError::AccountNotIncluded { pubkey: sa.pubkey });
        }
        // Only stake-program accounts carry delegations.
        if sa.owner != STAKE_PROGRAM_ID {
            continue;
        }
        if let Some(d) = decode_stake_delegation(&sa.data) {
            let active = effective_stake(&d, epoch, &history, new_rate_activation_epoch);
            if active > 0 {
                *sums.entry(d.voter_pubkey).or_insert(0) += active as u128;
            }
        }
    }

    let mut table = EpochStakeTable::new(epoch);
    for (vote_account, total) in sums {
        // Saturate at u64::MAX (a single vote account's active stake cannot
        // exceed the total lamport supply, well under u64::MAX, but stay safe).
        table.insert(vote_account, total.min(u64::MAX as u128) as u64);
    }
    if table.is_empty() {
        return Err(ProvenanceError::EmptyDerivedTable);
    }
    Ok(DerivedStakeTable {
        table,
        authorized_voters,
    })
}

// ============================================================================
// Weak-subjectivity anchor + verified table
// ============================================================================

/// The irreducible trust root: a known-good `(epoch, stake_table_root)`
/// checkpoint, like every light client's weak-subjectivity checkpoint. A stake
/// table is admitted at the anchor epoch only when its [`EpochStakeTable::root`]
/// equals `stake_table_root`; later epochs are admitted by [`rotate`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WeakSubjectivityAnchor {
    /// The anchored epoch.
    pub epoch: u64,
    /// The pinned [`EpochStakeTable::root`] for that epoch.
    pub stake_table_root: [u8; 32],
}

impl WeakSubjectivityAnchor {
    /// Build an anchor from a known-good stake table (the genuine distribution at
    /// its epoch — the weak-subjectivity checkpoint a deployer commits to).
    pub fn from_table(table: &EpochStakeTable) -> Self {
        Self {
            epoch: table.epoch,
            stake_table_root: table.root(),
        }
    }
}

/// A stake table whose provenance has been verified back to the
/// [`WeakSubjectivityAnchor`] — either the anchor epoch's table (root matches the
/// anchor) or one reached from it by [`rotate`] steps. Carries the authorized
/// voters so the consensus tally can bind each vote's signer to its on-chain
/// authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedStakeTable {
    table: EpochStakeTable,
    authorized_voters: BTreeMap<[u8; 32], [u8; 32]>,
}

impl VerifiedStakeTable {
    /// The verified epoch.
    pub fn epoch(&self) -> u64 {
        self.table.epoch
    }

    /// The verified stake table.
    pub fn table(&self) -> &EpochStakeTable {
        &self.table
    }

    /// Admit the **anchor epoch's** table: derive it from bank state and require
    /// its root to equal the anchor's pinned root. This is the base of the trust
    /// chain — the only place the (trusted) anchor root is consulted.
    pub fn from_anchor(
        anchor: &WeakSubjectivityAnchor,
        accounts_hash: &[u8; 32],
        stake_accounts: &[ProvenAccount],
        vote_accounts: &[ProvenAccount],
        stake_history_account: &ProvenAccount,
        new_rate_activation_epoch: Option<u64>,
    ) -> Result<Self, ProvenanceError> {
        let derived = derive_stake_table(
            anchor.epoch,
            accounts_hash,
            stake_accounts,
            vote_accounts,
            stake_history_account,
            new_rate_activation_epoch,
        )?;
        let derived_root = derived.table.root();
        if derived_root != anchor.stake_table_root {
            return Err(ProvenanceError::AnchorRootMismatch {
                anchor: anchor.stake_table_root,
                derived: derived_root,
            });
        }
        Ok(Self {
            table: derived.table,
            authorized_voters: derived.authorized_voters,
        })
    }

    /// **Tally with authorized-voter binding** (the trustless super-majority).
    /// Like [`verify_supermajority`], but additionally requires each counted vote
    /// to be witness-backed (a real vote transaction) and signed by exactly the
    /// vote account's on-chain authorized voter for the epoch (decoded from the
    /// proven vote-account state). A placeholder vote, an unauthorized signer, or
    /// a vote account with no proven authorized voter contributes **zero** stake.
    ///
    /// Returns `Ok(voted_stake)` when ≥ 2/3 of the verified total stake validly
    /// and authorizedly voted `(slot, bank_hash)`, else `Err((voted, total))`.
    pub fn tally_authorized(
        &self,
        slot: u64,
        bank_hash: &[u8; 32],
        votes: &[ValidatorVote],
    ) -> Result<u128, (u128, u128)> {
        use std::collections::BTreeSet;
        let total = self.table.total_stake();
        let mut counted: BTreeSet<[u8; 32]> = BTreeSet::new();
        let mut voted: u128 = 0;
        for v in votes {
            if v.slot != slot || &v.bank_hash != bank_hash {
                continue;
            }
            let stake = self.table.stake_of(&v.vote_pubkey);
            if stake == 0 || counted.contains(&v.vote_pubkey) {
                continue;
            }
            // Authorized-voter binding: only a witness-backed vote whose signer is
            // the proven on-chain authorized voter counts.
            let Some(witness) = &v.tx_witness else {
                continue;
            };
            let Ok(ingested) = parse_verified_vote_tx(&witness.tx_bytes) else {
                continue; // signature / parse failure
            };
            if ingested.vote_account != v.vote_pubkey
                || ingested.voted_slot != slot
                || &ingested.voted_bank_hash != bank_hash
            {
                continue;
            }
            let Some(expected) = self.authorized_voters.get(&v.vote_pubkey) else {
                continue; // no proven authorized voter for this account
            };
            if &ingested.authorized_voter != expected {
                continue; // signer is not the on-chain authorized voter
            }
            counted.insert(v.vote_pubkey);
            voted += stake as u128;
        }
        if voted.saturating_mul(3) >= total.saturating_mul(2) && total > 0 {
            Ok(voted)
        } else {
            Err((voted, total))
        }
    }
}

/// One epoch-rotation step: the next epoch's bank-state accounts (proving the
/// next stake table), plus the consensus attestation that the bank state they
/// live in is rooted by ≥ 2/3 of the *currently-trusted* epoch's stake.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RotationStep {
    /// The epoch this step advances the trusted table to.
    pub to_epoch: u64,
    /// The slot whose bank state the next table is derived from.
    pub slot: u64,
    /// The bank hash the *currently-trusted* stake attests for `slot`.
    pub bank_hash: [u8; 32],
    /// The bank-hash components binding `accounts_hash` to `bank_hash`.
    pub bank_components: BankHashComponents,
    /// Votes from the currently-trusted epoch's validators attesting `bank_hash`.
    pub votes: Vec<ValidatorVote>,
    /// The accounts hash of `slot`'s bank state (where the next table's accounts
    /// live); must equal `bank_components.accounts_hash`.
    pub accounts_hash: [u8; 32],
    /// Stake accounts proving the next epoch's delegations.
    pub stake_accounts: Vec<ProvenAccount>,
    /// Vote accounts proving the next epoch's authorized voters.
    pub vote_accounts: Vec<ProvenAccount>,
    /// The next epoch's `StakeHistory` sysvar account, proving the cluster stake
    /// history the warmup/cooldown curve reads.
    pub stake_history_account: ProvenAccount,
    /// The `reduce_stake_warmup_cooldown` feature epoch (`None` ⟹ original 25%).
    pub new_rate_activation_epoch: Option<u64>,
}

/// Rotate the trusted stake table forward by one epoch: derive the next table
/// from `step`'s bank-state accounts, and require that bank state to be attested
/// by ≥ 2/3 of `current`'s (already-trusted) stake. The newly-trusted table is
/// returned; the trust chains transitively back to the anchor.
///
/// Note the attestation uses the *plain* [`verify_supermajority`] over the
/// trusted table (the rotation is anchored by the trusted epoch's stake-weighted
/// Ed25519, not by an authorized-voter binding for the as-yet-untrusted next
/// epoch).
pub fn rotate(
    current: &VerifiedStakeTable,
    step: &RotationStep,
) -> Result<VerifiedStakeTable, ProvenanceError> {
    if step.to_epoch <= current.epoch() {
        return Err(ProvenanceError::NonMonotonicRotation {
            from: current.epoch(),
            to: step.to_epoch,
        });
    }
    // The accounts hash the next table is derived from must be the one the
    // attesting bank hash commits to.
    if step.bank_components.accounts_hash != step.accounts_hash
        || !step.bank_components.binds(&step.bank_hash)
    {
        return Err(ProvenanceError::RotationBankHashMismatch);
    }
    // The bank state must be attested by ≥ 2/3 of the currently-trusted stake.
    if verify_supermajority(current.table(), step.slot, &step.bank_hash, &step.votes).is_err() {
        return Err(ProvenanceError::RotationNotAttested);
    }
    // Derive the next epoch's table from that (now-attested) bank state.
    let derived = derive_stake_table(
        step.to_epoch,
        &step.accounts_hash,
        &step.stake_accounts,
        &step.vote_accounts,
        &step.stake_history_account,
        step.new_rate_activation_epoch,
    )?;
    Ok(VerifiedStakeTable {
        table: derived.table,
        authorized_voters: derived.authorized_voters,
    })
}

// ============================================================================
// Test/dev fixture builders (promoted from the unit-test module so INTEGRATION
// tests and downstream crates' dev builds can assemble anchored fixtures)
// ============================================================================

/// **Bank-state-provenance fixture builders — TEST/DEV ONLY.**
///
/// Real-layout builders for stake accounts, vote accounts, the StakeHistory
/// sysvar, single-chunk 16-ary inclusions, and genuinely-signed TowerSync vote
/// transactions — everything needed to assemble a
/// [`WeakSubjectivityAnchor`]-rooted (anchored) fixture whose stake table is
/// *derived from bank state*, exactly what the production anchored verifiers
/// consume. Compiled only under `cfg(test)` or the dev-only `test-utils`
/// feature; never part of a shipped build.
#[cfg(any(test, feature = "test-utils"))]
pub mod fixtures {
    use super::*;
    use crate::solana_wire::{MerkleLevel, accounts_merkle_node, ingest_vote_transaction};
    use ed25519_dalek::{Signer, SigningKey};
    use solana_vote_interface::instruction::VoteInstruction;
    use solana_vote_interface::state::{TowerSync, VoteStateV3, VoteStateVersions};

    /// A deterministic Ed25519 signing key from a one-byte seed.
    pub fn sk(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// Build a mainnet-layout `StakeStateV2::Stake` account `data` for a
    /// delegation. 200 bytes (Solana's stake account size), zero-padded.
    pub fn build_stake_account_data(
        voter: &[u8; 32],
        stake: u64,
        activation_epoch: u64,
        deactivation_epoch: u64,
    ) -> Vec<u8> {
        let mut d = vec![0u8; 200];
        d[0..4].copy_from_slice(&STAKE_TAG_STAKE.to_le_bytes());
        // Meta occupies [4, 124); contents irrelevant to the delegation decode.
        d[DELEGATION_OFF..DELEGATION_OFF + 32].copy_from_slice(voter);
        d[DELEGATION_OFF + 32..DELEGATION_OFF + 40].copy_from_slice(&stake.to_le_bytes());
        d[DELEGATION_OFF + 40..DELEGATION_OFF + 48]
            .copy_from_slice(&activation_epoch.to_le_bytes());
        d[DELEGATION_OFF + 48..DELEGATION_OFF + 56]
            .copy_from_slice(&deactivation_epoch.to_le_bytes());
        d
    }

    /// Serialize a `StakeHistory` sysvar account `data`: a bincode
    /// `Vec<(Epoch, StakeHistoryEntry)>` — `u64` LE count then 32-byte records
    /// `(epoch, effective, activating, deactivating)`. Mirrors what
    /// [`decode_stake_history`] reads.
    pub fn encode_stake_history_data(entries: &[(u64, u64, u64, u64)]) -> Vec<u8> {
        let mut d = Vec::with_capacity(8 + entries.len() * 32);
        d.extend_from_slice(&(entries.len() as u64).to_le_bytes());
        for (epoch, effective, activating, deactivating) in entries {
            d.extend_from_slice(&epoch.to_le_bytes());
            d.extend_from_slice(&effective.to_le_bytes());
            d.extend_from_slice(&activating.to_le_bytes());
            d.extend_from_slice(&deactivating.to_le_bytes());
        }
        d
    }

    /// Build a real bincode `VoteStateVersions::V3` vote-account `data` whose
    /// authorized voter at every epoch is `voter`.
    pub fn build_vote_account_data(node: &[u8; 32], voter: &[u8; 32], epoch: u64) -> Vec<u8> {
        use solana_pubkey::Pubkey;
        use solana_vote_interface::authorized_voters::AuthorizedVoters;
        let mut vs = VoteStateV3 {
            node_pubkey: Pubkey::from(*node),
            authorized_voters: AuthorizedVoters::new(epoch, Pubkey::from(*voter)),
            ..VoteStateV3::default()
        };
        // Ensure a withdrawer too (irrelevant, but realistic).
        vs.authorized_withdrawer = Pubkey::from(*node);
        bincode::serialize(&VoteStateVersions::new_v3(vs)).expect("serialize vote state")
    }

    /// The 16-ary accounts-tree fan-out (one chunk's maximum children).
    pub const MERKLE_FANOUT_T: usize = 16;

    /// Place `leaves` into a single 16-ary chunk and return
    /// `(accounts_hash, proof_for_each_index)`.
    pub fn single_chunk(leaves: &[[u8; 32]]) -> ([u8; 32], Vec<AccountsInclusionProof16>) {
        assert!(leaves.len() <= MERKLE_FANOUT_T);
        let accounts_hash = accounts_merkle_node(leaves);
        let proofs = (0..leaves.len())
            .map(|i| {
                let siblings: Vec<[u8; 32]> = leaves
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, h)| *h)
                    .collect();
                AccountsInclusionProof16 {
                    levels: vec![MerkleLevel {
                        position: i as u8,
                        siblings,
                    }],
                }
            })
            .collect();
        (accounts_hash, proofs)
    }

    /// A [`ProvenAccount`] with fixed lamports/rent (the fields fixtures never
    /// vary), carrying `data` + its 16-ary inclusion `proof`.
    pub fn proven_account(
        pubkey: [u8; 32],
        owner: [u8; 32],
        data: Vec<u8>,
        proof: AccountsInclusionProof16,
    ) -> ProvenAccount {
        ProvenAccount {
            pubkey,
            lamports: 1_000_000,
            owner,
            executable: false,
            rent_epoch: 0,
            data,
            proof,
        }
    }

    /// A REAL signed TowerSync vote transaction by `authority` for
    /// `vote_account` voting `(slot, bank)`, ingested through the mainnet wire
    /// parser so the produced [`ValidatorVote`] carries a genuine tx witness —
    /// the only kind of vote [`VerifiedStakeTable::tally_authorized`] counts.
    pub fn tower_sync_tx(
        authority: &SigningKey,
        vote_account: &[u8; 32],
        slot: u64,
        bank: [u8; 32],
    ) -> ValidatorVote {
        // Build a real legacy vote tx with the authority as sole signer; reuse
        // the wire ingestion so the produced vote carries a real witness.
        let auth_pk = authority.verifying_key().to_bytes();
        let vote_program = vote_program_id();
        let account_keys: Vec<[u8; 32]> = vec![
            auth_pk,
            *vote_account,
            [0x10u8; 32],
            [0x11u8; 32],
            vote_program,
        ];
        let ts = TowerSync::from(vec![(slot - 1, 2u32), (slot, 1u32)]);
        let ts = TowerSync {
            hash: solana_hash::Hash::new_from_array(bank),
            ..ts
        };
        let vi = VoteInstruction::TowerSync(ts);
        let ix_data = bincode::serialize(&vi).expect("serialize vi");
        let metas: Vec<u8> = vec![1, 0]; // vote account(1), authority(0)
        let mut msg = Vec::new();
        msg.push(1u8); // num_required_signatures
        msg.push(0u8);
        msg.push(3u8);
        put_compact_u16(&mut msg, account_keys.len() as u16);
        for k in &account_keys {
            msg.extend_from_slice(k);
        }
        msg.extend_from_slice(&[0x99u8; 32]); // recent_blockhash
        put_compact_u16(&mut msg, 1);
        msg.push(4u8); // program id index
        put_compact_u16(&mut msg, metas.len() as u16);
        msg.extend_from_slice(&metas);
        put_compact_u16(&mut msg, ix_data.len() as u16);
        msg.extend_from_slice(&ix_data);
        let sig = authority.sign(&msg).to_bytes();
        let mut tx = Vec::new();
        put_compact_u16(&mut tx, 1);
        tx.extend_from_slice(&sig);
        tx.extend_from_slice(&msg);
        ingest_vote_transaction(&tx).expect("ingest")
    }

    /// Solana's compact-u16 (shortvec) length encoding.
    pub fn put_compact_u16(out: &mut Vec<u8>, mut v: u16) {
        loop {
            let mut byte = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if v == 0 {
                break;
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    pub(crate) use super::fixtures::*;

    #[test]
    fn decode_stake_delegation_reads_layout() {
        let voter = [0x42u8; 32];
        let data = build_stake_account_data(&voter, 5_000, 3, u64::MAX);
        let d = decode_stake_delegation(&data).expect("decodes a Stake variant");
        assert_eq!(d.voter_pubkey, voter);
        assert_eq!(d.stake, 5_000);
        assert_eq!(d.activation_epoch, 3);
        assert_eq!(d.deactivation_epoch, u64::MAX);
    }

    #[test]
    fn decode_stake_delegation_rejects_non_stake_variant() {
        let mut data = build_stake_account_data(&[1u8; 32], 1, 0, u64::MAX);
        data[0] = 1; // Initialized, not Stake
        assert_eq!(decode_stake_delegation(&data), None);
        let mut short = data.clone();
        short.truncate(50);
        assert_eq!(decode_stake_delegation(&short), None);
    }

    #[test]
    fn active_stake_respects_epoch_window() {
        let d = Delegation {
            voter_pubkey: [0u8; 32],
            stake: 1000,
            activation_epoch: 5,
            deactivation_epoch: 9,
        };
        assert_eq!(active_stake(&d, 4), 0); // before activation
        assert_eq!(active_stake(&d, 5), 1000); // active
        assert_eq!(active_stake(&d, 8), 1000); // active
        assert_eq!(active_stake(&d, 9), 0); // deactivated
    }

    // ---- stake-history sysvar fixtures + the warmup/cooldown curve -----------

    #[test]
    fn decode_stake_history_round_trips() {
        let data = encode_stake_history_data(&[(11, 5, 6, 7), (10, 1_000_000, 1_000_000, 0)]);
        let h = decode_stake_history(&data).expect("decodes");
        assert_eq!(
            h.get(10),
            Some(&StakeHistoryEntry {
                effective: 1_000_000,
                activating: 1_000_000,
                deactivating: 0
            })
        );
        assert_eq!(h.get(11).map(|e| e.effective), Some(5));
        // A count beyond MAX_ENTRIES is refused; a truncated record is refused.
        let mut huge = (MAX_ENTRIES as u64 + 1).to_le_bytes().to_vec();
        huge.extend_from_slice(&[0u8; 32]);
        assert_eq!(decode_stake_history(&huge), None);
        let truncated = {
            let mut t = 1u64.to_le_bytes().to_vec();
            t.extend_from_slice(&[0u8; 20]); // short record
            t
        };
        assert_eq!(decode_stake_history(&truncated), None);
    }

    #[test]
    fn effective_stake_follows_warmup_curve() {
        // A delegation of 1_000_000 activating at epoch 10. The cluster at epoch 10
        // has effective = activating = 1_000_000 (this lone validator warming up).
        let d = Delegation {
            voter_pubkey: [0u8; 32],
            stake: 1_000_000,
            activation_epoch: 10,
            deactivation_epoch: u64::MAX,
        };
        let history =
            decode_stake_history(&encode_stake_history_data(&[(10, 1_000_000, 1_000_000, 0)]))
                .unwrap();

        // At the activation epoch it is ALL activating, 0 effective.
        assert_eq!(effective_stake(&d, 10, &history, Some(0)), 0);
        // One epoch later, warmup is rate-limited to the 9% tower rate (new rate
        // active from genesis): 1_000_000 * 9% = 90_000, NOT the full 1_000_000.
        assert_eq!(effective_stake(&d, 11, &history, Some(0)), 90_000);
        // Under the ORIGINAL 25% rate (None ⟹ never switched), the same epoch
        // warms 1_000_000 * 25% = 250_000 — the cited constant difference.
        assert_eq!(effective_stake(&d, 11, &history, None), 250_000);
        // A delegation whose activation epoch is NOT in the (bounded) history is
        // treated as fully warmed — the common long-active case.
        let old = Delegation {
            activation_epoch: 0,
            ..d
        };
        assert_eq!(effective_stake(&old, 11, &history, Some(0)), 1_000_000);
    }

    // ---- vote-account authorized-voter decode -------------------------------

    #[test]
    fn decode_authorized_voter_round_trips() {
        let node = [0x11u8; 32];
        let voter = [0x22u8; 32];
        let data = build_vote_account_data(&node, &voter, 7);
        assert_eq!(decode_authorized_voter(&data, 7), Some(voter));
        // Carry-forward semantics: a later epoch sees the same voter.
        assert_eq!(decode_authorized_voter(&data, 9), Some(voter));
        // Garbage data does not decode.
        assert_eq!(decode_authorized_voter(&[0u8; 4], 7), None);
    }

    // ---- inclusion fixtures -------------------------------------------------

    /// A small genuine cluster: two vote accounts (authorized voters a1/a2) with
    /// stake 700/300, plus the (empty) StakeHistory sysvar account, all proven
    /// into one accounts hash. Both validators activated at epoch 0, which the
    /// empty history does not cover, so each is fully warmed (effective = full).
    /// Returns `(epoch, accounts_hash, stake_accounts, vote_accounts, va1, va2,
    /// a1, a2, stake_history_account)`.
    #[allow(clippy::type_complexity)]
    fn cluster() -> (
        u64,
        [u8; 32],
        Vec<ProvenAccount>,
        Vec<ProvenAccount>,
        [u8; 32],
        [u8; 32],
        SigningKey,
        SigningKey,
        ProvenAccount,
    ) {
        let epoch = 42u64;
        let va1 = [0xA1u8; 32];
        let va2 = [0xA2u8; 32];
        let a1 = sk(11);
        let a2 = sk(12);
        let a1pk = a1.verifying_key().to_bytes();
        let a2pk = a2.verifying_key().to_bytes();

        let vote_program = vote_program_id();
        let stake_program = STAKE_PROGRAM_ID;
        let sysvar_owner = SYSVAR_OWNER_ID;

        // Account data.
        let vd1 = build_vote_account_data(&[0x01u8; 32], &a1pk, epoch);
        let vd2 = build_vote_account_data(&[0x02u8; 32], &a2pk, epoch);
        let sd1 = build_stake_account_data(&va1, 700, 0, u64::MAX);
        let sd2 = build_stake_account_data(&va2, 300, 0, u64::MAX);
        let shd = encode_stake_history_data(&[]); // empty → epoch-0 validators fully warmed

        let sa1pk = [0x51u8; 32];
        let sa2pk = [0x52u8; 32];

        // Per-account leaves (the order in the chunk).
        let leaves = [
            solana_account_hash(1_000_000, &vote_program, false, 0, &vd1, &va1),
            solana_account_hash(1_000_000, &vote_program, false, 0, &vd2, &va2),
            solana_account_hash(1_000_000, &stake_program, false, 0, &sd1, &sa1pk),
            solana_account_hash(1_000_000, &stake_program, false, 0, &sd2, &sa2pk),
            solana_account_hash(
                1_000_000,
                &sysvar_owner,
                false,
                0,
                &shd,
                &STAKE_HISTORY_SYSVAR_ID,
            ),
        ];
        let (accounts_hash, proofs) = single_chunk(&leaves);

        let vote_accounts = vec![
            proven_account(va1, vote_program, vd1, proofs[0].clone()),
            proven_account(va2, vote_program, vd2, proofs[1].clone()),
        ];
        let stake_accounts = vec![
            proven_account(sa1pk, stake_program, sd1, proofs[2].clone()),
            proven_account(sa2pk, stake_program, sd2, proofs[3].clone()),
        ];
        let stake_history_account = proven_account(
            STAKE_HISTORY_SYSVAR_ID,
            sysvar_owner,
            shd,
            proofs[4].clone(),
        );
        (
            epoch,
            accounts_hash,
            stake_accounts,
            vote_accounts,
            va1,
            va2,
            a1,
            a2,
            stake_history_account,
        )
    }

    #[test]
    fn derive_stake_table_from_bank_state() {
        let (epoch, accounts_hash, stake_accounts, vote_accounts, va1, va2, a1, a2, sh) = cluster();
        let derived = derive_stake_table(
            epoch,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .expect("derive");
        assert_eq!(derived.table.stake_of(&va1), 700);
        assert_eq!(derived.table.stake_of(&va2), 300);
        assert_eq!(derived.table.total_stake(), 1000);
        // Authorized voters bound to the real signers.
        assert_eq!(
            derived.authorized_voters.get(&va1),
            Some(&a1.verifying_key().to_bytes())
        );
        assert_eq!(
            derived.authorized_voters.get(&va2),
            Some(&a2.verifying_key().to_bytes())
        );
    }

    #[test]
    fn derive_refuses_tampered_account() {
        let (epoch, accounts_hash, mut stake_accounts, vote_accounts, .., sh) = cluster();
        // Inflate a stake account's recorded stake: its blake3 hash changes, so
        // the inclusion proof no longer roots to the committed accounts hash.
        let n = stake_accounts[0].data.len();
        stake_accounts[0].data[DELEGATION_OFF + 32] ^= 0xFF; // mutate stake bytes
        let _ = n;
        let err = derive_stake_table(
            epoch,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap_err();
        assert!(matches!(err, ProvenanceError::AccountNotIncluded { .. }));
    }

    // ---- anchor admission + authorized-voter binding ------------------------

    #[test]
    fn anchor_admits_matching_table_and_binds_voters() {
        let (epoch, accounts_hash, stake_accounts, vote_accounts, va1, va2, a1, a2, sh) = cluster();
        // The anchor is the genuine distribution at the epoch.
        let derived = derive_stake_table(
            epoch,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap();
        let anchor = WeakSubjectivityAnchor::from_table(&derived.table);

        let verified = VerifiedStakeTable::from_anchor(
            &anchor,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .expect("anchor admits its own derivation");
        assert_eq!(verified.epoch(), epoch);

        // A bank hash voted by both authorized voters (700+300 = 1000/1000).
        let slot = 1_000u64;
        let bank = [0x77u8; 32];
        let votes = vec![
            tower_sync_tx(&a1, &va1, slot, bank),
            tower_sync_tx(&a2, &va2, slot, bank),
        ];
        let voted = verified.tally_authorized(slot, &bank, &votes).expect("2/3");
        assert_eq!(voted, 1000);
    }

    #[test]
    fn unauthorized_signer_contributes_no_stake() {
        let (epoch, accounts_hash, stake_accounts, vote_accounts, va1, va2, _a1, a2, sh) =
            cluster();
        let derived = derive_stake_table(
            epoch,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap();
        let anchor = WeakSubjectivityAnchor::from_table(&derived.table);
        let verified = VerifiedStakeTable::from_anchor(
            &anchor,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap();

        let slot = 1_000u64;
        let bank = [0x77u8; 32];
        // va1 is voted by an IMPOSTER key (not its on-chain authorized voter a1).
        let imposter = sk(99);
        let votes = vec![
            tower_sync_tx(&imposter, &va1, slot, bank), // unauthorized → 0
            tower_sync_tx(&a2, &va2, slot, bank),       // authorized → 300
        ];
        // Only 300/1000 counts → below 2/3.
        let err = verified.tally_authorized(slot, &bank, &votes).unwrap_err();
        assert_eq!(err, (300, 1000));
    }

    #[test]
    fn anchor_rejects_mismatched_distribution() {
        let (epoch, accounts_hash, stake_accounts, vote_accounts, .., sh) = cluster();
        // Anchor pins a DIFFERENT root (a fabricated distribution).
        let mut fake = EpochStakeTable::new(epoch);
        fake.insert([0xDEu8; 32], 999);
        let anchor = WeakSubjectivityAnchor::from_table(&fake);
        let err = VerifiedStakeTable::from_anchor(
            &anchor,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap_err();
        assert!(matches!(err, ProvenanceError::AnchorRootMismatch { .. }));
    }

    // ---- epoch rotation -----------------------------------------------------

    #[test]
    fn rotation_from_anchor_accepted_and_forgery_refused() {
        // Epoch N: the anchor cluster (a1/a2 with 700/300).
        let (epoch, accounts_hash, stake_accounts, vote_accounts, va1, va2, a1, a2, sh) = cluster();
        let derived = derive_stake_table(
            epoch,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap();
        let anchor = WeakSubjectivityAnchor::from_table(&derived.table);
        let current = VerifiedStakeTable::from_anchor(
            &anchor,
            &accounts_hash,
            &stake_accounts,
            &vote_accounts,
            &sh,
            None,
        )
        .unwrap();

        // Epoch N+1's bank state: a new distribution (va1 grows to 900, va2→100).
        let next_epoch = epoch + 1;
        let a1pk = a1.verifying_key().to_bytes();
        let a2pk = a2.verifying_key().to_bytes();
        let vote_program = vote_program_id();
        let stake_program = STAKE_PROGRAM_ID;
        let sysvar_owner = SYSVAR_OWNER_ID;
        let vd1 = build_vote_account_data(&[0x01u8; 32], &a1pk, next_epoch);
        let vd2 = build_vote_account_data(&[0x02u8; 32], &a2pk, next_epoch);
        let sd1 = build_stake_account_data(&va1, 900, 0, u64::MAX);
        let sd2 = build_stake_account_data(&va2, 100, 0, u64::MAX);
        let shd = encode_stake_history_data(&[]); // empty → epoch-0 stake fully warmed
        let leaves = [
            solana_account_hash(1_000_000, &vote_program, false, 0, &vd1, &va1),
            solana_account_hash(1_000_000, &vote_program, false, 0, &vd2, &va2),
            solana_account_hash(1_000_000, &stake_program, false, 0, &sd1, &[0x61u8; 32]),
            solana_account_hash(1_000_000, &stake_program, false, 0, &sd2, &[0x62u8; 32]),
            solana_account_hash(
                1_000_000,
                &sysvar_owner,
                false,
                0,
                &shd,
                &STAKE_HISTORY_SYSVAR_ID,
            ),
        ];
        let (next_accounts_hash, proofs) = single_chunk(&leaves);
        let next_vote_accounts = vec![
            proven_account(va1, vote_program, vd1, proofs[0].clone()),
            proven_account(va2, vote_program, vd2, proofs[1].clone()),
        ];
        let next_stake_accounts = vec![
            proven_account([0x61u8; 32], stake_program, sd1, proofs[2].clone()),
            proven_account([0x62u8; 32], stake_program, sd2, proofs[3].clone()),
        ];
        let next_stake_history_account = proven_account(
            STAKE_HISTORY_SYSVAR_ID,
            sysvar_owner,
            shd,
            proofs[4].clone(),
        );

        // The attesting bank state for epoch N+1's slot, voted by the CURRENT
        // (epoch N) validators a1/a2.
        let next_slot = 5_000u64;
        let bank_components = BankHashComponents {
            parent_bank_hash: [0x01; 32],
            accounts_hash: next_accounts_hash,
            signature_count: 1,
            last_blockhash: [0x02; 32],
        };
        let bank_hash = bank_components.compute();
        // Real signed vote transactions from the trusted-epoch validators, keyed
        // by their VOTE ACCOUNTS (va1/va2 — the trusted table's keys). The
        // rotation attestation tallies these over the trusted table.
        let votes = vec![
            tower_sync_tx(&a1, &va1, next_slot, bank_hash),
            tower_sync_tx(&a2, &va2, next_slot, bank_hash),
        ];

        let good_step = RotationStep {
            to_epoch: next_epoch,
            slot: next_slot,
            bank_hash,
            bank_components,
            votes: votes.clone(),
            accounts_hash: next_accounts_hash,
            stake_accounts: next_stake_accounts.clone(),
            vote_accounts: next_vote_accounts.clone(),
            stake_history_account: next_stake_history_account.clone(),
            new_rate_activation_epoch: None,
        };
        let rotated = rotate(&current, &good_step).expect("valid rotation accepted");
        assert_eq!(rotated.epoch(), next_epoch);
        assert_eq!(rotated.table().stake_of(&va1), 900);
        assert_eq!(rotated.table().stake_of(&va2), 100);

        // Forgery: same next distribution but NOT attested by the trusted epoch
        // (drop the votes). Refused.
        let forged = RotationStep {
            votes: vec![],
            ..good_step.clone()
        };
        assert_eq!(
            rotate(&current, &forged).unwrap_err(),
            ProvenanceError::RotationNotAttested
        );

        // Forgery: a bank hash the trusted validators never signed (tamper the
        // accounts hash so the votes are over a different bank hash) → not
        // attested.
        let mut bad_components = good_step.bank_components;
        bad_components.signature_count = 999;
        let bad_bank_hash = bad_components.compute();
        let forged2 = RotationStep {
            bank_hash: bad_bank_hash,
            bank_components: bad_components,
            // votes are still for the OLD bank_hash → none count for the new one.
            ..good_step.clone()
        };
        assert_eq!(
            rotate(&current, &forged2).unwrap_err(),
            ProvenanceError::RotationNotAttested
        );
    }
}
