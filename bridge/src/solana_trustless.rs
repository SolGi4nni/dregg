//! `dregg-bridge::solana_trustless`: the **trustless** inbound proof-of-lock for
//! the Solana `$DREGG` mirror — the honest upgrade from the trusted-oracle
//! attestation in [`crate::solana_mirror`].
//!
//! See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md` for the full design (Option A vs B,
//! the recommendation, the migration). The short of it:
//!
//! Today [`crate::solana_mirror::MirrorState::mint_against_lock`] trusts a
//! threshold [`crate::midnight::FederationAttestation`] that the Solana lock
//! happened. This module replaces that trusted *word* with a verifiable
//! *proof-of-lock* — a [`SolanaLockProof`] carrying Solana consensus evidence +
//! an account-inclusion proof — verified by [`verify_lock_proof_consensus`] and
//! routed through the SAME conservation accounting
//! ([`crate::solana_mirror::MirrorState::credit_lock`]) as the trusted path.
//!
//! # What is real vs. what is the remaining adapter layer
//!
//! The consensus verification is **no longer a stub.** It is the real
//! cryptographic check in [`crate::solana_consensus`]:
//!
//! - **Real (REACHES [`LockProofTrust::ConsensusVerified`]):** given a tracked
//!   per-epoch [`EpochStakeTable`], [`verify_lock_proof_consensus`] verifies that
//!   ≥ 2/3 of the epoch's active stake validly voted the claimed `bank_hash` at
//!   the claimed slot (real per-vote Ed25519 + stake-weighted sum + duplicate
//!   collapse), that the `bank_hash` recomputes from its committed components
//!   (binding the accounts hash + PoH tail to what was voted), that the vault
//!   account's lock record is included in that accounts hash (domain-separated
//!   sorted Merkle), and — when present — that the PoH tick chain links the
//!   slot's blockhash to a verified anchor.
//! - **Real (structural, [`LockProofTrust::StructureOnly`]):** [`verify_lock_proof`]
//!   checks proof structure + binding (well-formedness, the claim fields match
//!   the mirror config and the included record) and a *claimed-tally* sanity
//!   check, WITHOUT a stake table. It can never reach `ConsensusVerified`.
//! - **Remaining adapter layer (honest):** the cryptography and consensus
//!   arithmetic are real, but the mainnet **wire-format ingestion** is not yet
//!   reproduced — parsing real vote `Transaction`s into [`ValidatorVote`]s,
//!   sourcing/rotating the [`EpochStakeTable`] from Solana's stake program, the
//!   exact accounts-hash fan-out/preimage, and a bounded/recursive PoH anchor
//!   policy. See [`crate::solana_consensus`] for the precise modeled-vs-mainnet
//!   boundary.
//!
//! The [`LockProofTrust`] dial tells the caller exactly which level a given
//! verification achieved, so the structural check can never be mistaken for the
//! consensus check.

use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::solana_consensus::{
    BankHashComponents, EpochStakeTable, PohSegment, ValidatorVote, VoteSetError,
    verify_accounts_inclusion, verify_poh_segment, verify_supermajority,
};
use crate::solana_mirror::{MirrorError, MirrorMint, MirrorState};

/// Solana Tower-BFT consensus evidence for one slot: the voted bank hash, the
/// epoch + the real stake-weighted votes, the bank-hash components that bind the
/// accounts hash to the voted hash, and (optionally) the PoH linkage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusEvidence {
    /// The Solana slot the lock was finalized in.
    pub slot: u64,
    /// The bank hash the super-majority voted (the state commitment for `slot`).
    pub bank_hash: [u8; 32],
    /// The epoch whose [`EpochStakeTable`] weights these votes.
    pub epoch: u64,
    /// **Claimed** voted stake — a hint used only by the structure-only
    /// [`verify_lock_proof`] sanity check. The real path
    /// ([`verify_lock_proof_consensus`]) IGNORES this and recomputes the voted
    /// stake from `votes` against the tracked stake table.
    pub voted_stake: u128,
    /// **Claimed** total stake — a hint, as `voted_stake`.
    pub total_stake: u128,
    /// The real per-validator Ed25519 votes for `(slot, bank_hash)`. The
    /// consensus path verifies each signature and stake-weights the valid ones.
    pub votes: Vec<ValidatorVote>,
    /// The components the bank hash commits to (parent hash, accounts hash,
    /// signature count, PoH tail). Recomputed and bound to `bank_hash`.
    pub bank_components: BankHashComponents,
    /// Optional PoH segment linking a verified anchor to the slot's blockhash
    /// (`bank_components.last_blockhash`). When present it is verified.
    pub poh: Option<PohSegment>,
}

/// Inclusion proof that the Solana vault account, in the proven bank state,
/// records the lock of `recorded_amount` bound to `recorded_recipient`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccountInclusionProof {
    /// The Solana vault account pubkey that custodies locked `$DREGG`.
    pub vault_account: [u8; 32],
    /// The amount recorded as locked by this account state.
    pub recorded_amount: u64,
    /// The dregg recipient the lock record binds the mint to.
    pub recorded_recipient: CellId,
    /// The lock id recorded (the replay nonce; matches the bound claim).
    pub recorded_lock_id: [u8; 32],
    /// The accounts hash the bank hash commits to (the root the path proves into).
    pub accounts_hash: [u8; 32],
    /// The sibling path of `vault_account`'s lock-record leaf into
    /// `accounts_hash`, folded with the domain-separated sorted-Merkle node hash
    /// ([`crate::solana_consensus::merkle_node`]).
    pub merkle_path: Vec<[u8; 32]>,
}

/// A verifiable proof that `amount` of `spl_mint` was locked on a finalized
/// Solana slot, bound for `dregg_recipient` inside dregg. The trustless
/// counterpart of [`crate::solana_mirror::SolanaLockAttestation`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolanaLockProof {
    /// Unique id of the Solana lock event (replay nonce).
    pub lock_id: [u8; 32],
    /// The SPL mint pubkey of the locked token (`$DREGG` on Solana).
    pub spl_mint: [u8; 32],
    /// Amount locked, in the token's atomic units.
    pub amount: u64,
    /// The dregg cell that should receive the mirrored asset.
    pub dregg_recipient: CellId,
    /// Solana Tower-BFT consensus evidence for the lock's slot.
    pub consensus: ConsensusEvidence,
    /// Inclusion of the vault account (with the lock record) into the bank state.
    pub inclusion: AccountInclusionProof,
}

/// The trust level a verification call actually achieved.
///
/// This is the honesty dial: it tells the caller whether the consensus
/// verification — the part that makes the bridge trustless — actually ran.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LockProofTrust {
    /// Only the proof's STRUCTURE and BINDING were checked (well-formedness +
    /// the claim fields match), plus a claimed-tally sanity check — WITHOUT a
    /// stake table. Reached by [`verify_lock_proof`]. NOT a trustless guarantee.
    StructureOnly,
    /// Solana consensus was genuinely verified against a tracked stake table:
    /// real Ed25519 stake-weighted ≥ 2/3 votes on the bank hash, the bank-hash
    /// component binding, the accounts-hash inclusion of the lock record, and
    /// (when present) the PoH linkage. Reached by [`verify_lock_proof_consensus`].
    ConsensusVerified,
}

/// Why a [`SolanaLockProof`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LockProofError {
    /// The proof is for a different SPL mint than this mirror.
    WrongMint,
    /// Amount is below the configured dust floor.
    BelowMin,
    /// Amount exceeds the configured per-lock maximum.
    AboveMax,
    /// The inclusion proof's recorded fields do not match the bound claim
    /// (amount / recipient / lock_id mismatch — the proof binds to a different
    /// lock than it claims).
    ClaimMismatch,
    /// The proof is structurally empty/ill-formed (no votes, empty inclusion
    /// path, or a zero claimed-stake denominator).
    Malformed,
    /// The voted stake does not meet the ≥ 2/3 threshold of total stake.
    ///
    /// In [`verify_lock_proof`] this is the *claimed-tally* sanity check; in
    /// [`verify_lock_proof_consensus`] the `voted`/`total` are the REAL
    /// cryptographically-counted stake against the tracked stake table.
    StakeBelowThreshold {
        /// The voted stake (claimed, or real in the consensus path).
        voted: u128,
        /// The total stake (claimed, or real in the consensus path).
        total: u128,
    },
    /// The proof's evidence epoch does not match the supplied stake table's epoch
    /// — the wrong epoch's stake distribution would be applied.
    WrongEpoch {
        /// The epoch the evidence claims.
        evidence: u64,
        /// The epoch the stake table is for.
        table: u64,
    },
    /// The bank-hash components do not recompute to the voted `bank_hash`, or the
    /// accounts hash they commit to does not match the inclusion proof's root.
    BankHashMismatch,
    /// The vault account's lock record does not include into the voted bank
    /// state's accounts hash via the supplied path.
    AccountsInclusionInvalid,
    /// The PoH segment is present but does not verify (bad tick chain, or its
    /// tail is not the slot's blockhash).
    PohInvalid,
    /// PoH verification was required but no PoH segment was supplied.
    PohMissing,
}

impl std::fmt::Display for LockProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongMint => write!(f, "lock proof is for a different SPL mint"),
            Self::BelowMin => write!(f, "amount below the mirror minimum"),
            Self::AboveMax => write!(f, "amount above the per-lock maximum"),
            Self::ClaimMismatch => write!(f, "inclusion proof fields do not match the bound claim"),
            Self::Malformed => write!(f, "lock proof is structurally ill-formed"),
            Self::StakeBelowThreshold { voted, total } => write!(
                f,
                "voted stake {voted} does not meet the 2/3 threshold of total stake {total}"
            ),
            Self::WrongEpoch { evidence, table } => write!(
                f,
                "evidence epoch {evidence} does not match stake-table epoch {table}"
            ),
            Self::BankHashMismatch => {
                write!(f, "bank-hash components do not bind the voted bank hash")
            }
            Self::AccountsInclusionInvalid => {
                write!(
                    f,
                    "vault account lock record is not included in the voted accounts hash"
                )
            }
            Self::PohInvalid => write!(f, "PoH segment does not verify against the slot blockhash"),
            Self::PohMissing => write!(f, "PoH verification required but no segment supplied"),
        }
    }
}

impl std::error::Error for LockProofError {}

/// Error from the mint-against-proof methods: either the proof failed to verify,
/// or the (verified) mint broke the mirror's accounting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofMintError {
    /// The lock proof did not verify.
    Proof(LockProofError),
    /// The proof verified, but crediting the lock broke mirror accounting
    /// (replay / conservation / overflow).
    Mint(MirrorError),
}

impl std::fmt::Display for ProofMintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Proof(e) => write!(f, "lock proof verification failed: {e}"),
            Self::Mint(e) => write!(f, "mint accounting failed: {e}"),
        }
    }
}

impl std::error::Error for ProofMintError {}

/// Check the proof's structure and binding (mint, amount bounds, the included
/// record matches the bound claim, non-empty votes + inclusion path). Shared by
/// both the structure-only and consensus paths.
fn check_binding(
    proof: &SolanaLockProof,
    spl_mint: &[u8; 32],
    min_amount: u64,
    max_amount: u64,
) -> Result<(), LockProofError> {
    // (1) config binding.
    if proof.spl_mint != *spl_mint {
        return Err(LockProofError::WrongMint);
    }
    if proof.amount < min_amount {
        return Err(LockProofError::BelowMin);
    }
    if proof.amount > max_amount {
        return Err(LockProofError::AboveMax);
    }

    // (2) the inclusion proof must bind to exactly the claimed lock.
    let inc = &proof.inclusion;
    if inc.recorded_amount != proof.amount
        || inc.recorded_recipient != proof.dregg_recipient
        || inc.recorded_lock_id != proof.lock_id
    {
        return Err(LockProofError::ClaimMismatch);
    }

    // (3) structural well-formedness.
    if proof.consensus.votes.is_empty() || inc.merkle_path.is_empty() {
        return Err(LockProofError::Malformed);
    }
    Ok(())
}

/// Verify a Solana lock proof's **structure and binding only**, WITHOUT a stake
/// table. Returns [`LockProofTrust::StructureOnly`] — the consensus is NOT
/// verified, so this is NOT a trustless guarantee. Use
/// [`verify_lock_proof_consensus`] for the real trustless check.
///
/// Checks (all real): the mint/amount config binding, that the included record
/// matches the bound claim, well-formedness, and a *claimed-tally* sanity check
/// (`voted/total ≥ 2/3` over the untrusted claimed scalars).
pub fn verify_lock_proof(
    proof: &SolanaLockProof,
    spl_mint: &[u8; 32],
    min_amount: u64,
    max_amount: u64,
) -> Result<LockProofTrust, LockProofError> {
    check_binding(proof, spl_mint, min_amount, max_amount)?;

    // Claimed-tally structural sanity (a hint, NOT a consensus check).
    let c = &proof.consensus;
    if c.total_stake == 0 {
        return Err(LockProofError::Malformed);
    }
    if c.voted_stake.saturating_mul(3) < c.total_stake.saturating_mul(2) {
        return Err(LockProofError::StakeBelowThreshold {
            voted: c.voted_stake,
            total: c.total_stake,
        });
    }
    Ok(LockProofTrust::StructureOnly)
}

/// Verify a Solana lock proof against a **tracked epoch stake table** — the real
/// trustless check. Returns [`LockProofTrust::ConsensusVerified`] only when:
///
/// 1. structure + binding pass ([`check_binding`]);
/// 2. the evidence epoch matches `stake_table.epoch`;
/// 3. ≥ 2/3 of the epoch's active stake validly voted the claimed `(slot,
///    bank_hash)` — real per-vote Ed25519 + stake-weighted sum;
/// 4. the bank-hash components recompute to the voted `bank_hash` and commit to
///    the inclusion proof's `accounts_hash`;
/// 5. the vault account's lock record is included in that accounts hash;
/// 6. if `require_poh` (or a PoH segment is present), the PoH tick chain links
///    the anchor to the slot's blockhash.
pub fn verify_lock_proof_consensus(
    proof: &SolanaLockProof,
    spl_mint: &[u8; 32],
    min_amount: u64,
    max_amount: u64,
    stake_table: &EpochStakeTable,
    require_poh: bool,
) -> Result<LockProofTrust, LockProofError> {
    check_binding(proof, spl_mint, min_amount, max_amount)?;
    verify_consensus(&proof.consensus, &proof.inclusion, stake_table, require_poh)?;
    Ok(LockProofTrust::ConsensusVerified)
}

/// The real Solana-consensus verification (see [`verify_lock_proof_consensus`]).
fn verify_consensus(
    consensus: &ConsensusEvidence,
    inclusion: &AccountInclusionProof,
    stake_table: &EpochStakeTable,
    require_poh: bool,
) -> Result<(), LockProofError> {
    // (2) the stake table must be for the evidence's epoch.
    if stake_table.epoch != consensus.epoch {
        return Err(LockProofError::WrongEpoch {
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
        Err(VoteSetError::EmptyStakeTable) => return Err(LockProofError::Malformed),
        Err(VoteSetError::StakeBelowSupermajority { voted, total }) => {
            return Err(LockProofError::StakeBelowThreshold { voted, total });
        }
    }

    // (4) bind the accounts hash (and PoH tail) to the voted bank hash.
    if consensus.bank_components.accounts_hash != inclusion.accounts_hash
        || !consensus.bank_components.binds(&consensus.bank_hash)
    {
        return Err(LockProofError::BankHashMismatch);
    }

    // (5) the vault account's lock record must include into that accounts hash.
    if !verify_accounts_inclusion(
        &inclusion.vault_account,
        inclusion.recorded_amount,
        &inclusion.recorded_recipient,
        &inclusion.recorded_lock_id,
        &inclusion.merkle_path,
        &inclusion.accounts_hash,
    ) {
        return Err(LockProofError::AccountsInclusionInvalid);
    }

    // (6) PoH linkage: if present it must verify and tail at the slot blockhash;
    // if required and absent, refuse.
    match &consensus.poh {
        Some(seg) => {
            if verify_poh_segment(seg).is_err()
                || seg.tail_hash != consensus.bank_components.last_blockhash
            {
                return Err(LockProofError::PohInvalid);
            }
        }
        None => {
            if require_poh {
                return Err(LockProofError::PohMissing);
            }
        }
    }

    Ok(())
}

impl MirrorState {
    /// **Structure-only** mirror-mint against a [`SolanaLockProof`] — verifies
    /// structure + binding (NOT consensus) via [`verify_lock_proof`], then routes
    /// through the SAME [`MirrorState::credit_lock`] accounting the trusted path
    /// uses. Returns [`LockProofTrust::StructureOnly`]; use
    /// [`MirrorState::mint_against_lock_proof_consensus`] for the trustless mint.
    ///
    /// On any error the state is left unchanged.
    pub fn mint_against_lock_proof(
        &mut self,
        proof: &SolanaLockProof,
    ) -> Result<(MirrorMint, LockProofTrust), ProofMintError> {
        let trust = verify_lock_proof(
            proof,
            &self.config.spl_mint,
            self.config.min_amount,
            self.config.max_amount,
        )
        .map_err(ProofMintError::Proof)?;

        let mint = self
            .credit_lock(proof.lock_id, proof.amount, proof.dregg_recipient)
            .map_err(ProofMintError::Mint)?;

        Ok((mint, trust))
    }

    /// **Trustless** mirror-mint against a [`SolanaLockProof`], verified against
    /// a tracked epoch `stake_table` via [`verify_lock_proof_consensus`]. Routes
    /// through the SAME [`MirrorState::credit_lock`] accounting — only the lock
    /// *evidence* (verified consensus proof vs trusted signature) differs.
    /// Returns [`LockProofTrust::ConsensusVerified`].
    ///
    /// On any error the state is left unchanged.
    pub fn mint_against_lock_proof_consensus(
        &mut self,
        proof: &SolanaLockProof,
        stake_table: &EpochStakeTable,
        require_poh: bool,
    ) -> Result<(MirrorMint, LockProofTrust), ProofMintError> {
        let trust = verify_lock_proof_consensus(
            proof,
            &self.config.spl_mint,
            self.config.min_amount,
            self.config.max_amount,
            stake_table,
            require_poh,
        )
        .map_err(ProofMintError::Proof)?;

        let mint = self
            .credit_lock(proof.lock_id, proof.amount, proof.dregg_recipient)
            .map_err(ProofMintError::Mint)?;

        Ok((mint, trust))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::midnight::EpochKey;
    use crate::solana_consensus::{account_leaf, merkle_node};
    use crate::solana_mirror::MirrorConfig;
    use dregg_turn::action::Effect;
    use ed25519_dalek::SigningKey;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    const SPL_MINT: [u8; 32] = [0xABu8; 32];
    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];
    const EPOCH: u64 = 5;

    fn config() -> MirrorConfig {
        let o = SigningKey::from_bytes(&[7u8; 32]);
        MirrorConfig {
            spl_mint: SPL_MINT,
            asset: MIRROR_ASSET,
            oracle_keys: vec![EpochKey {
                from_epoch: 0,
                to_epoch: None,
                pubkey: o.verifying_key().to_bytes(),
            }],
            min_amount: 1,
            max_amount: 1_000_000,
        }
    }

    fn vk(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// Three validators with 400/400/200 stake. The first two (800/1000 = 80%)
    /// clear the 2/3 threshold.
    fn stake_table() -> EpochStakeTable {
        EpochStakeTable::from_entries(
            EPOCH,
            [
                (vk(11).verifying_key().to_bytes(), 400),
                (vk(12).verifying_key().to_bytes(), 400),
                (vk(13).verifying_key().to_bytes(), 200),
            ],
        )
    }

    /// A fully real, consensus-grade proof: real Ed25519 votes from ≥2/3 stake,
    /// a bank hash that recomputes from its components, a real accounts-inclusion
    /// path, and a real PoH segment.
    fn consensus_grade(amount: u64, recipient: CellId, lock_id: u8) -> SolanaLockProof {
        let slot = 12_345u64;
        let vault = [0x22u8; 32];
        let lid = [lock_id; 32];

        // Accounts hash: include the lock-record leaf with one sibling.
        let leaf = account_leaf(&vault, amount, &recipient, &lid);
        let sib = [0xEEu8; 32];
        let accounts_hash = merkle_node(&leaf, &sib);

        // PoH: a short real tick chain ending at the slot's last_blockhash.
        use sha2::{Digest, Sha256};
        let anchor = [0x55u8; 32];
        let mut tail = anchor;
        for _ in 0..256u64 {
            let mut h = Sha256::new();
            h.update(tail);
            tail = h.finalize().into();
        }

        let bank_components = BankHashComponents {
            parent_bank_hash: [0x01; 32],
            accounts_hash,
            signature_count: 3,
            last_blockhash: tail,
        };
        let bank_hash = bank_components.compute();

        // Real votes from the two big validators (800/1000 stake).
        let votes = vec![
            ValidatorVote::sign(&vk(11), slot, bank_hash),
            ValidatorVote::sign(&vk(12), slot, bank_hash),
        ];

        SolanaLockProof {
            lock_id: lid,
            spl_mint: SPL_MINT,
            amount,
            dregg_recipient: recipient,
            consensus: ConsensusEvidence {
                slot,
                bank_hash,
                epoch: EPOCH,
                voted_stake: 800,
                total_stake: 1000,
                votes,
                bank_components,
                poh: Some(PohSegment {
                    anchor_hash: anchor,
                    num_hashes: 256,
                    tail_hash: tail,
                }),
            },
            inclusion: AccountInclusionProof {
                vault_account: vault,
                recorded_amount: amount,
                recorded_recipient: recipient,
                recorded_lock_id: lid,
                accounts_hash,
                merkle_path: vec![sib],
            },
        }
    }

    // ---- structure-only path (no stake table) ------------------------------

    #[test]
    fn well_formed_proof_accepted_as_structure_only() {
        let cfg = config();
        let proof = consensus_grade(500, cid(1), 1);
        let trust =
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).expect("ok");
        assert_eq!(trust, LockProofTrust::StructureOnly);
    }

    #[test]
    fn mint_against_proof_credits_through_same_accounting() {
        let mut mirror = MirrorState::new(config());
        let recipient = cid(1);
        let (mint, trust) = mirror
            .mint_against_lock_proof(&consensus_grade(500, recipient, 1))
            .expect("a well-formed proof mirror-mints");

        assert_eq!(trust, LockProofTrust::StructureOnly);
        assert_eq!(mint.amount, 500);
        match mint.effect {
            Effect::Mint { target, amount, .. } => {
                assert_eq!(target, recipient);
                assert_eq!(amount, 500);
            }
            ref other => panic!("expected Effect::Mint, got {other:?}"),
        }
        assert_eq!(mirror.live_supply, 500);
        assert_eq!(mirror.currently_locked, 500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn double_mint_via_proof_is_rejected() {
        let mut mirror = MirrorState::new(config());
        let proof = consensus_grade(500, cid(1), 1);
        mirror.mint_against_lock_proof(&proof).expect("first ok");
        assert_eq!(
            mirror.mint_against_lock_proof(&proof).unwrap_err(),
            ProofMintError::Mint(MirrorError::DuplicateLock)
        );
        assert_eq!(mirror.live_supply, 500);
    }

    #[test]
    fn malformed_proof_refused_empty_votes() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.votes.clear();
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::Malformed
        );
    }

    #[test]
    fn malformed_proof_refused_empty_inclusion_path() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.inclusion.merkle_path.clear();
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::Malformed
        );
    }

    #[test]
    fn claim_mismatch_refused() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.inclusion.recorded_recipient = cid(9);
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::ClaimMismatch
        );

        let mut proof2 = consensus_grade(500, cid(1), 2);
        proof2.inclusion.recorded_amount = 501;
        assert_eq!(
            verify_lock_proof(&proof2, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::ClaimMismatch
        );
    }

    #[test]
    fn wrong_mint_refused() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.spl_mint = [0xFF; 32];
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::WrongMint
        );
    }

    #[test]
    fn amount_bounds_enforced() {
        let cfg = config();
        let below = consensus_grade(0, cid(1), 1);
        assert_eq!(
            verify_lock_proof(&below, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::BelowMin
        );
        let above = consensus_grade(2_000_000, cid(1), 2);
        assert_eq!(
            verify_lock_proof(&above, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::AboveMax
        );
    }

    #[test]
    fn claimed_stake_below_threshold_refused() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.voted_stake = 600;
        proof.consensus.total_stake = 1000;
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::StakeBelowThreshold {
                voted: 600,
                total: 1000
            }
        );
    }

    // ---- consensus path (real verification against a stake table) ----------

    #[test]
    fn consensus_verified_for_genuine_lock() {
        let cfg = config();
        let proof = consensus_grade(500, cid(1), 1);
        let trust = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            true, // require PoH — the proof carries a real segment
        )
        .expect("genuine lock verifies consensus");
        assert_eq!(trust, LockProofTrust::ConsensusVerified);
    }

    #[test]
    fn consensus_mint_credits_and_reports_verified() {
        let mut mirror = MirrorState::new(config());
        let recipient = cid(1);
        let (mint, trust) = mirror
            .mint_against_lock_proof_consensus(
                &consensus_grade(500, recipient, 1),
                &stake_table(),
                true,
            )
            .expect("trustless mint");
        assert_eq!(trust, LockProofTrust::ConsensusVerified);
        assert_eq!(mint.amount, 500);
        assert_eq!(mirror.live_supply, 500);
        assert_eq!(mirror.currently_locked, 500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn consensus_refused_below_two_thirds() {
        let cfg = config();
        // Drop one big vote: only 400/1000 = 40% of real stake votes.
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.votes.truncate(1);
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        assert_eq!(
            err,
            LockProofError::StakeBelowThreshold {
                voted: 400,
                total: 1000
            }
        );
    }

    #[test]
    fn consensus_refused_forged_vote_signature() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        // Corrupt the second vote's signature: it no longer verifies, so only
        // 400/1000 of real stake remains — below 2/3.
        proof.consensus.votes[1].signature[0] ^= 0xFF;
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        assert_eq!(
            err,
            LockProofError::StakeBelowThreshold {
                voted: 400,
                total: 1000
            }
        );
    }

    #[test]
    fn consensus_refused_inclusion_against_wrong_bank_hash() {
        let cfg = config();
        // Tamper the inclusion's accounts_hash so it no longer matches the
        // bank-hash components — the accounts hash is not the voted one.
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.inclusion.accounts_hash[0] ^= 0xFF;
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        assert_eq!(err, LockProofError::BankHashMismatch);
    }

    #[test]
    fn consensus_refused_tampered_bank_hash() {
        let cfg = config();
        // The votes are over a bank_hash that no longer recomputes from the
        // components (and the votes would not match it either).
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.bank_hash[0] ^= 0xFF;
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        // The votes are for the old bank_hash, so none count for the new one →
        // zero voted stake → below threshold.
        assert_eq!(
            err,
            LockProofError::StakeBelowThreshold {
                voted: 0,
                total: 1000
            }
        );
    }

    #[test]
    fn consensus_refused_tampered_inclusion_record() {
        let cfg = config();
        // Inflate the recorded amount AND the claim so binding passes but the
        // Merkle leaf no longer matches the committed accounts hash.
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.amount = 600;
        proof.inclusion.recorded_amount = 600;
        // bank_components.accounts_hash still commits the old (500) leaf root.
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        assert_eq!(err, LockProofError::AccountsInclusionInvalid);
    }

    #[test]
    fn consensus_refused_wrong_epoch() {
        let cfg = config();
        let proof = consensus_grade(500, cid(1), 1);
        let wrong_epoch_table =
            EpochStakeTable::from_entries(EPOCH + 1, [(vk(11).verifying_key().to_bytes(), 800)]);
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &wrong_epoch_table,
            false,
        )
        .unwrap_err();
        assert_eq!(
            err,
            LockProofError::WrongEpoch {
                evidence: EPOCH,
                table: EPOCH + 1
            }
        );
    }

    #[test]
    fn consensus_refused_bad_poh() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        if let Some(seg) = proof.consensus.poh.as_mut() {
            seg.tail_hash[0] ^= 0xFF; // tail no longer matches the chain
        }
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .unwrap_err();
        assert_eq!(err, LockProofError::PohInvalid);
    }

    #[test]
    fn consensus_refused_missing_required_poh() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.poh = None;
        let err = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            true, // require PoH
        )
        .unwrap_err();
        assert_eq!(err, LockProofError::PohMissing);
    }

    #[test]
    fn consensus_ok_without_poh_when_not_required() {
        let cfg = config();
        let mut proof = consensus_grade(500, cid(1), 1);
        proof.consensus.poh = None;
        let trust = verify_lock_proof_consensus(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &stake_table(),
            false,
        )
        .expect("ok without PoH when not required");
        assert_eq!(trust, LockProofTrust::ConsensusVerified);
    }
}
