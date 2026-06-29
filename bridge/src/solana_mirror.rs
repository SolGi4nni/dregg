//! `dregg-bridge::solana_mirror`: mirror a Solana/pump.fun SPL token (`$DREGG`)
//! into dregg's value layer as a first-class conserved, `Payable` asset.
//!
//! See `docs/deos/TOKEN-MIRROR-BRIDGE.md` for the full design. The short of it:
//!
//! ```text
//!  Solana: user locks N $DREGG  ──►  oracle threshold-attests the lock
//!                                          │
//!                                          ▼
//!                              MirrorState.mint_against_lock
//!                              → Effect::Mint { target, amount }  (well-debited, Σδ=0)
//!                                          │  (ordinary dregg asset)
//!                                          ▼
//!                              dregg_payable::resolve_pay → Effect::Transfer
//!                              → pays an execution-lease / ToolGateway charge
//!  redeem: Effect::Burn(mirror) ──► SolanaUnlockRequest ──► oracle unlocks on Solana
//! ```
//!
//! # Trust model (honest)
//!
//! This is a **trusted-oracle / validator-set** mirror. dregg trusts a threshold
//! [`crate::midnight::FederationAttestation`] (an Ed25519/Schnorr signature
//! aggregated to one epoch key — the SAME shape the `midnight` bridge uses) that
//! a lock happened on Solana. It does NOT verify Solana consensus. The trustless
//! upgrade — a Solana light client or an inbound zk-proof-of-lock — is named in
//! the design doc but not built; note that the ETH `STARK→SNARK→EVM` *settlement*
//! pattern in [`crate::ethereum`] does NOT supply it (that is outbound, and
//! Solana's consensus/account model differs from Ethereum's).
//!
//! # What is real here
//!
//! The dregg-side mechanism: attestation verification, replay dedup, amount
//! bounds, the conservation invariant `live_supply ≤ currently_locked`, and the
//! production of the REAL kernel effects ([`dregg_turn::action::Effect::Mint`] /
//! [`Burn`](dregg_turn::action::Effect::Burn) / and the payment
//! [`Transfer`](dregg_turn::action::Effect::Transfer) via
//! [`dregg_payable::resolve_pay`]). No new kernel verb is introduced.

use std::collections::BTreeSet;

use dregg_cell::Nullifier;
use dregg_turn::action::Effect;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::midnight::{EpochKey, FederationAttestation};

/// Domain separation for the Solana-lock attestation payload, distinct from the
/// `midnight` bridge domain so an attestation for one bridge can never be
/// replayed against the other.
pub const SOLANA_MIRROR_DOMAIN: &str = "dregg-solana-mirror-v1";

/// Domain separation for the COMMITTED consume-once lock nullifier (the
/// concurrency-safe double-mint gate, `docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md`
/// §3). Distinct from [`SOLANA_MIRROR_DOMAIN`] (the attestation-signature domain)
/// and from the Stripe nullifier domain.
pub const SOLANA_LOCK_NULLIFIER_DOMAIN: &str = "dregg-solana-lock-v1";

/// Derive the domain-separated, consume-once nullifier for a Solana lock.
///
/// `nf = H("dregg-solana-lock-v1" ‖ spl_mint ‖ lock_id)`. Binding `spl_mint`
/// scopes the nullifier to this mirror so a `lock_id` from another mirror can
/// never collide. This is the value gated against the executor's committed
/// `note_nullifiers` set in [`dregg_turn::executor::bridge_ledger`] — so a
/// `lock_id` is consumed exactly once GLOBALLY, regardless of how many relayer
/// processes observe the same lock.
pub fn lock_nullifier(spl_mint: &[u8; 32], lock_id: &[u8; 32]) -> Nullifier {
    let mut h = blake3::Hasher::new_derive_key(SOLANA_LOCK_NULLIFIER_DOMAIN);
    h.update(spl_mint);
    h.update(lock_id);
    Nullifier(*h.finalize().as_bytes())
}

/// The verified, committed-bridge-ready facts of a Solana lock: the consume-once
/// nullifier plus the mint target/amount. Produced by [`MirrorState::verify_lock`]
/// WITHOUT mutating any per-relayer RAM — the authority is committed state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedLock {
    /// The domain-separated consume-once lock nullifier (see [`lock_nullifier`]).
    pub lock_nullifier: Nullifier,
    /// The dregg cell to credit the mirrored asset.
    pub recipient: CellId,
    /// The amount to mint.
    pub amount: u64,
}

/// An attested claim that `amount` of the SPL token `spl_mint` was locked on
/// Solana, bound for `dregg_recipient` inside dregg.
///
/// The `attestation` is the trusted leg: a threshold signature by the oracle /
/// validator set over [`SolanaLockAttestation::canonical_payload`] under the
/// epoch key. The `lock_id` (e.g. the Solana lock-transaction signature hash) is
/// the replay nonce.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolanaLockAttestation {
    /// Unique id of the Solana lock event (replay nonce). Typically the lock
    /// transaction signature hashed to 32 bytes.
    pub lock_id: [u8; 32],
    /// The SPL mint pubkey of the locked token (`$DREGG` on Solana). 32 bytes.
    pub spl_mint: [u8; 32],
    /// Amount locked, in the token's atomic units.
    pub amount: u64,
    /// The dregg cell that should receive the mirrored asset.
    pub dregg_recipient: CellId,
    /// The oracle-set epoch under which the attestation was produced (selects
    /// the verifying key, exactly like the `midnight` bridge).
    pub epoch: u64,
    /// The threshold attestation over the canonical payload.
    pub attestation: FederationAttestation,
}

impl SolanaLockAttestation {
    /// Canonical bytes signed by the oracle set:
    /// `lock_id || spl_mint || amount_le || recipient || epoch_le`.
    pub fn canonical_payload(&self) -> Vec<u8> {
        let mut p = Vec::with_capacity(32 + 32 + 8 + 32 + 8);
        p.extend_from_slice(&self.lock_id);
        p.extend_from_slice(&self.spl_mint);
        p.extend_from_slice(&self.amount.to_le_bytes());
        p.extend_from_slice(self.dregg_recipient.as_bytes());
        p.extend_from_slice(&self.epoch.to_le_bytes());
        p
    }

    /// Domain-separated message hash the oracle signs.
    pub fn message_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key(SOLANA_MIRROR_DOMAIN);
        h.update(&self.canonical_payload());
        *h.finalize().as_bytes()
    }

    /// Build a signed attestation (oracle-side helper / test helper).
    pub fn create(
        lock_id: [u8; 32],
        spl_mint: [u8; 32],
        amount: u64,
        dregg_recipient: CellId,
        epoch: u64,
        signing_key: &ed25519_dalek::SigningKey,
    ) -> Self {
        use ed25519_dalek::Signer;
        // Build the payload-bearing struct first, then sign its message hash so
        // the attestation binds to exactly these fields.
        let proto = Self {
            lock_id,
            spl_mint,
            amount,
            dregg_recipient,
            epoch,
            attestation: FederationAttestation {
                message_hash: [0u8; 32],
                signature: Vec::new(),
                epoch,
                federation_pubkey: signing_key.verifying_key().to_bytes().to_vec(),
            },
        };
        let message_hash = proto.message_hash();
        let signature = signing_key.sign(&message_hash).to_bytes().to_vec();
        Self {
            attestation: FederationAttestation {
                message_hash,
                signature,
                epoch,
                federation_pubkey: signing_key.verifying_key().to_bytes().to_vec(),
            },
            ..proto
        }
    }

    /// Verify the attestation binds to THIS claim under `oracle_pubkey`.
    ///
    /// Checks (a) the attestation's `message_hash` equals the recomputed,
    /// domain-separated hash of these fields (so the signed bytes cannot be
    /// swapped under the recipient/amount), and (b) the Ed25519 signature is
    /// valid for that hash under the epoch oracle key.
    pub fn verify_under(&self, oracle_pubkey: &[u8; 32]) -> bool {
        if self.attestation.message_hash != self.message_hash() {
            return false;
        }
        self.attestation.verify(oracle_pubkey)
    }
}

/// A request to unlock `amount` of `spl_mint` on Solana, emitted when a mirror
/// holder redeems (burns) their mirrored asset. The oracle / validator set acts
/// on this to release the locked tokens.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolanaUnlockRequest {
    /// The SPL mint to unlock.
    pub spl_mint: [u8; 32],
    /// Amount to unlock (Solana atomic units), equals the burned mirror amount.
    pub amount: u64,
    /// The Solana recipient (32-byte account pubkey) to receive the unlocked tokens.
    pub solana_recipient: [u8; 32],
    /// Unique id of the redeem, for the oracle's own replay protection.
    pub redeem_id: [u8; 32],
}

/// Configuration for one mirrored SPL token.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorConfig {
    /// The SPL mint pubkey being mirrored (`$DREGG` on Solana).
    pub spl_mint: [u8; 32],
    /// The dregg `AssetId` of the mirror (= the mirror issuer-well cell id; mirror
    /// holders denominate value in this `token_id`).
    pub asset: [u8; 32],
    /// Oracle / validator-set verifying keys by epoch (reuses the bridge's
    /// [`EpochKey`] range model).
    pub oracle_keys: Vec<EpochKey>,
    /// Minimum lockable/mintable amount (dust floor).
    pub min_amount: u64,
    /// Maximum per-lock amount (above this, governance is required).
    pub max_amount: u64,
    /// **The canonical bridge vault account** (the Solana PDA that custodies
    /// locked `$DREGG`). A trustless lock proof MUST escrow INTO this account:
    /// proving that *some* account merely EXISTS on Solana is not enough to mint
    /// (red-team BR-2-B / BR-3 — without this an attacker plants a self-asserting
    /// lock blob in any ~0.001-SOL account, lands it in a genuine finalized
    /// accounts hash, and mints having escrowed nothing). The trustless mint
    /// rejects any proof whose `inclusion.vault_account` is not this account.
    pub vault_account: [u8; 32],
    /// **The bridge lock program** that owns the vault account. The mainnet
    /// inclusion proof's account `owner` must equal this — so the escrow is held
    /// by the bridge's own program, not an attacker-controlled account that
    /// merely shares the vault pubkey shape.
    pub lock_program: [u8; 32],
    /// Pinned weak-subjectivity anchor epoch (governance constant). When set
    /// alongside [`Self::pinned_anchor_root`], the anchored trustless mint
    /// REFUSES any caller-supplied anchor whose `(epoch, stake_table_root)` does
    /// not match — closing red-team BR-2-C (the anchor + stake table were
    /// per-call args an attacker could swap for a 100%-self-stake distribution).
    #[serde(default)]
    pub pinned_anchor_epoch: Option<u64>,
    /// Pinned weak-subjectivity anchor stake-table root (governance constant).
    /// See [`Self::pinned_anchor_epoch`].
    #[serde(default)]
    pub pinned_anchor_root: Option<[u8; 32]>,
}

impl MirrorConfig {
    /// Look up the oracle verifying key valid for `epoch`.
    pub fn key_for_epoch(&self, epoch: u64) -> Option<&[u8; 32]> {
        self.oracle_keys.iter().find_map(|ek| {
            let in_range = epoch >= ek.from_epoch && ek.to_epoch.is_none_or(|to| epoch <= to);
            if in_range { Some(&ek.pubkey) } else { None }
        })
    }
}

/// Why a mirror operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MirrorError {
    /// No oracle key registered for the attestation's epoch.
    NoKeyForEpoch(u64),
    /// The threshold attestation did not verify under the epoch oracle key.
    AttestationInvalid,
    /// The attestation is for a different SPL mint than this mirror.
    WrongMint,
    /// Amount is below the configured dust floor.
    BelowMin,
    /// Amount exceeds the configured per-lock maximum.
    AboveMax,
    /// This `lock_id` was already mirrored (double-mint prevention).
    DuplicateLock,
    /// Minting `amount` would push `live_supply` above `currently_locked`
    /// (the conservation invariant). This is a LIVE gate, not decorative: the
    /// escrow backing (`currently_locked`) is raised ONLY by an independently
    /// verified lock ([`MirrorState::record_escrow`]); a mint draws against it
    /// ([`MirrorState::draw_mint`]) and is refused here when it would exceed the
    /// backing — so a mint with no real escrow, or a second draw against an
    /// already-spent escrow, is rejected (red-team BR-3: conservation is now
    /// non-vacuous, not "credit both sides by the same amount").
    InsufficientLocked { live: u64, locked: u64, amount: u64 },
    /// Redeeming `amount` exceeds the circulating mirror supply.
    InsufficientMirrorSupply { live: u64, amount: u64 },
    /// An accounting addition overflowed `u64`.
    Overflow,
}

impl std::fmt::Display for MirrorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoKeyForEpoch(e) => write!(f, "no oracle key for epoch {e}"),
            Self::AttestationInvalid => write!(f, "lock attestation failed verification"),
            Self::WrongMint => write!(f, "attestation is for a different SPL mint"),
            Self::BelowMin => write!(f, "amount below the mirror minimum"),
            Self::AboveMax => write!(f, "amount above the per-lock maximum"),
            Self::DuplicateLock => write!(f, "lock_id already mirrored (double-mint prevented)"),
            Self::InsufficientLocked {
                live,
                locked,
                amount,
            } => write!(
                f,
                "mint of {amount} would break conservation: live {live} + {amount} > locked {locked}"
            ),
            Self::InsufficientMirrorSupply { live, amount } => {
                write!(
                    f,
                    "redeem of {amount} exceeds circulating mirror supply {live}"
                )
            }
            Self::Overflow => write!(f, "supply accounting overflow"),
        }
    }
}

impl std::error::Error for MirrorError {}

/// The dregg-side ledger of one mirrored SPL token.
///
/// Tracks the two quantities the conservation invariant relates:
/// - `currently_locked`: $DREGG currently locked on Solana (rises on an attested
///   lock, falls on a confirmed redeem).
/// - `live_supply`: mirror-$DREGG currently circulating inside dregg (rises on
///   mint, falls on burn/redeem).
///
/// **Invariant (checked after every op):** `live_supply ≤ currently_locked`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorState {
    /// The mirror configuration (mint, asset id, oracle keys, bounds).
    pub config: MirrorConfig,
    /// $DREGG currently locked on Solana (attested).
    pub currently_locked: u64,
    /// Mirror-$DREGG currently circulating inside dregg.
    pub live_supply: u64,
    /// Lock ids already mirrored — a per-relayer LOCAL fast-reject CACHE, NOT the
    /// global double-mint authority. The authoritative consume-once gate is the
    /// committed `note_nullifiers` set (see [`lock_nullifier`] +
    /// [`dregg_turn::executor::bridge_ledger`]): a second relayer with a fresh
    /// `seen_locks` is still refused by COMMITTED state. This cache only saves a
    /// round-trip for the single-relayer happy path.
    seen_locks: BTreeSet<[u8; 32]>,
    /// Redeem ids already issued.
    seen_redeems: BTreeSet<[u8; 32]>,
}

/// The output of a successful mirror-mint: the kernel effect to submit plus a
/// record of who/what was credited.
///
/// (`Effect` is not `PartialEq`, so this struct is not either; inspect `effect`
/// by pattern match.)
#[derive(Clone, Debug)]
pub struct MirrorMint {
    /// The REAL kernel mint effect: credits `recipient`, debits the mirror's
    /// issuer well as the conserving dual (`Effect::Mint` is `Generative`).
    pub effect: Effect,
    /// The recipient that was credited.
    pub recipient: CellId,
    /// The amount minted.
    pub amount: u64,
}

/// The output of a redeem: the kernel burn effect plus the Solana unlock request.
///
/// (`Effect` is not `PartialEq`, so this struct is not either; inspect `effect`
/// by pattern match.)
#[derive(Clone, Debug)]
pub struct MirrorRedeem {
    /// The REAL kernel burn effect (`Effect::Burn`, `Annihilative`).
    pub effect: Effect,
    /// The unlock request the oracle set acts on (Solana side).
    pub unlock: SolanaUnlockRequest,
    /// The amount burned/redeemed.
    pub amount: u64,
}

impl MirrorState {
    /// Create an empty mirror for `config` (nothing locked, nothing minted).
    pub fn new(config: MirrorConfig) -> Self {
        Self {
            config,
            currently_locked: 0,
            live_supply: 0,
            seen_locks: BTreeSet::new(),
            seen_redeems: BTreeSet::new(),
        }
    }

    /// The conservation invariant: circulating mirror supply never exceeds the
    /// amount locked on Solana.
    pub fn invariant_holds(&self) -> bool {
        self.live_supply <= self.currently_locked
    }

    /// Whether `lock_id` has already been mirrored.
    pub fn is_lock_seen(&self, lock_id: &[u8; 32]) -> bool {
        self.seen_locks.contains(lock_id)
    }

    /// **Mirror-mint against an attested Solana lock — RAM path, TEST/INTERNAL
    /// ONLY.**
    ///
    /// Verifies the threshold attestation, enforces replay/amount/mint bounds,
    /// records the escrow, and produces the REAL kernel [`Effect::Mint`].
    ///
    /// This is gated behind `#[cfg(any(test, feature = "test-utils"))]` and is
    /// NOT part of the production surface (red-team BR-1): its replay dedup is a
    /// per-process `seen_locks` set, so two relayer processes would double-mint
    /// one lock. The SOUND production path is [`Self::verify_lock`] →
    /// `dregg_turn::executor::bridge_ledger`'s `bridge_mint_against_lock`, whose
    /// committed `note_nullifiers` set is the GLOBAL double-mint authority.
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn mint_against_lock(
        &mut self,
        att: &SolanaLockAttestation,
    ) -> Result<MirrorMint, MirrorError> {
        if att.spl_mint != self.config.spl_mint {
            return Err(MirrorError::WrongMint);
        }
        if att.amount < self.config.min_amount {
            return Err(MirrorError::BelowMin);
        }
        if att.amount > self.config.max_amount {
            return Err(MirrorError::AboveMax);
        }
        if self.seen_locks.contains(&att.lock_id) {
            return Err(MirrorError::DuplicateLock);
        }
        let key = self
            .config
            .key_for_epoch(att.epoch)
            .ok_or(MirrorError::NoKeyForEpoch(att.epoch))?;
        if !att.verify_under(key) {
            return Err(MirrorError::AttestationInvalid);
        }

        self.credit_lock(att.lock_id, att.amount, att.dregg_recipient)
    }

    /// **Verify a lock attestation for the COMMITTED bridge mint, mutating no
    /// per-relayer RAM.**
    ///
    /// Runs exactly the same checks as [`Self::mint_against_lock`]
    /// (mint match, amount bounds, threshold attestation) but does NOT touch
    /// `seen_locks` / `currently_locked` / `live_supply`. It returns the
    /// consume-once [`VerifiedLock`] the caller feeds to
    /// [`dregg_turn::executor::bridge_ledger`]'s
    /// `TurnExecutor::bridge_mint_against_lock`, where the committed
    /// `note_nullifiers` set is the global double-mint authority and a committed
    /// cell is the supply source of truth.
    ///
    /// This is the SOUND multi-relayer path: any number of relayers may call
    /// `verify_lock` for the same lock and race the committed mint — exactly one
    /// wins (the first to consume the nullifier); the rest are refused by
    /// committed state, not by per-relayer `seen_locks`.
    pub fn verify_lock(&self, att: &SolanaLockAttestation) -> Result<VerifiedLock, MirrorError> {
        if att.spl_mint != self.config.spl_mint {
            return Err(MirrorError::WrongMint);
        }
        if att.amount < self.config.min_amount {
            return Err(MirrorError::BelowMin);
        }
        if att.amount > self.config.max_amount {
            return Err(MirrorError::AboveMax);
        }
        let key = self
            .config
            .key_for_epoch(att.epoch)
            .ok_or(MirrorError::NoKeyForEpoch(att.epoch))?;
        if !att.verify_under(key) {
            return Err(MirrorError::AttestationInvalid);
        }
        Ok(VerifiedLock {
            lock_nullifier: lock_nullifier(&att.spl_mint, &att.lock_id),
            recipient: att.dregg_recipient,
            amount: att.amount,
        })
    }

    /// **Record an independently-verified escrow**, raising `currently_locked`
    /// (the conservation backing) by `escrowed`. Deduped by `lock_id` so the same
    /// escrow can never inflate the backing twice.
    ///
    /// This is the INDEPENDENT source of `currently_locked` (red-team BR-3): the
    /// caller MUST have verified that `escrowed` was genuinely locked into the
    /// bridge's vault (a signed attestation, or a vault-bound consensus proof)
    /// BEFORE calling. The mint draws against this backing separately via
    /// [`Self::draw_mint`] — escrow and mint are NOT one fused credit, so
    /// conservation is a real constraint.
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub(crate) fn record_escrow(
        &mut self,
        lock_id: [u8; 32],
        escrowed: u64,
    ) -> Result<(), MirrorError> {
        if self.seen_locks.contains(&lock_id) {
            return Err(MirrorError::DuplicateLock);
        }
        let new_locked = self
            .currently_locked
            .checked_add(escrowed)
            .ok_or(MirrorError::Overflow)?;
        self.currently_locked = new_locked;
        self.seen_locks.insert(lock_id);
        Ok(())
    }

    /// **Draw a mint against the recorded escrow backing**, raising `live_supply`
    /// by `amount` and emitting the REAL [`Effect::Mint`]. This is where
    /// conservation BITES (red-team BR-3): if `live_supply + amount` would exceed
    /// `currently_locked` — i.e. the mint is not covered by independently-recorded
    /// escrow — it is refused with [`MirrorError::InsufficientLocked`]. A mint
    /// with no escrow at all (`currently_locked == 0`) is therefore rejected.
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub(crate) fn draw_mint(
        &mut self,
        amount: u64,
        recipient: CellId,
    ) -> Result<MirrorMint, MirrorError> {
        let new_live = self
            .live_supply
            .checked_add(amount)
            .ok_or(MirrorError::Overflow)?;
        if new_live > self.currently_locked {
            return Err(MirrorError::InsufficientLocked {
                live: self.live_supply,
                locked: self.currently_locked,
                amount,
            });
        }
        self.live_supply = new_live;
        debug_assert!(self.invariant_holds());

        Ok(MirrorMint {
            effect: Effect::Mint {
                target: recipient,
                slot: 0,
                amount,
            },
            recipient,
            amount,
        })
    }

    /// The shared lock-accounting routine, independent of how the lock is
    /// evidenced (trusted attestation vs trustless proof): record the escrow as
    /// the conservation backing, then draw the mint against it. The two steps are
    /// distinct accumulators (see [`Self::record_escrow`] / [`Self::draw_mint`]),
    /// so `InsufficientLocked` is genuinely reachable — not the old
    /// credit-both-sides-by-the-same-amount vacuity (red-team BR-3).
    ///
    /// Callers MUST have verified the lock evidence (signature or proof), the
    /// amount bounds / mint match, AND that the lock escrows into the bridge vault
    /// BEFORE calling this (see `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`).
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub(crate) fn credit_lock(
        &mut self,
        lock_id: [u8; 32],
        amount: u64,
        recipient: CellId,
    ) -> Result<MirrorMint, MirrorError> {
        self.record_escrow(lock_id, amount)?;
        match self.draw_mint(amount, recipient) {
            Ok(mint) => Ok(mint),
            Err(e) => {
                // Roll the escrow back so the whole op is atomic on failure.
                self.currently_locked = self.currently_locked.saturating_sub(amount);
                self.seen_locks.remove(&lock_id);
                Err(e)
            }
        }
    }

    /// **Redeem (burn) mirror-$DREGG and request the Solana unlock.**
    ///
    /// Produces the REAL kernel [`Effect::Burn`] over `holder` and a
    /// [`SolanaUnlockRequest`]; decrements both `live_supply` and
    /// `currently_locked` so the invariant is preserved.
    pub fn redeem(
        &mut self,
        holder: CellId,
        amount: u64,
        solana_recipient: [u8; 32],
        redeem_id: [u8; 32],
    ) -> Result<MirrorRedeem, MirrorError> {
        if amount < self.config.min_amount {
            return Err(MirrorError::BelowMin);
        }
        if self.seen_redeems.contains(&redeem_id) {
            return Err(MirrorError::DuplicateLock);
        }
        if amount > self.live_supply {
            return Err(MirrorError::InsufficientMirrorSupply {
                live: self.live_supply,
                amount,
            });
        }

        // live ≤ locked held before; subtracting `amount` from both preserves it.
        self.live_supply -= amount;
        self.currently_locked = self.currently_locked.saturating_sub(amount);
        self.seen_redeems.insert(redeem_id);
        debug_assert!(self.invariant_holds());

        Ok(MirrorRedeem {
            effect: Effect::Burn {
                target: holder,
                slot: 0,
                amount,
            },
            unlock: SolanaUnlockRequest {
                spl_mint: self.config.spl_mint,
                amount,
                solana_recipient,
                redeem_id,
            },
            amount,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_payable::{InvokeAuthority, InvokeRefused, resolve_pay};
    use ed25519_dalek::SigningKey;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn oracle() -> SigningKey {
        // Deterministic test oracle key.
        SigningKey::from_bytes(&[7u8; 32])
    }

    const SPL_MINT: [u8; 32] = [0xABu8; 32]; // pump.fun $DREGG mint
    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32]; // mirror issuer-well / token_id

    fn config(o: &SigningKey) -> MirrorConfig {
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
            vault_account: [0x22u8; 32],
            lock_program: [0x07u8; 32],
            pinned_anchor_epoch: None,
            pinned_anchor_root: None,
        }
    }

    fn lock(amount: u64, recipient: CellId, lock_id: u8, o: &SigningKey) -> SolanaLockAttestation {
        SolanaLockAttestation::create([lock_id; 32], SPL_MINT, amount, recipient, 0, o)
    }

    #[test]
    fn attestation_roundtrips_and_binds_fields() {
        let o = oracle();
        let att = lock(500, cid(1), 1, &o);
        assert!(att.verify_under(&o.verifying_key().to_bytes()));

        // Tampering the amount breaks the bound message hash (the recomputed
        // hash no longer matches the signed one).
        let mut tampered = att.clone();
        tampered.amount = 999;
        assert!(!tampered.verify_under(&o.verifying_key().to_bytes()));

        // A different key does not verify.
        let other = SigningKey::from_bytes(&[9u8; 32]);
        assert!(!att.verify_under(&other.verifying_key().to_bytes()));
    }

    #[test]
    fn mint_against_lock_produces_real_mint_and_conserves() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        let recipient = cid(1);

        let minted = mirror
            .mint_against_lock(&lock(500, recipient, 1, &o))
            .expect("a valid lock mirror-mints");

        assert_eq!(minted.amount, 500);
        assert_eq!(minted.recipient, recipient);
        match minted.effect {
            Effect::Mint {
                target,
                slot,
                amount,
            } => {
                assert_eq!(target, recipient);
                assert_eq!(slot, 0);
                assert_eq!(amount, 500);
            }
            ref other => panic!("expected Effect::Mint, got {other:?}"),
        }
        assert_eq!(mirror.live_supply, 500);
        assert_eq!(mirror.currently_locked, 500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn double_mint_is_rejected() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        let att = lock(500, cid(1), 1, &o);
        mirror.mint_against_lock(&att).expect("first mint ok");
        assert_eq!(
            mirror.mint_against_lock(&att).unwrap_err(),
            MirrorError::DuplicateLock
        );
        // No double credit.
        assert_eq!(mirror.live_supply, 500);
        assert_eq!(mirror.currently_locked, 500);
    }

    /// BR-3 (conservation is NON-VACUOUS): a mint draw with NO recorded escrow is
    /// rejected. Under the old "credit both sides by the same amount" accounting
    /// this was dead code (`live > locked` always false); now `currently_locked`
    /// is an independent backing the draw is checked against.
    #[test]
    fn draw_without_escrow_breaks_conservation() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        assert_eq!(mirror.currently_locked, 0);
        assert_eq!(
            mirror.draw_mint(500, cid(1)).unwrap_err(),
            MirrorError::InsufficientLocked {
                live: 0,
                locked: 0,
                amount: 500,
            }
        );
        // No mint happened.
        assert_eq!(mirror.live_supply, 0);
        assert!(mirror.invariant_holds());
    }

    /// BR-3: conservation BITES — minting more than the recorded escrow is
    /// rejected (the over-mint case), while minting WITHIN it succeeds (the
    /// true-and-false coverage that proves the gate is non-vacuous).
    #[test]
    fn over_mint_beyond_escrow_is_rejected() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));

        // Record an independently-verified escrow of 500.
        mirror
            .record_escrow([1u8; 32], 500)
            .expect("escrow recorded");
        assert_eq!(mirror.currently_locked, 500);

        // Draw exactly 500: WITHIN backing → ok (the FALSE branch of the gate).
        mirror.draw_mint(500, cid(1)).expect("draw within escrow");
        assert_eq!(mirror.live_supply, 500);
        assert!(mirror.invariant_holds());

        // Draw 1 more against the same (now fully-drawn) escrow → over-mint, the
        // TRUE branch of the gate fires.
        assert_eq!(
            mirror.draw_mint(1, cid(2)).unwrap_err(),
            MirrorError::InsufficientLocked {
                live: 500,
                locked: 500,
                amount: 1,
            }
        );
        // The rejected draw left supply untouched; conservation holds.
        assert_eq!(mirror.live_supply, 500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn forged_attestation_is_rejected_and_state_unchanged() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        // Sign with the WRONG key.
        let forger = SigningKey::from_bytes(&[42u8; 32]);
        let bad = lock(500, cid(1), 1, &forger);
        assert_eq!(
            mirror.mint_against_lock(&bad).unwrap_err(),
            MirrorError::AttestationInvalid
        );
        assert_eq!(mirror.live_supply, 0);
        assert_eq!(mirror.currently_locked, 0);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn amount_bounds_enforced() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        assert_eq!(
            mirror
                .mint_against_lock(&lock(0, cid(1), 1, &o))
                .unwrap_err(),
            MirrorError::BelowMin
        );
        assert_eq!(
            mirror
                .mint_against_lock(&lock(2_000_000, cid(1), 2, &o))
                .unwrap_err(),
            MirrorError::AboveMax
        );
    }

    #[test]
    fn redeem_burns_and_preserves_conservation() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));
        mirror
            .mint_against_lock(&lock(500, cid(1), 1, &o))
            .expect("mint");

        let solana_recipient = [0x11u8; 32];
        let red = mirror
            .redeem(cid(1), 200, solana_recipient, [0x55u8; 32])
            .expect("redeem ok");

        match red.effect {
            Effect::Burn {
                target,
                slot,
                amount,
            } => {
                assert_eq!(target, cid(1));
                assert_eq!(slot, 0);
                assert_eq!(amount, 200);
            }
            ref other => panic!("expected Effect::Burn, got {other:?}"),
        }
        assert_eq!(red.unlock.amount, 200);
        assert_eq!(red.unlock.spl_mint, SPL_MINT);
        assert_eq!(red.unlock.solana_recipient, solana_recipient);

        assert_eq!(mirror.live_supply, 300);
        assert_eq!(mirror.currently_locked, 300);
        assert!(mirror.invariant_holds());

        // Cannot redeem more than circulating.
        assert!(matches!(
            mirror.redeem(cid(1), 1000, solana_recipient, [0x66u8; 32]),
            Err(MirrorError::InsufficientMirrorSupply { .. })
        ));
    }

    /// END-TO-END: a Solana lock is mirror-minted, then the bridged $DREGG pays
    /// for an execution-lease through the SAME `resolve_pay` rail the metered
    /// ToolGateway charge uses — desugaring to ONE conserving `Effect::Transfer`.
    #[test]
    fn bridged_dregg_pays_an_execution_lease() {
        let o = oracle();
        let mut mirror = MirrorState::new(config(&o));

        let consumer = cid(1); // holds mirror-$DREGG after minting
        let lease_provider = cid(2); // the DreggNet service / lease cell
        let lease_price = 250u64;

        // 1) Mirror-mint 500 bridged $DREGG to the consumer against a lock.
        let minted = mirror
            .mint_against_lock(&lock(500, consumer, 1, &o))
            .expect("mirror-mint");
        assert_eq!(minted.amount, 500);

        // 2) Pay the execution-lease with the mirrored asset over the existing
        //    Payable rail (the asset tag is the mirror's AssetId).
        let (action, sig) = resolve_pay(
            consumer,
            mirror.config.asset, // bridged $DREGG is an ordinary AssetId
            lease_price,
            lease_provider,
            InvokeAuthority::Signature,
        )
        .expect("bridged $DREGG resolves a pay through the Payable interface");

        // The pay desugars to exactly ONE conserving Transfer (Σδ=0).
        assert_eq!(action.effects.len(), 1);
        match action.effects[0] {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, consumer);
                assert_eq!(to, lease_provider);
                assert_eq!(amount, lease_price);
            }
            ref other => panic!("execution-lease charge must be a Transfer, got {other:?}"),
        }
        // It routed through the canonical, replayable Payable method sig.
        assert_eq!(sig.semantics, dregg_cell::interface::Semantics::Replayable);

        // The mirror's own conservation is intact through all of this.
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn unauthorized_lease_payment_is_refused() {
        // Defence: paying for a lease still requires the Signature cap gate —
        // bridging the asset does not bypass authorization.
        let refused = resolve_pay(cid(1), MIRROR_ASSET, 100, cid(2), InvokeAuthority::None)
            .expect_err("an unauthorized lease payment must be refused");
        assert!(matches!(refused, InvokeRefused::Unauthorized { .. }));
    }
}
