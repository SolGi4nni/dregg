//! Typed production weld from the full private fhEgg verifier to an atomic
//! Dark Bazaar game/asset consequence.
//!
//! The generic settlement path quite deliberately accepts any configured
//! [`fhegg_fhe::attestation::ComputationIntegrityVerifier`].  That is useful for
//! compatibility, but it is too weak a type for a game mechanic that promises
//! the fixed private-book relation: its receipt retained the public claim digest
//! while erasing the private statement/root and the exact composite certificate
//! that authorized it.
//!
//! This adapter does not implement another market or game rule.  It first asks
//! the deployment-owned [`crate::fhegg_verifier_registry::FheggVerifierRegistry`]
//! to mint a [`PrivateBfvVerifiedAuthority`] from the exact receipt/context, then
//! calls the existing atomic executor + provenance-carrying asset settlement.
//! The returned consequence binds the verifier, complete evidence envelope,
//! private proof session/rule/root, full MPC session, ordered roster, source
//! board, executor receipt, asset, and trade-world before/after images.

use std::fmt;

use dreggnet_trade::{AssetId, TradeWorld};
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, Digest32, ExpectedClearingContext, ReplayGuard,
};

use crate::fhegg_atomic_asset::{
    AtomicFheggAssetSettlementError, AtomicFheggAssetSettlementReceipt, AtomicSettlementJournal,
};
use crate::fhegg_verifier_registry::{FheggVerifierRegistry, FheggVerifierRegistryError};
use crate::private_bfv_attested_clearing::PrivateBfvVerifiedAuthority;
use crate::{DarkBazaarOffering, DarkBazaarSession};

const CONSEQUENCE_DOMAIN: &str = "dreggnet-market/private-bfv-live-apex-consequence/v1";

/// One real market/game transition with the complete private proof authority
/// kept attached for downstream mechanics and audit.
#[derive(Clone, Debug)]
pub struct PrivateBfvLiveApexReceipt {
    pub authority: PrivateBfvVerifiedAuthority,
    pub settlement: AtomicFheggAssetSettlementReceipt,
    pub consequence_digest: Digest32,
}

impl PrivateBfvLiveApexReceipt {
    pub fn binding_verifies(&self) -> bool {
        self.authority.binding_verifies()
            && self.settlement.audit_digest_verifies()
            && self.authority.claim_digest() == self.settlement.fhegg.claim_digest
            && u64::from(self.authority.price()) == self.settlement.fhegg.price
            && u64::from(self.authority.volume()) == self.settlement.fhegg.volume
            && self.consequence_digest == consequence_digest(&self.authority, &self.settlement)
    }
}

#[derive(Debug)]
pub enum PrivateBfvLiveApexError {
    Registry(FheggVerifierRegistryError),
    Settlement(AtomicFheggAssetSettlementError),
    PostSettlementMismatch(&'static str),
}

impl fmt::Display for PrivateBfvLiveApexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Registry(error) => write!(f, "private apex verifier refused: {error}"),
            Self::Settlement(error) => write!(f, "private apex settlement refused: {error}"),
            Self::PostSettlementMismatch(reason) => {
                write!(f, "private apex authority/settlement mismatch: {reason}")
            }
        }
    }
}

impl std::error::Error for PrivateBfvLiveApexError {}

impl From<FheggVerifierRegistryError> for PrivateBfvLiveApexError {
    fn from(error: FheggVerifierRegistryError) -> Self {
        Self::Registry(error)
    }
}

impl From<AtomicFheggAssetSettlementError> for PrivateBfvLiveApexError {
    fn from(error: AtomicFheggAssetSettlementError) -> Self {
        Self::Settlement(error)
    }
}

impl DarkBazaarOffering {
    /// Verify the full private certificate and make its exact result cause the
    /// existing atomic executor-backed market + asset state transition.
    #[allow(clippy::too_many_arguments)]
    pub fn settle_private_bfv_asset_atomic<R>(
        &self,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        registry: &FheggVerifierRegistry,
        replay_guard: &mut R,
    ) -> Result<PrivateBfvLiveApexReceipt, PrivateBfvLiveApexError>
    where
        R: ReplayGuard + Clone,
    {
        let authority = registry.prepare_private_bfv_authority(receipt, expected)?;
        let settlement = self.settle_fhegg_asset_atomic(
            session,
            world,
            asset,
            receipt,
            expected,
            registry,
            replay_guard,
        )?;
        finish(authority, settlement)
    }

    /// Crash-recoverable form using the existing atomic settlement journal.
    /// Re-running after a committed consequence reconstructs the same typed
    /// private authority; no proof witness, secret key, or share is required.
    #[allow(clippy::too_many_arguments)]
    pub fn settle_private_bfv_asset_atomic_recover<R, J>(
        &self,
        transaction_id: Digest32,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        registry: &FheggVerifierRegistry,
        replay_guard: &mut R,
        journal: &mut J,
    ) -> Result<PrivateBfvLiveApexReceipt, PrivateBfvLiveApexError>
    where
        R: ReplayGuard + Clone,
        J: AtomicSettlementJournal,
    {
        let authority = registry.prepare_private_bfv_authority(receipt, expected)?;
        let settlement = self.settle_fhegg_asset_atomic_recover(
            transaction_id,
            session,
            world,
            asset,
            receipt,
            expected,
            registry,
            replay_guard,
            journal,
        )?;
        finish(authority, settlement)
    }
}

fn finish(
    authority: PrivateBfvVerifiedAuthority,
    settlement: AtomicFheggAssetSettlementReceipt,
) -> Result<PrivateBfvLiveApexReceipt, PrivateBfvLiveApexError> {
    if authority.claim_digest() != settlement.fhegg.claim_digest {
        return Err(PrivateBfvLiveApexError::PostSettlementMismatch(
            "claim digest changed across consequence",
        ));
    }
    if u64::from(authority.price()) != settlement.fhegg.price
        || u64::from(authority.volume()) != settlement.fhegg.volume
    {
        return Err(PrivateBfvLiveApexError::PostSettlementMismatch(
            "private proof output differs from committed settlement",
        ));
    }
    let consequence_digest = consequence_digest(&authority, &settlement);
    Ok(PrivateBfvLiveApexReceipt {
        authority,
        settlement,
        consequence_digest,
    })
}

fn consequence_digest(
    authority: &PrivateBfvVerifiedAuthority,
    settlement: &AtomicFheggAssetSettlementReceipt,
) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key(CONSEQUENCE_DOMAIN);
    hasher.update(&authority.authority_digest());
    hasher.update(&settlement.audit_digest);
    hasher.update(&settlement.fhegg.source_commitment);
    hasher.update(&settlement.fhegg.settlement_turn.receipt_hash());
    hasher.update(&settlement.asset.asset.0);
    hasher.update(&settlement.world_before);
    hasher.update(&settlement.world_after);
    match &settlement.journal_audit {
        Some(audit) => {
            hasher.update(&[1]);
            hasher.update(&audit.digest());
        }
        None => {
            hasher.update(&[0]);
        }
    }
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use dregg_app_framework::TurnReceipt;
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_trade::{AssetId, LegSpec, ProvenanceReport, Settlement};

    use crate::asset_backed::AssetBackedClearing;
    use crate::fhegg_atomic_asset::AtomicFheggAssetSettlementReceipt;
    use crate::fhegg_settlement::FheggSettlementReceipt;
    use crate::private_bfv_attested_clearing::PrivateBfvVerifiedAuthority;

    use super::finish;

    fn fixture() -> super::PrivateBfvLiveApexReceipt {
        let claim_digest = [0x51; 32];
        let authority = PrivateBfvVerifiedAuthority::test_fixture(claim_digest, 3, 1);
        let asset = AssetId([0x61; 32]);
        let seller = DreggIdentity("seller".to_owned());
        let winner = DreggIdentity("winner".to_owned());
        let settlement_turn = TurnReceipt {
            turn_hash: [0x71; 32],
            forest_hash: [0x72; 32],
            pre_state_hash: [0x73; 32],
            post_state_hash: [0x74; 32],
            effects_hash: [0x75; 32],
            action_count: 1,
            ..TurnReceipt::default()
        };
        let mut settlement = AtomicFheggAssetSettlementReceipt {
            fhegg: FheggSettlementReceipt {
                claim_digest,
                source_commitment: [0x76; 32],
                price: 3,
                volume: 1,
                winner: winner.clone(),
                settlement_turn,
            },
            asset: AssetBackedClearing {
                asset,
                seller,
                winner,
                price: 3,
                settlement: Settlement {
                    a_gave: LegSpec::Asset(asset),
                    b_gave: LegSpec::Dregg(3),
                },
                provenance: ProvenanceReport {
                    verified: true,
                    length: 2,
                    current_owner: [0x77; 32],
                    revoked: false,
                    reasons: Vec::new(),
                },
            },
            world_before: [0x78; 32],
            world_after: [0x79; 32],
            audit_digest: [0; 32],
            journal_audit: None,
        };
        settlement.audit_digest = settlement.recompute_audit_digest();
        finish(authority, settlement).expect("exact typed consequence")
    }

    #[test]
    fn typed_private_apex_refuses_authority_and_turn_substitution() {
        let honest = fixture();
        assert!(honest.binding_verifies());

        let mut wrong_verifier = honest.clone();
        wrong_verifier.authority.tamper_verifier();
        assert!(!wrong_verifier.binding_verifies());

        let mut wrong_certificate = honest.clone();
        wrong_certificate.authority.tamper_certificate();
        assert!(!wrong_certificate.binding_verifies());

        let mut wrong_root = honest.clone();
        wrong_root.authority.tamper_root();
        assert!(!wrong_root.binding_verifies());

        let mut wrong_roster = honest.clone();
        wrong_roster.authority.tamper_roster();
        assert!(!wrong_roster.binding_verifies());

        let mut wrong_turn = honest.clone();
        wrong_turn.settlement.fhegg.settlement_turn.turn_hash[0] ^= 1;
        assert!(!wrong_turn.binding_verifies());

        // Mutating both public winner copies used to survive the apex's own
        // checks if a caller also recomputed its public consequence digest.
        // The atomic settlement audit is the independently committed binding.
        let mut wrong_winner = honest.clone();
        let substituted_winner = DreggIdentity("substituted-winner".to_owned());
        wrong_winner.settlement.fhegg.winner = substituted_winner.clone();
        wrong_winner.settlement.asset.winner = substituted_winner;
        wrong_winner.consequence_digest =
            super::consequence_digest(&wrong_winner.authority, &wrong_winner.settlement);
        assert!(!wrong_winner.binding_verifies());

        let mut wrong_claim = honest;
        wrong_claim.settlement.fhegg.claim_digest[0] ^= 1;
        assert!(!wrong_claim.binding_verifies());
    }
}
