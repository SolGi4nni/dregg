//! A verified private fhEgg result authorizes one exact signed dungeon consequence.
//!
//! The private Bazaar verifier and the game router deliberately remain separate
//! systems.  This module is the typed weld between them.  It projects only the
//! public authority carried by a [`PrivateBfvLiveApexReceipt`], binds that
//! authority to one incarnation/generation-qualified [`GameActionRef`], and then
//! dispatches exactly that action through the signed common-game-spine path.
//! The target epoch is obtained from [`GameEpochLedger`] rather than accepted
//! as a second caller assertion, and is re-read immediately before dispatch.
//!
//! The first deployed mechanic is the Warden's Keep raid-Mender recovery.  The
//! second is a shielded crown claim: a finalized FNSP-v2 tender redemption whose
//! public value equals the verified Bazaar price authorizes its deployment-pinned
//! Bazaar winner to land one exact Red/Blue `WriteOnce` crown turn.  The spend authority is
//! not a raw proof or a caller boolean.  It is a private-field
//! [`dregg_persist::FinalizedFaithfulSpend`] minted only by the atomic durable
//! finalization transaction after HidingFRI verification, historical-root
//! authentication, exact ordered nullifier insertion, receipt commit, and
//! attested-root persistence have all succeeded.
//!
//! Neither the private order witness, BFV openings, faithful note opening/path,
//! raid score matrix, nor a viewer projection crosses this API.  The adapter
//! accepts no asserted actor label and no caller-supplied game receipt: it
//! invokes the signed spine itself. Its output contains public commitments and
//! receipt ids only. FNSP-v2 intentionally makes value, asset type, nullifier,
//! and roots public; those public fields remain visible here.
//! The private BFV authority requires its `NativePostQuantum` authenticated
//! quorum-crossing profile; that does not make the current Ristretto/Bulletproof
//! same-opening argument PQ. The persist-minted spend binds a real attested-root
//! author signature and federation id, but its committee-finality security is
//! deliberately unclassified here: the hybrid quorum may be backfilled after
//! the atomic spend record and must be evaluated by a later roster-aware view.
//!
//! Atomicity is the target engine's one committed turn.  The preceding faithful
//! spend, Bazaar asset settlement, and this game turn are not one distributed
//! transaction.  FNSP-v2 establishes a durable one-shot note redemption, not a
//! recipient output; the apex's atomic asset/value cross remains the Bazaar
//! payment. A deployment must persist
//! [`PrivateFheggGameConsequenceGate::authorization_id`]
//! after success (and restore it on restart); the Keep's Mender field and the
//! host's signed-counter journal independently make the concrete mechanic
//! one-shot across the post-turn persistence window.

use dregg_persist::FinalizedFaithfulSpend;
use dreggnet_market::private_bfv_attested_clearing::PrivateBfvQuorumSecurity;
use dreggnet_market::private_bfv_live_apex::PrivateBfvLiveApexReceipt;
use dreggnet_offerings::{Action, Attribution, DreggIdentity, OfferingHost, SignedAction};

use crate::game_spine::{
    GameActionRef, GameHostIncarnation, GameKind, GameReceipt, GameResult, GameSessionBinding,
    GameSessionRef, GameSpineError, execute_bound_signed_game_turn,
};
use crate::{GameEpochError, GameEpochLedger};

const AUTHORIZATION_DOMAIN: &str = "dregg.private-fhegg-game-authorization.v1";
const CONSEQUENCE_DOMAIN: &str = "dregg.private-fhegg-game-consequence.v1";
const WINNER_ROUTE_DOMAIN: &str = "dregg.private-fhegg-winner-route.v1";
const FAITHFUL_AUTHORITY_DOMAIN: &str = "dregg.finalized-faithful-spend-game-authority.v1";

/// The deliberately small initial vocabulary of private-fhEgg game effects.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrivateFheggGameMechanic {
    /// Spend the Mender seat selected by the independently verified private
    /// raid assignment, raising the Keep party from 30 HP to 50 HP once.
    DungeonRaidMender,
    /// A finalized FNSP-v2 tender redemption matching the private Bazaar's exact
    /// one-lot price lets the mapped winner claim either Red or Blue's
    /// executor-enforced `WriteOnce` crown.
    DungeonShieldedCrown,
}

impl PrivateFheggGameMechanic {
    const fn tag(self) -> &'static [u8] {
        match self {
            Self::DungeonRaidMender => b"dungeon/raid-mender/v1",
            Self::DungeonShieldedCrown => b"dungeon/shielded-crown/v1",
        }
    }

    const fn requires_faithful_spend(self) -> bool {
        matches!(self, Self::DungeonShieldedCrown)
    }

    fn validate_target(
        self,
        reference: &GameActionRef,
        action: &Action,
    ) -> Result<(), PrivateFheggGameConsequenceError> {
        match self {
            Self::DungeonRaidMender => {
                if reference.session.kind() != GameKind::Dungeon
                    || action.turn != dreggnet_offerings::dungeon::TURN_CHOOSE
                    || !dungeon_on_dregg::KP_PRIVATE_RAID_MENDER_CHOICES
                        .iter()
                        .any(|choice| i64::try_from(*choice).ok() == Some(action.arg))
                {
                    return Err(PrivateFheggGameConsequenceError::WrongMechanicTarget);
                }
            }
            Self::DungeonShieldedCrown => {
                if reference.session.kind() != GameKind::Dungeon
                    || action.turn != dreggnet_offerings::dungeon::TURN_CHOOSE
                    || ![
                        dungeon_on_dregg::KP_CLAIM_RED,
                        dungeon_on_dregg::KP_CLAIM_BLUE,
                    ]
                    .iter()
                    .any(|choice| i64::try_from(*choice).ok() == Some(action.arg))
                {
                    return Err(PrivateFheggGameConsequenceError::WrongMechanicTarget);
                }
            }
        }
        Ok(())
    }
}

/// Independently configured mapping from a public Bazaar identity to the key
/// that must sign the game turn.  The mapping is policy, so its digest is part
/// of the authorization rather than inferred from a display label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateFheggWinnerRoute {
    market_winner: DreggIdentity,
    game_signer_pubkey_hex: String,
    digest: [u8; 32],
}

impl PrivateFheggWinnerRoute {
    pub fn new(
        market_winner: DreggIdentity,
        game_signer_pubkey_hex: impl Into<String>,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        if market_winner.0.is_empty() {
            return Err(PrivateFheggGameConsequenceError::InvalidWinnerRoute(
                "market winner is empty",
            ));
        }
        let game_signer_pubkey_hex = game_signer_pubkey_hex.into().to_ascii_lowercase();
        if !is_canonical_pubkey_hex(&game_signer_pubkey_hex) {
            return Err(PrivateFheggGameConsequenceError::InvalidWinnerRoute(
                "game signer is not a canonical 32-byte public key",
            ));
        }
        let digest = winner_route_digest(&market_winner, &game_signer_pubkey_hex);
        Ok(Self {
            market_winner,
            game_signer_pubkey_hex,
            digest,
        })
    }

    pub fn market_winner(&self) -> &DreggIdentity {
        &self.market_winner
    }

    pub fn game_signer_pubkey_hex(&self) -> &str {
        &self.game_signer_pubkey_hex
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

/// Public-only projection of the exact finalized faithful spend consumed by a
/// game authorization. It carries no note opening, Merkle path, or proof bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulSpendGameAuthorityReceipt {
    /// Catalog-domain commitment to this whole public projection.
    pub authority_digest: [u8; 32],
    /// Persist's independent digest, minted inside the atomic finalization
    /// transaction and embedded here so a different durable spend cannot be
    /// substituted under a recomputed catalog projection.
    pub persisted_authority_digest: [u8; 32],
    pub federation_id: [u8; 32],
    pub attested_root_digest: [u8; 32],
    pub finalized_height: u64,
    pub block_id: [u8; 32],
    pub finality_round: Option<u64>,
    pub turn_hash: [u8; 32],
    pub turn_receipt_hash: [u8; 32],
    pub spend_agent: [u8; 32],
    pub spend_index: u32,
    pub root_height: u64,
    pub historical_note_root: [u8; 32],
    pub nullifier: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub successor_nullifier_root: [u8; 32],
}

impl FaithfulSpendGameAuthorityReceipt {
    pub fn binding_verifies(&self) -> bool {
        self.authority_digest == faithful_spend_authority_digest(self)
            && self.persisted_authority_digest != [0; 32]
            && self.federation_id != [0; 32]
            && self.attested_root_digest != [0; 32]
            && self.block_id != [0; 32]
            && self.turn_hash != [0; 32]
            && self.turn_receipt_hash != [0; 32]
            && self.spend_agent != [0; 32]
            && self.nullifier != [0; 32]
            && self.root_height <= self.finalized_height
    }

    /// Rejoin this portable public projection to the private-field durable
    /// authority loaded by a verifier from its trusted persistence boundary.
    pub fn matches_finalized_spend(&self, spend: &FinalizedFaithfulSpend) -> bool {
        self.binding_verifies()
            && self.persisted_authority_digest == spend.authority_digest()
            && self.federation_id == spend.federation_id()
            && self.attested_root_digest == spend.attested_root_digest()
            && self.finalized_height == spend.finalized_height()
            && self.block_id == spend.block_id()
            && self.finality_round == spend.finality_round()
            && self.turn_hash == spend.turn_hash()
            && self.turn_receipt_hash == spend.turn_receipt_hash()
            && self.spend_agent == spend.spend_agent()
            && self.spend_index == spend.spend_index()
            && self.root_height == spend.root_height()
            && self.historical_note_root == spend.historical_note_root8()
            && self.nullifier == spend.nullifier()
            && self.value == spend.value()
            && self.asset_type == spend.asset_type()
            && self.successor_nullifier_root == spend.successor_nullifier_root8()
    }
}

/// Catalog-private wrapper around persistence's unforgeable-in-production
/// authority.  Production construction consumes only the private-field type
/// loaded from the finalized-spend table; it cannot be reconstructed from raw
/// proof bytes or caller-selected public fields.
#[derive(Clone, Debug, PartialEq, Eq)]
struct FinalizedFaithfulSpendAuthority {
    public: FaithfulSpendGameAuthorityReceipt,
}

impl FinalizedFaithfulSpendAuthority {
    fn from_persisted(
        spend: &FinalizedFaithfulSpend,
        expected_federation_id: [u8; 32],
        expected_spend_agent: [u8; 32],
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        if expected_federation_id == [0; 32] || spend.federation_id() != expected_federation_id {
            return Err(PrivateFheggGameConsequenceError::SpendFederationMismatch);
        }
        if expected_spend_agent == [0; 32] || spend.spend_agent() != expected_spend_agent {
            return Err(PrivateFheggGameConsequenceError::SpendAgentMismatch);
        }
        let mut public = FaithfulSpendGameAuthorityReceipt {
            authority_digest: [0; 32],
            persisted_authority_digest: spend.authority_digest(),
            federation_id: spend.federation_id(),
            attested_root_digest: spend.attested_root_digest(),
            finalized_height: spend.finalized_height(),
            block_id: spend.block_id(),
            finality_round: spend.finality_round(),
            turn_hash: spend.turn_hash(),
            turn_receipt_hash: spend.turn_receipt_hash(),
            spend_agent: expected_spend_agent,
            spend_index: spend.spend_index(),
            root_height: spend.root_height(),
            historical_note_root: spend.historical_note_root8(),
            nullifier: spend.nullifier(),
            value: spend.value(),
            asset_type: spend.asset_type(),
            successor_nullifier_root: spend.successor_nullifier_root8(),
        };
        if public.persisted_authority_digest == [0; 32]
            || public.turn_hash == [0; 32]
            || public.turn_receipt_hash == [0; 32]
            || public.nullifier == [0; 32]
        {
            return Err(PrivateFheggGameConsequenceError::InvalidFaithfulSpendAuthority);
        }
        public.authority_digest = faithful_spend_authority_digest(&public);
        debug_assert!(public.binding_verifies());
        Ok(Self { public })
    }

    #[cfg(test)]
    fn fixture(value: u64, asset_type: u64, spend_agent: [u8; 32]) -> Self {
        let mut public = FaithfulSpendGameAuthorityReceipt {
            authority_digest: [0; 32],
            persisted_authority_digest: [0x70; 32],
            federation_id: [0x71; 32],
            attested_root_digest: [0x72; 32],
            finalized_height: 9,
            block_id: [0x73; 32],
            finality_round: Some(4),
            turn_hash: [0x74; 32],
            turn_receipt_hash: [0x75; 32],
            spend_agent,
            spend_index: 0,
            root_height: 7,
            historical_note_root: [0x76; 32],
            nullifier: [0x77; 32],
            value,
            asset_type,
            successor_nullifier_root: [0x78; 32],
        };
        public.authority_digest = faithful_spend_authority_digest(&public);
        Self { public }
    }
}

/// Secret-free public authority projected from the full verified apex value.
/// Fields are private so production callers cannot fabricate one without first
/// presenting the verifier-minted [`PrivateBfvLiveApexReceipt`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct PrivateFheggGameAuthority {
    verifier_id: [u8; 32],
    claim_digest: [u8; 32],
    certificate_digest: [u8; 32],
    authority_digest: [u8; 32],
    apex_consequence_digest: [u8; 32],
    private_session: u32,
    relation: u32,
    private_root: [u32; 8],
    roster_commitment: [u8; 32],
    settlement_turn_hash: [u8; 32],
    market_asset_id: [u8; 32],
    market_winner: DreggIdentity,
    price: u32,
    volume: u32,
}

impl PrivateFheggGameAuthority {
    fn from_live_apex(
        apex: &PrivateBfvLiveApexReceipt,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        if !apex.binding_verifies() || !apex.settlement.audit_digest_verifies() {
            return Err(PrivateFheggGameConsequenceError::InvalidPrivateAuthority(
                "typed apex or atomic settlement binding does not verify",
            ));
        }
        if apex.authority.quorum_security() != PrivateBfvQuorumSecurity::NativePostQuantum {
            return Err(PrivateFheggGameConsequenceError::InvalidPrivateAuthority(
                "game consequence requires the native-PQ authenticated quorum profile",
            ));
        }
        if apex.authority.volume() != 1
            || apex.settlement.fhegg.volume != 1
            || apex.authority.price() == 0
        {
            return Err(PrivateFheggGameConsequenceError::InvalidPrivateAuthority(
                "private result is not the fixed positive one-lot game clearing",
            ));
        }
        if apex.settlement.asset.asset.0 == [0; 32]
            || apex.settlement.fhegg.winner.0.is_empty()
            || apex.settlement.asset.winner != apex.settlement.fhegg.winner
        {
            return Err(PrivateFheggGameConsequenceError::InvalidPrivateAuthority(
                "market and atomic asset consequence disagree on the winner",
            ));
        }
        if [
            apex.authority.verifier_id(),
            apex.authority.claim_digest(),
            apex.authority.certificate_digest(),
            apex.authority.authority_digest(),
            apex.consequence_digest,
            apex.authority.roster_commitment(),
            apex.settlement.fhegg.settlement_turn.turn_hash,
        ]
        .iter()
        .any(|digest| *digest == [0; 32])
        {
            return Err(PrivateFheggGameConsequenceError::InvalidPrivateAuthority(
                "private authority contains a zero sentinel",
            ));
        }
        Ok(Self {
            verifier_id: apex.authority.verifier_id(),
            claim_digest: apex.authority.claim_digest(),
            certificate_digest: apex.authority.certificate_digest(),
            authority_digest: apex.authority.authority_digest(),
            apex_consequence_digest: apex.consequence_digest,
            private_session: apex.authority.private_session(),
            relation: apex.authority.relation(),
            private_root: apex.authority.private_root(),
            roster_commitment: apex.authority.roster_commitment(),
            settlement_turn_hash: apex.settlement.fhegg.settlement_turn.turn_hash,
            market_asset_id: apex.settlement.asset.asset.0,
            market_winner: apex.settlement.fhegg.winner.clone(),
            price: apex.authority.price(),
            volume: apex.authority.volume(),
        })
    }

    #[cfg(test)]
    fn fixture(market_winner: DreggIdentity) -> Self {
        Self {
            verifier_id: [0x11; 32],
            claim_digest: [0x12; 32],
            certificate_digest: [0x13; 32],
            authority_digest: [0x14; 32],
            apex_consequence_digest: [0x15; 32],
            private_session: 17,
            relation: 0xDB_04,
            private_root: [1, 2, 3, 4, 5, 6, 7, 8],
            roster_commitment: [0x16; 32],
            settlement_turn_hash: [0x17; 32],
            market_asset_id: [0x18; 32],
            market_winner,
            price: 3,
            volume: 1,
        }
    }
}

/// One-shot policy object joining full private authority to one exact game
/// action.  It owns no proof bytes and exposes no callback that could return a
/// caller-fabricated receipt.
#[derive(Debug)]
pub struct PrivateFheggGameConsequenceGate {
    authority: PrivateFheggGameAuthority,
    faithful_spend: Option<FinalizedFaithfulSpendAuthority>,
    winner_route: PrivateFheggWinnerRoute,
    mechanic: PrivateFheggGameMechanic,
    target_reference: GameActionRef,
    target_action: Action,
    epoch_ledger: GameEpochLedger,
    host_incarnation: GameHostIncarnation,
    session_generation: u64,
    authorization_id: [u8; 32],
    consumed: bool,
}

impl PrivateFheggGameConsequenceGate {
    /// Pin the verifier-minted private authority to one live, bound game
    /// affordance.  A stale head later refuses in the common spine before the
    /// game executor runs.
    pub fn new(
        apex: &PrivateBfvLiveApexReceipt,
        required_asset_id: [u8; 32],
        winner_route: PrivateFheggWinnerRoute,
        mechanic: PrivateFheggGameMechanic,
        epoch_ledger: &GameEpochLedger,
        target_reference: GameActionRef,
        target_action: Action,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        let authority = PrivateFheggGameAuthority::from_live_apex(apex)?;
        Self::from_authority(
            authority,
            required_asset_id,
            winner_route,
            mechanic,
            epoch_ledger,
            target_reference,
            target_action,
        )
    }

    /// Join a verifier-minted private Bazaar result to a genuinely finalized
    /// FNSP-v2 tender redemption and one exact Dungeon crown claim. The expected
    /// federation and spend agent are deployment policy: `spend_agent` is the
    /// public finalized-turn submitter and does not reveal or assert the hidden
    /// note owner.
    #[allow(clippy::too_many_arguments)]
    pub fn new_shielded_crown(
        apex: &PrivateBfvLiveApexReceipt,
        required_market_asset_id: [u8; 32],
        required_tender_asset_type: u64,
        expected_spend_federation_id: [u8; 32],
        expected_spend_agent: [u8; 32],
        finalized_spend: &FinalizedFaithfulSpend,
        winner_route: PrivateFheggWinnerRoute,
        epoch_ledger: &GameEpochLedger,
        target_reference: GameActionRef,
        target_action: Action,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        let authority = PrivateFheggGameAuthority::from_live_apex(apex)?;
        let faithful_spend = FinalizedFaithfulSpendAuthority::from_persisted(
            finalized_spend,
            expected_spend_federation_id,
            expected_spend_agent,
        )?;
        Self::from_authorities(
            authority,
            Some(faithful_spend),
            required_market_asset_id,
            Some(required_tender_asset_type),
            winner_route,
            PrivateFheggGameMechanic::DungeonShieldedCrown,
            epoch_ledger,
            target_reference,
            target_action,
        )
    }

    fn from_authority(
        authority: PrivateFheggGameAuthority,
        required_asset_id: [u8; 32],
        winner_route: PrivateFheggWinnerRoute,
        mechanic: PrivateFheggGameMechanic,
        epoch_ledger: &GameEpochLedger,
        target_reference: GameActionRef,
        target_action: Action,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        Self::from_authorities(
            authority,
            None,
            required_asset_id,
            None,
            winner_route,
            mechanic,
            epoch_ledger,
            target_reference,
            target_action,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn from_authorities(
        authority: PrivateFheggGameAuthority,
        faithful_spend: Option<FinalizedFaithfulSpendAuthority>,
        required_asset_id: [u8; 32],
        required_tender_asset_type: Option<u64>,
        winner_route: PrivateFheggWinnerRoute,
        mechanic: PrivateFheggGameMechanic,
        epoch_ledger: &GameEpochLedger,
        target_reference: GameActionRef,
        target_action: Action,
    ) -> Result<Self, PrivateFheggGameConsequenceError> {
        if required_asset_id == [0; 32] || authority.market_asset_id != required_asset_id {
            return Err(PrivateFheggGameConsequenceError::MarketAssetMismatch);
        }
        if authority.market_winner != winner_route.market_winner {
            return Err(PrivateFheggGameConsequenceError::WinnerRouteMismatch);
        }
        match (mechanic.requires_faithful_spend(), faithful_spend.as_ref()) {
            (true, None) => {
                return Err(PrivateFheggGameConsequenceError::MissingFaithfulSpendAuthority);
            }
            (false, Some(_)) => {
                return Err(PrivateFheggGameConsequenceError::UnexpectedFaithfulSpendAuthority);
            }
            (true, Some(spend)) => {
                if spend.public.value != u64::from(authority.price)
                    || Some(spend.public.asset_type) != required_tender_asset_type
                {
                    return Err(PrivateFheggGameConsequenceError::FaithfulTenderMismatch);
                }
            }
            (false, None) => {}
        }
        if target_reference.expected_pre_head.is_empty()
            || target_reference.turn != target_action.turn
            || target_reference.arg != target_action.arg
            || target_reference.text != target_action.text
        {
            return Err(PrivateFheggGameConsequenceError::ActionReferenceMismatch);
        }
        mechanic.validate_target(&target_reference, &target_action)?;
        let (host_incarnation, session_generation) = match target_reference.session.binding() {
            GameSessionBinding::Bound {
                host_incarnation,
                session_generation,
            } => (*host_incarnation, *session_generation),
            GameSessionBinding::LegacyUnbound => {
                return Err(PrivateFheggGameConsequenceError::UnboundGameSession);
            }
        };
        let live_session = epoch_ledger.bound_session(
            target_reference.session.offering(),
            target_reference.session.session_id(),
        )?;
        if live_session != target_reference.session {
            return Err(PrivateFheggGameConsequenceError::AuthorityEpochMismatch);
        }
        let authorization_id = authorization_id(
            &authority,
            faithful_spend.as_ref(),
            &winner_route,
            mechanic,
            &target_reference,
        );
        Ok(Self {
            authority,
            faithful_spend,
            winner_route,
            mechanic,
            target_reference,
            target_action,
            epoch_ledger: epoch_ledger.clone(),
            host_incarnation,
            session_generation,
            authorization_id,
            consumed: false,
        })
    }

    pub const fn authorization_id(&self) -> [u8; 32] {
        self.authorization_id
    }

    pub fn target_session(&self) -> &GameSessionRef {
        &self.target_reference.session
    }

    pub fn target_action(&self) -> &Action {
        &self.target_action
    }

    pub const fn is_consumed(&self) -> bool {
        self.consumed
    }

    /// Restore the exact durable one-shot id.  A different id cannot be used to
    /// suppress this authorization accidentally or maliciously.
    pub fn restore_consumed(
        &mut self,
        authorization_id: [u8; 32],
    ) -> Result<(), PrivateFheggGameConsequenceError> {
        if authorization_id != self.authorization_id {
            return Err(PrivateFheggGameConsequenceError::RestoreIdMismatch);
        }
        self.consumed = true;
        Ok(())
    }

    /// Execute the exact pinned action through the signed, authority-epoch-aware
    /// common game spine.  Refusal does not consume the private authorization.
    pub fn execute_signed(
        &mut self,
        host: &mut OfferingHost,
        signed_action: SignedAction,
    ) -> Result<PrivateFheggGameConsequenceReceipt, PrivateFheggGameConsequenceError> {
        if self.consumed {
            return Err(PrivateFheggGameConsequenceError::AlreadyConsumed);
        }
        if signed_action.actor_pubkey_hex.to_ascii_lowercase()
            != self.winner_route.game_signer_pubkey_hex
        {
            return Err(PrivateFheggGameConsequenceError::WrongGameSigner);
        }
        if signed_action.action.turn != self.target_action.turn
            || signed_action.action.arg != self.target_action.arg
            || signed_action.action.text != self.target_action.text
        {
            return Err(PrivateFheggGameConsequenceError::ActionReferenceMismatch);
        }

        // Epoch custody can change after a UI captures an affordance (close /
        // reopen, host replacement). Re-read it at the last possible point so
        // a byte-identical fresh state cannot revive the old authorization.
        let live_session = self.epoch_ledger.bound_session(
            self.target_reference.session.offering(),
            self.target_reference.session.session_id(),
        )?;
        if live_session != self.target_reference.session {
            return Err(PrivateFheggGameConsequenceError::AuthorityEpochMismatch);
        }

        let result = execute_bound_signed_game_turn(
            host,
            self.host_incarnation,
            self.session_generation,
            &self.target_reference.session,
            self.target_reference.clone(),
            signed_action,
        )?;
        let receipt = match result {
            GameResult::Refused { reason, .. } => {
                return Err(PrivateFheggGameConsequenceError::GameRefused(reason));
            }
            GameResult::Landed(receipt) => receipt,
        };
        let (action, attribution, inner_receipt_id, ended) = match &receipt {
            GameReceipt::Turn {
                action,
                attribution,
                inner_receipt_id,
                ended,
                ..
            } => (action, attribution, *inner_receipt_id, *ended),
            GameReceipt::Operation { .. } => {
                return Err(PrivateFheggGameConsequenceError::InvalidGameReceipt(
                    "signed consequence returned an operation receipt",
                ));
            }
        };
        if action != &self.target_reference || !receipt.routing_binding_valid() {
            return Err(PrivateFheggGameConsequenceError::InvalidGameReceipt(
                "game receipt does not bind the exact target action",
            ));
        }
        if attribution
            != &(Attribution::Signed {
                pubkey_hex: self.winner_route.game_signer_pubkey_hex.clone(),
            })
        {
            return Err(PrivateFheggGameConsequenceError::InvalidGameReceipt(
                "game receipt lost the deployment-pinned signed attribution",
            ));
        }
        let game_receipt_id = receipt.receipt_id();
        let action_preimage_id = self.target_reference.routing_preimage_id();
        let consequence_digest = consequence_digest(
            self.authorization_id,
            self.mechanic,
            self.faithful_spend.as_ref().map(|spend| &spend.public),
            self.authority.authority_digest,
            self.authority.certificate_digest,
            self.authority.private_session,
            self.authority.private_root,
            self.authority.market_asset_id,
            &self.authority.market_winner,
            self.winner_route.digest,
            &self.winner_route.game_signer_pubkey_hex,
            &self.target_reference.session,
            action_preimage_id,
            game_receipt_id,
            inner_receipt_id,
            ended,
        );
        self.consumed = true;
        Ok(PrivateFheggGameConsequenceReceipt {
            authorization_id: self.authorization_id,
            consequence_digest,
            mechanic: self.mechanic,
            faithful_spend: self
                .faithful_spend
                .as_ref()
                .map(|spend| spend.public.clone()),
            authority_digest: self.authority.authority_digest,
            certificate_digest: self.authority.certificate_digest,
            private_session: self.authority.private_session,
            private_root: self.authority.private_root,
            market_asset_id: self.authority.market_asset_id,
            market_winner: self.authority.market_winner.clone(),
            winner_route_digest: self.winner_route.digest,
            game_signer_pubkey_hex: self.winner_route.game_signer_pubkey_hex.clone(),
            target_session: self.target_reference.session.clone(),
            action_preimage_id,
            game_receipt_id,
            inner_game_receipt_id: inner_receipt_id,
            ended,
        })
    }
}

/// Public-only receipt joining the exact verified private source to the exact
/// common-spine game turn.  It carries commitments, never proof witnesses.
/// [`Self::binding_verifies`] checks internal substitution resistance;
/// [`Self::matches_authorities`] additionally rejoins the two typed sources.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateFheggGameConsequenceReceipt {
    pub authorization_id: [u8; 32],
    pub consequence_digest: [u8; 32],
    pub mechanic: PrivateFheggGameMechanic,
    pub faithful_spend: Option<FaithfulSpendGameAuthorityReceipt>,
    pub authority_digest: [u8; 32],
    pub certificate_digest: [u8; 32],
    pub private_session: u32,
    pub private_root: [u32; 8],
    pub market_asset_id: [u8; 32],
    pub market_winner: DreggIdentity,
    pub winner_route_digest: [u8; 32],
    pub game_signer_pubkey_hex: String,
    pub target_session: GameSessionRef,
    pub action_preimage_id: [u8; 32],
    pub game_receipt_id: [u8; 32],
    pub inner_game_receipt_id: [u8; 32],
    pub ended: bool,
}

impl PrivateFheggGameConsequenceReceipt {
    pub fn binding_verifies(&self) -> bool {
        self.consequence_digest
            == consequence_digest(
                self.authorization_id,
                self.mechanic,
                self.faithful_spend.as_ref(),
                self.authority_digest,
                self.certificate_digest,
                self.private_session,
                self.private_root,
                self.market_asset_id,
                &self.market_winner,
                self.winner_route_digest,
                &self.game_signer_pubkey_hex,
                &self.target_session,
                self.action_preimage_id,
                self.game_receipt_id,
                self.inner_game_receipt_id,
                self.ended,
            )
            && self.authority_digest != [0; 32]
            && self.certificate_digest != [0; 32]
            && self.game_receipt_id != [0; 32]
            && self.inner_game_receipt_id != [0; 32]
            && self.action_preimage_id != [0; 32]
            && self.market_asset_id != [0; 32]
            && self.target_session.binding().is_bound()
            && is_canonical_pubkey_hex(&self.game_signer_pubkey_hex)
            && self.winner_route_digest
                == winner_route_digest(&self.market_winner, &self.game_signer_pubkey_hex)
            && match (
                self.mechanic.requires_faithful_spend(),
                &self.faithful_spend,
            ) {
                (true, Some(spend)) => spend.binding_verifies(),
                (false, None) => true,
                _ => false,
            }
    }

    /// Rejoin the portable consequence to the typed private-market authority
    /// and, for shielded mechanics, the exact store-minted spend authority.
    /// `binding_verifies` alone establishes internal commitment consistency;
    /// this method establishes the external authority anchors.
    pub fn matches_authorities(
        &self,
        apex: &PrivateBfvLiveApexReceipt,
        finalized_spend: Option<&FinalizedFaithfulSpend>,
    ) -> bool {
        let Ok(authority) = PrivateFheggGameAuthority::from_live_apex(apex) else {
            return false;
        };
        self.binding_verifies()
            && self.authority_digest == authority.authority_digest
            && self.certificate_digest == authority.certificate_digest
            && self.private_session == authority.private_session
            && self.private_root == authority.private_root
            && self.market_asset_id == authority.market_asset_id
            && self.market_winner == authority.market_winner
            && match (&self.faithful_spend, finalized_spend) {
                (Some(receipt), Some(spend)) => receipt.matches_finalized_spend(spend),
                (None, None) => true,
                _ => false,
            }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateFheggGameConsequenceError {
    InvalidPrivateAuthority(&'static str),
    InvalidWinnerRoute(&'static str),
    InvalidFaithfulSpendAuthority,
    SpendFederationMismatch,
    SpendAgentMismatch,
    FaithfulTenderMismatch,
    MissingFaithfulSpendAuthority,
    UnexpectedFaithfulSpendAuthority,
    MarketAssetMismatch,
    WinnerRouteMismatch,
    WrongMechanicTarget,
    UnboundGameSession,
    AuthorityEpochMismatch,
    ActionReferenceMismatch,
    WrongGameSigner,
    AlreadyConsumed,
    RestoreIdMismatch,
    GameRefused(String),
    InvalidGameReceipt(&'static str),
    EpochCustody(String),
    GameSpine(String),
}

impl From<GameEpochError> for PrivateFheggGameConsequenceError {
    fn from(error: GameEpochError) -> Self {
        Self::EpochCustody(error.to_string())
    }
}

impl From<GameSpineError> for PrivateFheggGameConsequenceError {
    fn from(error: GameSpineError) -> Self {
        Self::GameSpine(error.to_string())
    }
}

impl std::fmt::Display for PrivateFheggGameConsequenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private fhEgg game consequence refused: {self:?}")
    }
}

impl std::error::Error for PrivateFheggGameConsequenceError {}

fn faithful_spend_authority_digest(spend: &FaithfulSpendGameAuthorityReceipt) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(FAITHFUL_AUTHORITY_DOMAIN);
    for digest in [
        spend.persisted_authority_digest,
        spend.federation_id,
        spend.attested_root_digest,
        spend.block_id,
        spend.turn_hash,
        spend.turn_receipt_hash,
        spend.spend_agent,
        spend.historical_note_root,
        spend.nullifier,
        spend.successor_nullifier_root,
    ] {
        hash_field(&mut hasher, &digest);
    }
    hash_field(&mut hasher, &spend.spend_index.to_be_bytes());
    for number in [
        spend.finalized_height,
        spend.root_height,
        spend.value,
        spend.asset_type,
    ] {
        hash_field(&mut hasher, &number.to_be_bytes());
    }
    match spend.finality_round {
        Some(round) => {
            hash_field(&mut hasher, &[1]);
            hash_field(&mut hasher, &round.to_be_bytes());
        }
        None => hash_field(&mut hasher, &[0]),
    }
    *hasher.finalize().as_bytes()
}

fn is_canonical_pubkey_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn winner_route_digest(winner: &DreggIdentity, signer: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(WINNER_ROUTE_DOMAIN);
    hash_field(&mut hasher, winner.0.as_bytes());
    hash_field(&mut hasher, signer.as_bytes());
    *hasher.finalize().as_bytes()
}

fn authorization_id(
    authority: &PrivateFheggGameAuthority,
    faithful_spend: Option<&FinalizedFaithfulSpendAuthority>,
    winner_route: &PrivateFheggWinnerRoute,
    mechanic: PrivateFheggGameMechanic,
    target: &GameActionRef,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(AUTHORIZATION_DOMAIN);
    for digest in [
        authority.verifier_id,
        authority.claim_digest,
        authority.certificate_digest,
        authority.authority_digest,
        authority.apex_consequence_digest,
        authority.roster_commitment,
        authority.settlement_turn_hash,
        authority.market_asset_id,
        winner_route.digest,
        target.routing_preimage_id(),
    ] {
        hash_field(&mut hasher, &digest);
    }
    hash_field(&mut hasher, &authority.private_session.to_be_bytes());
    hash_field(&mut hasher, &authority.relation.to_be_bytes());
    for lane in authority.private_root {
        hash_field(&mut hasher, &lane.to_be_bytes());
    }
    hash_field(&mut hasher, &authority.price.to_be_bytes());
    hash_field(&mut hasher, &authority.volume.to_be_bytes());
    match faithful_spend {
        Some(spend) => {
            hash_field(&mut hasher, &[1]);
            hash_field(&mut hasher, &spend.public.authority_digest);
        }
        None => hash_field(&mut hasher, &[0]),
    }
    hash_field(&mut hasher, mechanic.tag());
    *hasher.finalize().as_bytes()
}

fn consequence_digest(
    authorization_id: [u8; 32],
    mechanic: PrivateFheggGameMechanic,
    faithful_spend: Option<&FaithfulSpendGameAuthorityReceipt>,
    authority_digest: [u8; 32],
    certificate_digest: [u8; 32],
    private_session: u32,
    private_root: [u32; 8],
    market_asset_id: [u8; 32],
    market_winner: &DreggIdentity,
    winner_route_digest: [u8; 32],
    game_signer_pubkey_hex: &str,
    target_session: &GameSessionRef,
    action_preimage_id: [u8; 32],
    game_receipt_id: [u8; 32],
    inner_game_receipt_id: [u8; 32],
    ended: bool,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CONSEQUENCE_DOMAIN);
    hash_field(&mut hasher, &authorization_id);
    hash_field(&mut hasher, mechanic.tag());
    match faithful_spend {
        Some(spend) => {
            hash_field(&mut hasher, &[1]);
            hash_field(&mut hasher, &spend.authority_digest);
        }
        None => hash_field(&mut hasher, &[0]),
    }
    hash_field(&mut hasher, &authority_digest);
    hash_field(&mut hasher, &certificate_digest);
    hash_field(&mut hasher, &private_session.to_be_bytes());
    for lane in private_root {
        hash_field(&mut hasher, &lane.to_be_bytes());
    }
    hash_field(&mut hasher, &market_asset_id);
    hash_field(&mut hasher, market_winner.0.as_bytes());
    hash_field(&mut hasher, &winner_route_digest);
    hash_field(&mut hasher, game_signer_pubkey_hex.as_bytes());
    hash_game_session(&mut hasher, target_session);
    hash_field(&mut hasher, &action_preimage_id);
    hash_field(&mut hasher, &game_receipt_id);
    hash_field(&mut hasher, &inner_game_receipt_id);
    hash_field(&mut hasher, &[u8::from(ended)]);
    *hasher.finalize().as_bytes()
}

fn hash_game_session(hasher: &mut blake3::Hasher, session: &GameSessionRef) {
    hash_field(hasher, session.offering().as_bytes());
    hash_field(hasher, session.session_id().0.as_bytes());
    match session.binding() {
        GameSessionBinding::LegacyUnbound => hash_field(hasher, &[0]),
        GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } => {
            hash_field(hasher, &[1]);
            hash_field(hasher, host_incarnation.as_bytes());
            hash_field(hasher, &session_generation.to_be_bytes());
        }
    }
}

fn hash_field(hasher: &mut blake3::Hasher, value: &[u8]) {
    hasher.update(&(value.len() as u64).to_be_bytes());
    hasher.update(value);
}

#[cfg(test)]
mod tests {
    use dreggnet_offerings::dungeon::{DungeonOffering, PRIVATE_RAID_OPERATION};
    use dreggnet_offerings::{DreggIdentity, OfferingHost, SessionConfig, SessionId, TurnSigner};
    use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};
    use dungeon_on_dregg::{
        KP_CLAIM_BLUE, KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_PRIVATE_RAID_MENDER_CHOICES,
        KP_TRADE_BLOWS,
    };

    use crate::game_spine::{
        GameAffordance, GameAudience, GameCommand, GameHostIncarnation, GameSessionRef,
        execute_bound_asserted_game_command, inspect_bound_game_session,
    };

    use super::*;

    const SESSION: &str = "private-fhegg-raid-mender";
    const GENERATION: u64 = 1;

    fn action_at(view: &crate::game_spine::GameSessionView, arg: usize) -> (GameActionRef, Action) {
        view.affordances
            .iter()
            .find_map(|affordance| match affordance {
                GameAffordance::Turn {
                    reference, action, ..
                } if i64::try_from(arg).ok() == Some(action.arg) => {
                    Some((reference.clone(), action.clone()))
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("live dungeon omitted choice {arg}"))
    }

    fn operation_at(
        view: &crate::game_spine::GameSessionView,
        name: &str,
        payload: Vec<u8>,
    ) -> GameCommand {
        view.affordances
            .iter()
            .find_map(|affordance| match affordance {
                GameAffordance::Operation { reference, .. } if reference.operation == name => {
                    Some(GameCommand::Operation {
                        reference: reference.clone(),
                        payload: payload.clone(),
                    })
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("live dungeon omitted operation {name}"))
    }

    fn inspect(
        host: &OfferingHost,
        incarnation: GameHostIncarnation,
        session: &GameSessionRef,
    ) -> crate::game_spine::GameSessionView {
        inspect_bound_game_session(
            host,
            incarnation,
            GENERATION,
            session.clone(),
            &GameAudience::Shared,
        )
        .expect("bound game inspection")
    }

    #[test]
    fn private_bazaar_winner_spends_the_proof_assigned_mender_through_signed_spine_once() {
        let incarnation = GameHostIncarnation::new([0x41; 32]).unwrap();
        let id = SessionId::new(SESSION);
        let session = GameSessionRef::bound("dungeon", id.clone(), incarnation, GENERATION)
            .expect("bound dungeon session");
        let mut host = OfferingHost::new();
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        host.open_session("dungeon", id.clone(), SessionConfig::with_seed(31_337))
            .expect("dungeon opens");
        let epochs = GameEpochLedger::in_memory(incarnation);
        assert_eq!(
            epochs
                .bind_after_ensure("dungeon", &id, true)
                .expect("fresh session obtains a generation"),
            GENERATION
        );

        // Reach the 30-HP sanctum through ordinary common-spine turns.
        for choice in [KP_TRADE_BLOWS, KP_PRESS_ON, KP_DESCEND] {
            let view = inspect(&host, incarnation, &session);
            let (reference, action) = action_at(&view, choice);
            let result = execute_bound_asserted_game_command(
                &mut host,
                incarnation,
                GENERATION,
                &session,
                GameCommand::Turn { reference, action },
                DreggIdentity("raid-pathfinder".to_owned()),
            )
            .expect("setup route is well formed");
            assert!(matches!(result, GameResult::Landed(_)));
        }

        // A different private proof establishes the role permutation. Its
        // scores/admissibility matrix never enters the fhEgg consequence gate.
        let scores = [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]];
        let assignment = prove_private_assignment(
            ((31_337u64 % 2_013_265_920) + 1) as u32,
            scores,
            [[true; 4]; 4],
        )
        .expect("private raid assignment proves");
        let mender_seat = assignment
            .statement()
            .roles
            .iter()
            .position(|role| *role == RaidRole::Mender as u8)
            .expect("role permutation has one Mender");
        let mender_choice = KP_PRIVATE_RAID_MENDER_CHOICES[mender_seat];
        let view = inspect(&host, incarnation, &session);
        let command = operation_at(
            &view,
            PRIVATE_RAID_OPERATION,
            assignment
                .to_postcard()
                .expect("canonical public proof receipt"),
        );
        let applied = execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            GENERATION,
            &session,
            command,
            DreggIdentity("raid-proof-uploader".to_owned()),
        )
        .expect("proof operation route is well formed");
        assert!(matches!(applied, GameResult::Landed(_)));

        let winner = DreggIdentity("bazaar:winner".to_owned());
        let winner_signer = TurnSigner::from_seed([0x51; 32]);
        let route = PrivateFheggWinnerRoute::new(winner.clone(), winner_signer.pubkey_hex())
            .expect("deployment pins winner to signer");
        let view = inspect(&host, incarnation, &session);
        let (reference, action) = action_at(&view, mender_choice);
        let authority = PrivateFheggGameAuthority::fixture(winner);
        let mut gate = PrivateFheggGameConsequenceGate::from_authority(
            authority.clone(),
            [0x18; 32],
            route.clone(),
            PrivateFheggGameMechanic::DungeonRaidMender,
            &epochs,
            reference.clone(),
            action.clone(),
        )
        .expect("exact private authority targets the assigned Mender action");

        // A different signer is refused before common-spine dispatch and does
        // not stale the target head or consume the authorization.
        let thief = TurnSigner::from_seed([0x52; 32]);
        let stolen = gate
            .execute_signed(&mut host, thief.sign("dungeon", &id, 0, action.clone()))
            .expect_err("nonwinner key cannot spend the Bazaar result");
        assert_eq!(stolen, PrivateFheggGameConsequenceError::WrongGameSigner);
        assert!(!gate.is_consumed());

        // A close/reopen in epoch custody invalidates an already captured gate
        // even when the in-memory game happens to retain a byte-identical head.
        assert!(epochs.mark_closed("dungeon", &id).unwrap());
        let current_generation = epochs.bind_after_ensure("dungeon", &id, true).unwrap();
        assert_eq!(current_generation, GENERATION + 1);
        let replaced = gate
            .execute_signed(
                &mut host,
                winner_signer.sign("dungeon", &id, 0, action.clone()),
            )
            .expect_err("captured generation cannot survive epoch replacement");
        assert_eq!(
            replaced,
            PrivateFheggGameConsequenceError::AuthorityEpochMismatch
        );
        assert!(!gate.is_consumed());
        let before = format!("{:?}", host.render("dungeon", &id).unwrap().0);
        assert!(before.contains("HP 30"), "{before}");

        let current_session = epochs.bound_session("dungeon", &id).unwrap();
        let current_reference = GameActionRef::new(
            current_session.clone(),
            &action,
            reference.expected_pre_head.clone(),
        );
        let mut gate = PrivateFheggGameConsequenceGate::from_authority(
            authority,
            [0x18; 32],
            route,
            PrivateFheggGameMechanic::DungeonRaidMender,
            &epochs,
            current_reference.clone(),
            action.clone(),
        )
        .expect("current epoch can bind the still-live exact action");

        let landed = gate
            .execute_signed(
                &mut host,
                winner_signer.sign("dungeon", &id, 0, action.clone()),
            )
            .expect("winner's exact signed Mender turn lands");
        assert!(landed.binding_verifies());
        assert_eq!(landed.target_session, current_session);
        assert_eq!(
            landed.action_preimage_id,
            current_reference.routing_preimage_id()
        );
        assert_eq!(landed.market_winner.0, "bazaar:winner");
        assert!(gate.is_consumed());
        assert!(host.verify("dungeon", &id).unwrap().verified);
        let rendered = format!("{:?}", host.render("dungeon", &id).unwrap().0);
        assert!(rendered.contains("HP 50"), "{rendered}");

        for tamper in 0..4 {
            let mut forged = landed.clone();
            match tamper {
                0 => forged.market_winner.0.push_str(":substituted"),
                1 => forged.private_root[0] ^= 1,
                2 => forged.action_preimage_id[0] ^= 1,
                3 => forged.game_receipt_id[0] ^= 1,
                _ => unreachable!(),
            }
            assert!(
                !forged.binding_verifies(),
                "public consequence substitution {tamper} must break its binding"
            );
        }

        let replay = gate
            .execute_signed(&mut host, winner_signer.sign("dungeon", &id, 1, action))
            .expect_err("private authorization is one-shot before dispatch");
        assert_eq!(replay, PrivateFheggGameConsequenceError::AlreadyConsumed);
    }

    #[test]
    fn shielded_bazaar_tender_claims_one_executor_enforced_dungeon_crown() {
        let incarnation = GameHostIncarnation::new([0x81; 32]).unwrap();
        let id = SessionId::new("private-fhegg-shielded-crown");
        let session = GameSessionRef::bound("dungeon", id.clone(), incarnation, GENERATION)
            .expect("bound dungeon session");
        let mut host = OfferingHost::new();
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        host.open_session("dungeon", id.clone(), SessionConfig::with_seed(99))
            .expect("dungeon opens");
        let epochs = GameEpochLedger::in_memory(incarnation);
        assert_eq!(
            epochs
                .bind_after_ensure("dungeon", &id, true)
                .expect("fresh session obtains a generation"),
            GENERATION
        );

        // Reach the contested crown through an ordinary common-spine turn.
        let view = inspect(&host, incarnation, &session);
        let (press_reference, press_action) = action_at(&view, KP_PRESS_ON);
        let pressed = execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            GENERATION,
            &session,
            GameCommand::Turn {
                reference: press_reference,
                action: press_action,
            },
            DreggIdentity("crown-pathfinder".to_owned()),
        )
        .expect("hall route is well formed");
        assert!(matches!(pressed, GameResult::Landed(_)));

        let winner = DreggIdentity("bazaar:shielded-winner".to_owned());
        let winner_signer = TurnSigner::from_seed([0x82; 32]);
        let winner_route = PrivateFheggWinnerRoute::new(winner.clone(), winner_signer.pubkey_hex())
            .expect("deployment pins winner to signer");
        let authority = PrivateFheggGameAuthority::fixture(winner);
        let finalized_spend = FinalizedFaithfulSpendAuthority::fixture(3, 77, [0x83; 32]);
        let view = inspect(&host, incarnation, &session);
        let (claim_reference, claim_action) = action_at(&view, KP_CLAIM_RED);
        let mut gate = PrivateFheggGameConsequenceGate::from_authorities(
            authority,
            Some(finalized_spend),
            [0x18; 32],
            Some(77),
            winner_route,
            PrivateFheggGameMechanic::DungeonShieldedCrown,
            &epochs,
            claim_reference.clone(),
            claim_action.clone(),
        )
        .expect("the exact finalized shielded tender authorizes the exact crown");

        // Bazaar winner routing is independently enforced: possession of a
        // finalized spend authority alone cannot substitute the game signer.
        let thief = TurnSigner::from_seed([0x84; 32]);
        let stolen = gate
            .execute_signed(
                &mut host,
                thief.sign("dungeon", &id, 0, claim_action.clone()),
            )
            .expect_err("unmapped signer cannot spend the shielded authorization");
        assert_eq!(stolen, PrivateFheggGameConsequenceError::WrongGameSigner);
        assert!(!gate.is_consumed());

        let landed = gate
            .execute_signed(
                &mut host,
                winner_signer.sign("dungeon", &id, 0, claim_action.clone()),
            )
            .expect("mapped Bazaar winner lands the exact crown turn");
        assert!(landed.binding_verifies());
        assert_eq!(
            landed.mechanic,
            PrivateFheggGameMechanic::DungeonShieldedCrown
        );
        let spend = landed
            .faithful_spend
            .as_ref()
            .expect("shielded consequence publishes its secret-free spend authority");
        assert_eq!(spend.value, 3);
        assert_eq!(spend.asset_type, 77);
        assert_eq!(
            landed.action_preimage_id,
            claim_reference.routing_preimage_id()
        );
        assert!(host.verify("dungeon", &id).unwrap().verified);
        let rendered = format!("{:?}", host.render("dungeon", &id).unwrap().0);
        assert!(rendered.contains("crown Red Hand"), "{rendered}");

        // The public consequence commits both authorities. Substituting the
        // tender, game receipt, or chosen private result breaks verification.
        for tamper in 0..4 {
            let mut forged = landed.clone();
            match tamper {
                0 => forged.faithful_spend.as_mut().expect("present").asset_type ^= 1,
                1 => forged.faithful_spend.as_mut().expect("present").nullifier[0] ^= 1,
                2 => forged.private_root[0] ^= 1,
                3 => forged.game_receipt_id[0] ^= 1,
                _ => unreachable!(),
            }
            assert!(
                !forged.binding_verifies(),
                "public shielded consequence substitution {tamper} must break its binding"
            );
        }

        let replay = gate
            .execute_signed(
                &mut host,
                winner_signer.sign("dungeon", &id, 1, claim_action),
            )
            .expect_err("shielded authorization is one-shot before dispatch");
        assert_eq!(replay, PrivateFheggGameConsequenceError::AlreadyConsumed);

        // The world itself has the final anti-double-claim tooth. A rival Blue
        // claim reaches the real executor and is refused by the shared owner
        // slot's WriteOnce constraint; it is not a test-only gate boolean.
        let view = inspect(&host, incarnation, &session);
        let (blue_reference, blue_action) = action_at(&view, KP_CLAIM_BLUE);
        let rival = execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            GENERATION,
            &session,
            GameCommand::Turn {
                reference: blue_reference,
                action: blue_action,
            },
            DreggIdentity("rival-hand".to_owned()),
        )
        .expect("rival route reaches the executor");
        assert!(matches!(rival, GameResult::Refused { .. }));
    }

    #[test]
    fn gate_refuses_unbound_non_mender_and_winner_route_substitution() {
        let winner = DreggIdentity("bazaar:winner".to_owned());
        let signer = TurnSigner::from_seed([0x61; 32]);
        let route = PrivateFheggWinnerRoute::new(winner.clone(), signer.pubkey_hex()).unwrap();
        let authority = PrivateFheggGameAuthority::fixture(winner.clone());
        let incarnation = GameHostIncarnation::new([0x62; 32]).unwrap();
        let epochs = GameEpochLedger::in_memory(incarnation);
        for session in ["hostile-route", "winner-substitution", "epoch-substitution"] {
            epochs
                .bind_after_ensure("dungeon", &SessionId::new(session), true)
                .unwrap();
        }
        let bound =
            GameSessionRef::bound("dungeon", SessionId::new("hostile-route"), incarnation, 1)
                .unwrap();
        let non_mender = Action::new(
            "descend",
            dreggnet_offerings::dungeon::TURN_CHOOSE,
            KP_DESCEND as i64,
            true,
        );
        let non_mender_ref = GameActionRef::new(bound, &non_mender, vec![1]);
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                authority.clone(),
                [0x18; 32],
                route.clone(),
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                non_mender_ref,
                non_mender,
            ),
            Err(PrivateFheggGameConsequenceError::WrongMechanicTarget)
        ));

        let mender = Action::new(
            "mend",
            dreggnet_offerings::dungeon::TURN_CHOOSE,
            KP_PRIVATE_RAID_MENDER_CHOICES[0] as i64,
            true,
        );
        let asset_bound =
            GameSessionRef::bound("dungeon", SessionId::new("hostile-route"), incarnation, 1)
                .unwrap();
        let asset_ref = GameActionRef::new(asset_bound, &mender, vec![1]);
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                authority.clone(),
                [0x99; 32],
                route.clone(),
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                asset_ref,
                mender.clone(),
            ),
            Err(PrivateFheggGameConsequenceError::MarketAssetMismatch)
        ));

        let unbound = GameSessionRef::new("dungeon", SessionId::new("legacy-route")).unwrap();
        let unbound_ref = GameActionRef::new(unbound, &mender, vec![1]);
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                authority.clone(),
                [0x18; 32],
                route,
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                unbound_ref,
                mender.clone(),
            ),
            Err(PrivateFheggGameConsequenceError::UnboundGameSession)
        ));

        let other_route = PrivateFheggWinnerRoute::new(
            DreggIdentity("bazaar:other".to_owned()),
            signer.pubkey_hex(),
        )
        .unwrap();
        let bound = GameSessionRef::bound(
            "dungeon",
            SessionId::new("winner-substitution"),
            incarnation,
            1,
        )
        .unwrap();
        let reference = GameActionRef::new(bound, &mender, vec![1]);
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                authority,
                [0x18; 32],
                other_route,
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                reference,
                mender.clone(),
            ),
            Err(PrivateFheggGameConsequenceError::WinnerRouteMismatch)
        ));

        let wrong_incarnation = GameHostIncarnation::new([0x63; 32]).unwrap();
        let substituted_epoch = GameSessionRef::bound(
            "dungeon",
            SessionId::new("epoch-substitution"),
            wrong_incarnation,
            1,
        )
        .unwrap();
        let substituted_epoch_ref = GameActionRef::new(substituted_epoch, &mender, vec![1]);
        let route = PrivateFheggWinnerRoute::new(winner.clone(), signer.pubkey_hex()).unwrap();
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                PrivateFheggGameAuthority::fixture(winner),
                [0x18; 32],
                route,
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                substituted_epoch_ref,
                mender,
            ),
            Err(PrivateFheggGameConsequenceError::AuthorityEpochMismatch)
        ));
    }

    #[test]
    fn shielded_crown_refuses_missing_or_mismatched_finalized_tender() {
        let winner = DreggIdentity("bazaar:shielded-winner".to_owned());
        let signer = TurnSigner::from_seed([0x91; 32]);
        let route = PrivateFheggWinnerRoute::new(winner.clone(), signer.pubkey_hex()).unwrap();
        let authority = PrivateFheggGameAuthority::fixture(winner);
        let incarnation = GameHostIncarnation::new([0x92; 32]).unwrap();
        let id = SessionId::new("shielded-crown-policy");
        let epochs = GameEpochLedger::in_memory(incarnation);
        epochs.bind_after_ensure("dungeon", &id, true).unwrap();
        let session = GameSessionRef::bound("dungeon", id, incarnation, GENERATION).unwrap();
        let claim = Action::new(
            "claim red",
            dreggnet_offerings::dungeon::TURN_CHOOSE,
            KP_CLAIM_RED as i64,
            true,
        );
        let reference = GameActionRef::new(session, &claim, vec![1]);

        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authority(
                authority.clone(),
                [0x18; 32],
                route.clone(),
                PrivateFheggGameMechanic::DungeonShieldedCrown,
                &epochs,
                reference.clone(),
                claim.clone(),
            ),
            Err(PrivateFheggGameConsequenceError::MissingFaithfulSpendAuthority)
        ));

        for bad_spend in [
            FinalizedFaithfulSpendAuthority::fixture(4, 77, [0x93; 32]),
            FinalizedFaithfulSpendAuthority::fixture(3, 78, [0x93; 32]),
        ] {
            assert!(matches!(
                PrivateFheggGameConsequenceGate::from_authorities(
                    authority.clone(),
                    Some(bad_spend),
                    [0x18; 32],
                    Some(77),
                    route.clone(),
                    PrivateFheggGameMechanic::DungeonShieldedCrown,
                    &epochs,
                    reference.clone(),
                    claim.clone(),
                ),
                Err(PrivateFheggGameConsequenceError::FaithfulTenderMismatch)
            ));
        }

        let mender = Action::new(
            "mend",
            dreggnet_offerings::dungeon::TURN_CHOOSE,
            KP_PRIVATE_RAID_MENDER_CHOICES[0] as i64,
            true,
        );
        let mender_reference = GameActionRef::new(reference.session.clone(), &mender, vec![1]);
        assert!(matches!(
            PrivateFheggGameConsequenceGate::from_authorities(
                authority,
                Some(FinalizedFaithfulSpendAuthority::fixture(3, 77, [0x93; 32])),
                [0x18; 32],
                Some(77),
                route,
                PrivateFheggGameMechanic::DungeonRaidMender,
                &epochs,
                mender_reference,
                mender,
            ),
            Err(PrivateFheggGameConsequenceError::UnexpectedFaithfulSpendAuthority)
        ));
    }
}
