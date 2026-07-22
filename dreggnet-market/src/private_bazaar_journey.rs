//! A playable, viewer-blind shell around the private Dark Bazaar raid path.
//!
//! The cryptographic and game-authority work remains in the existing modules:
//! `private_clearing` verifies the hiding proof and lands the real market clear,
//! `private_clearing_guild_allocation` binds its private winner to an exact
//! existing-character roster, and `private_clearing_consequence` lets that
//! result authorize exactly one real executor turn. This module supplies the
//! piece those backend APIs deliberately did not: one frontend-neutral player
//! journey that a browser, Discord, Telegram, or WeChat adapter can render.
//!
//! The adapter-facing contract contains only:
//! * fixed, payload-free [`Action`]s (`enter` and `refresh`);
//! * a [`Surface`] derived without a viewer identity; and
//! * a public pending/settled receipt containing commitments and landed turn
//!   hashes, never bids, reserve, winner, roster members, proof bytes, witness,
//!   selected character, or reward-opening material.
//!
//! Constructing a public receipt is not authorization. Under the
//! `private-clearing` feature, only [`PrivateBazaarRaidJourney::settle_verified`]
//! crosses from a verified private receipt into a target game's real turn.
//! This does not upgrade the fixed-book producer to house-blind operation:
//! `prepare_private_clearing_zk` still sees the order witness in its process.
//! A live fhEgg/BFV deployment can feed the same public journey after its
//! stronger source/attestation boundary is welded to this consequence API.

use deos_view::ViewNode;
use dreggnet_offerings::{Action, Surface};

pub const TURN_ENTER_PRIVATE_BAZAAR: &str = "enter-private-bazaar";
pub const TURN_REFRESH_PRIVATE_BAZAAR: &str = "refresh-private-bazaar";

#[cfg(feature = "private-clearing")]
const JOURNEY_DOMAIN: &str = "dreggnet-market/private-bazaar-player-journey/v1";
#[cfg(feature = "private-clearing")]
const REWARD_DOMAIN: &str = "dreggnet-market/private-bazaar-public-reward/v1";

/// The complete semantic action vocabulary accepted from public game surfaces.
/// Neither variant can transport a bid, reserve, witness, identity, or arbitrary
/// bytes. Those values enter only through their owning authenticated/private
/// protocols.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBazaarPublicAction {
    Enter,
    Refresh,
}

impl PrivateBazaarPublicAction {
    /// Encode into the one action type every `OfferingHost` frontend consumes.
    pub fn offering_action(self) -> Action {
        match self {
            Self::Enter => Action::new(
                "Enter the shielded raid allocation",
                TURN_ENTER_PRIVATE_BAZAAR,
                0,
                true,
            ),
            Self::Refresh => Action::new(
                "Refresh the public receipt",
                TURN_REFRESH_PRIVATE_BAZAAR,
                0,
                true,
            ),
        }
    }

    /// Decode a shared frontend action, refusing every payload-bearing or
    /// noncanonical shape. Labels are presentation and are intentionally not an
    /// authority input; the fixed `(turn, arg, text)` carrier is.
    pub fn from_offering_action(action: &Action) -> Result<Self, PrivateBazaarJourneyError> {
        if action.arg != 0 || action.text.is_some() || action.wants_text {
            return Err(PrivateBazaarJourneyError::PublicActionCarriesPayload);
        }
        match action.turn.as_str() {
            TURN_ENTER_PRIVATE_BAZAAR => Ok(Self::Enter),
            TURN_REFRESH_PRIVATE_BAZAAR => Ok(Self::Refresh),
            _ => Err(PrivateBazaarJourneyError::UnknownPublicAction),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBazaarPublicPhase {
    Pending,
    Settled,
}

impl PrivateBazaarPublicPhase {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Settled => "settled",
        }
    }
}

/// The same public result is safe to place in a shared channel or return to any
/// browser viewer. It deliberately has no actor/viewer field and no selected
/// member, winner, bid, price, reserve, proof, ciphertext, or witness field.
/// The roster/reward digests are binding public identifiers, not hiding
/// commitments; no privacy claim relies on their preimage resistance against a
/// small, guessable policy space.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarPublicReceipt {
    pub journey_id: [u8; 32],
    pub phase: PrivateBazaarPublicPhase,
    pub participant_count: u32,
    pub roster_commitment: [u8; 32],
    pub reward_commitment: [u8; 32],
    pub proof_session: Option<u32>,
    pub input_root: Option<[u32; 8]>,
    pub consequence_id: Option<[u8; 32]>,
    pub settlement_turn_hash: Option<[u8; 32]>,
    pub game_turn_hash: Option<[u8; 32]>,
    pub game_state_root: Option<[u8; 32]>,
}

impl PrivateBazaarPublicReceipt {
    /// Build the shared pending projection. This is presentation state, not a
    /// proof or authorization constructor.
    pub fn pending(
        journey_id: [u8; 32],
        participant_count: u32,
        roster_commitment: [u8; 32],
        reward_commitment: [u8; 32],
    ) -> Self {
        Self {
            journey_id,
            phase: PrivateBazaarPublicPhase::Pending,
            participant_count,
            roster_commitment,
            reward_commitment,
            proof_session: None,
            input_root: None,
            consequence_id: None,
            settlement_turn_hash: None,
            game_turn_hash: None,
            game_state_root: None,
        }
    }

    /// Public fields suitable for the existing web/chat binary-operation
    /// receipt allowlists. Values are commitments or already-public proof/turn
    /// outputs; private openings are not retained by this type.
    pub fn public_fields(&self) -> Vec<(String, String)> {
        let mut fields = vec![
            ("phase".to_owned(), self.phase.as_str().to_owned()),
            ("participant".to_owned(), self.participant_count.to_string()),
            ("requestDigest".to_owned(), hex32(self.journey_id)),
            (
                "decisionBundleDigest".to_owned(),
                hex32(self.roster_commitment),
            ),
            (
                "decisionClaimDigest".to_owned(),
                hex32(self.reward_commitment),
            ),
        ];
        if let Some(session) = self.proof_session {
            fields.push(("proofSession".to_owned(), session.to_string()));
        }
        if let Some(root) = self.input_root {
            fields.push(("inputRoot".to_owned(), hex_felts(root)));
        }
        if let Some(id) = self.consequence_id {
            fields.push(("statementDigest".to_owned(), hex32(id)));
        }
        if let Some(hash) = self.settlement_turn_hash {
            fields.push(("proofDigest".to_owned(), hex32(hash)));
        }
        if let Some(hash) = self.game_turn_hash {
            fields.push(("outcome".to_owned(), hex32(hash)));
        }
        if let Some(root) = self.game_state_root {
            fields.push(("newRoot".to_owned(), hex32(root)));
        }
        fields
    }

    /// One viewer-blind deos tree. Both browser and chat adapters render this
    /// exact [`Surface`] rather than rebuilding a Bazaar-specific DTO.
    pub fn surface(&self) -> Surface {
        let state = match self.phase {
            PrivateBazaarPublicPhase::Pending => vec![
                ViewNode::Text(
                    "The party entered. Private inputs remain with their owning protocol while the public receipt is pending."
                        .to_owned(),
                ),
                ViewNode::Text(format!(
                    "{} committed participants · roster {} · reward {}",
                    self.participant_count,
                    short_hex(self.roster_commitment),
                    short_hex(self.reward_commitment),
                )),
            ],
            PrivateBazaarPublicPhase::Settled => vec![
                ViewNode::Text(
                    "Settled: a verified private result caused one real game-engine turn."
                        .to_owned(),
                ),
                ViewNode::Text(format!(
                    "input {} · consequence {} · game state {}",
                    self.input_root.map(short_felts).unwrap_or_else(|| "missing".to_owned()),
                    self.consequence_id.map(short_hex).unwrap_or_else(|| "missing".to_owned()),
                    self.game_state_root.map(short_hex).unwrap_or_else(|| "missing".to_owned()),
                )),
            ],
        };
        Surface(ViewNode::Section {
            title: format!("Dark Bazaar raid · {}", self.phase.as_str()),
            tag: if self.phase == PrivateBazaarPublicPhase::Settled {
                "good".to_owned()
            } else {
                "accent".to_owned()
            },
            children: vec![
                ViewNode::Text(format!("Public journey {}", short_hex(self.journey_id))),
                ViewNode::Section {
                    title: "Viewer-blind receipt".to_owned(),
                    tag: "muted".to_owned(),
                    children: state,
                },
            ],
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PrivateBazaarJourneyError {
    UnknownPublicAction,
    PublicActionCarriesPayload,
    EnterAlreadySubmitted,
    RefreshBeforeEnter,
    SettlementBeforeEnter,
    SettlementAlreadyApplied,
    RecoveryRequired,
    MarketNotReady,
    MissingGameStateRoot,
    #[cfg(feature = "private-clearing")]
    Source(crate::private_clearing_consequence::PrivateClearingConsequenceError),
    #[cfg(feature = "private-clearing")]
    Allocation(crate::private_clearing_guild_allocation::PrivateClearingGuildAllocationError),
}

impl std::fmt::Display for PrivateBazaarJourneyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar journey refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarJourneyError {}

#[cfg(feature = "private-clearing")]
impl From<crate::private_clearing_consequence::PrivateClearingConsequenceError>
    for PrivateBazaarJourneyError
{
    fn from(error: crate::private_clearing_consequence::PrivateClearingConsequenceError) -> Self {
        Self::Source(error)
    }
}

#[cfg(feature = "private-clearing")]
impl From<crate::private_clearing_guild_allocation::PrivateClearingGuildAllocationError>
    for PrivateBazaarJourneyError
{
    fn from(
        error: crate::private_clearing_guild_allocation::PrivateClearingGuildAllocationError,
    ) -> Self {
        Self::Allocation(error)
    }
}

/// Server-side state for one public journey. Its roster and reward openings are
/// intentionally absent from [`PrivateBazaarPublicReceipt`].
#[cfg(feature = "private-clearing")]
pub struct PrivateBazaarRaidJourney {
    market_session: u32,
    roster: crate::private_clearing_guild_allocation::GuildRoster,
    reward: crate::private_clearing_guild_allocation::GuildReward,
    journey_id: [u8; 32],
    reward_commitment: [u8; 32],
    receipt: Option<PrivateBazaarPublicReceipt>,
    recovery_only: bool,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarRaidJourney {
    /// Bind an existing market session to an existing game roster and a
    /// product-selected reward. The market must already have a listing and must
    /// still be awaiting its private clear.
    pub fn new(
        session: &crate::DarkBazaarSession,
        roster: crate::private_clearing_guild_allocation::GuildRoster,
        reward: crate::private_clearing_guild_allocation::GuildReward,
    ) -> Result<Self, PrivateBazaarJourneyError> {
        if !session.is_listed() || session.is_settled() {
            return Err(PrivateBazaarJourneyError::MarketNotReady);
        }
        Ok(Self::bound(session, roster, reward, false))
    }

    /// Reconstruct the exact pending public journey after a process restart in
    /// the narrow window where the target game's turn committed but the public
    /// settled receipt did not. Recovery still requires an independently
    /// observed [`PrivateClearingCommittedObservation`](crate::private_clearing_consequence::PrivateClearingCommittedObservation);
    /// this constructor does not mark a consequence settled by itself.
    pub fn resume_pending(
        session: &crate::DarkBazaarSession,
        roster: crate::private_clearing_guild_allocation::GuildRoster,
        reward: crate::private_clearing_guild_allocation::GuildReward,
    ) -> Result<Self, PrivateBazaarJourneyError> {
        if !session.is_listed() || !session.is_settled() {
            return Err(PrivateBazaarJourneyError::MarketNotReady);
        }
        Ok(Self::bound(session, roster, reward, true))
    }

    fn bound(
        session: &crate::DarkBazaarSession,
        roster: crate::private_clearing_guild_allocation::GuildRoster,
        reward: crate::private_clearing_guild_allocation::GuildReward,
        pending: bool,
    ) -> Self {
        let market_session = session.private_proof_session();
        let reward_commitment = reward_commitment(&reward.kind, reward.amount);
        let journey_id = journey_id(
            market_session,
            roster.digest(),
            reward_commitment,
            roster.ordered_members().len() as u32,
        );
        let receipt = pending.then(|| {
            PrivateBazaarPublicReceipt::pending(
                journey_id,
                roster.ordered_members().len() as u32,
                roster.digest(),
                reward_commitment,
            )
        });
        Self {
            market_session,
            roster,
            reward,
            journey_id,
            reward_commitment,
            receipt,
            // `resume_pending` exists specifically for the post-game/public-
            // receipt crash window. It must never redispatch the game turn.
            recovery_only: pending,
        }
    }

    pub fn actions(&self) -> Vec<Action> {
        let semantic = if self.receipt.is_none() {
            PrivateBazaarPublicAction::Enter
        } else {
            PrivateBazaarPublicAction::Refresh
        };
        vec![semantic.offering_action()]
    }

    pub fn receipt(&self) -> Option<&PrivateBazaarPublicReceipt> {
        self.receipt.as_ref()
    }

    /// Apply only the payload-free public action grammar. Entering publishes a
    /// pending commitment receipt; refresh is a pure read and cannot alter the
    /// market, proof, or target game.
    pub fn advance_public(
        &mut self,
        action: &Action,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError> {
        match PrivateBazaarPublicAction::from_offering_action(action)? {
            PrivateBazaarPublicAction::Enter => {
                if self.receipt.is_some() {
                    return Err(PrivateBazaarJourneyError::EnterAlreadySubmitted);
                }
                self.receipt = Some(PrivateBazaarPublicReceipt::pending(
                    self.journey_id,
                    self.roster.ordered_members().len() as u32,
                    self.roster.digest(),
                    self.reward_commitment,
                ));
            }
            PrivateBazaarPublicAction::Refresh => {
                if self.receipt.is_none() {
                    return Err(PrivateBazaarJourneyError::RefreshBeforeEnter);
                }
            }
        }
        Ok(self.receipt.as_ref().expect("enter or existing receipt"))
    }

    /// Consume a verified private clearing and apply exactly one real turn to
    /// the selected existing character. The callback receives the selected
    /// server-side roster member and reward opening; neither is copied into the
    /// public receipt.
    pub fn settle_verified<F>(
        &mut self,
        session: &crate::DarkBazaarSession,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
        game_turn: F,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError>
    where
        F: FnOnce(
            &crate::private_clearing_guild_allocation::GuildMember,
            &crate::private_clearing_guild_allocation::GuildReward,
        ) -> Result<dregg_app_framework::TurnReceipt, String>,
    {
        self.settle_verified_with_commit_hook(session, private_receipt, game_turn, |_| Ok(()))
    }

    /// Durable form of [`Self::settle_verified`]. After the target game turn is
    /// committed and shape-checked, `after_game_commit` receives the exact
    /// observation needed by [`Self::recover_verified`]. A hook error leaves
    /// this public journey pending, so restart recovery can close the window
    /// without dispatching the game turn again.
    pub fn settle_verified_with_commit_hook<F, H>(
        &mut self,
        session: &crate::DarkBazaarSession,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
        game_turn: F,
        after_game_commit: H,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError>
    where
        F: FnOnce(
            &crate::private_clearing_guild_allocation::GuildMember,
            &crate::private_clearing_guild_allocation::GuildReward,
        ) -> Result<dregg_app_framework::TurnReceipt, String>,
        H: FnOnce(
            crate::private_clearing_consequence::PrivateClearingCommittedObservation,
        ) -> Result<(), String>,
    {
        self.require_pending(private_receipt)?;
        if self.recovery_only {
            return Err(PrivateBazaarJourneyError::RecoveryRequired);
        }
        let allocation = self.allocation(private_receipt)?;
        let target = allocation.selected_member().character_cell;
        let consequence_tag = allocation.consequence_tag();
        let mut gate = allocation.consequence_gate();
        let post_state = std::cell::Cell::new(None::<[u8; 32]>);
        let consequence = match gate.apply_game_turn_with_commit_hook(
            session,
            private_receipt,
            target,
            || game_turn(allocation.selected_member(), allocation.reward()),
            |consequence_id, receipt| {
                post_state.set(Some(receipt.post_state_hash));
                after_game_commit(
                    crate::private_clearing_consequence::PrivateClearingCommittedObservation::new(
                        consequence_id,
                        target,
                        consequence_tag,
                        receipt.clone(),
                    ),
                )
            },
        ) {
            Ok(consequence) => consequence,
            Err(
                error @ crate::private_clearing_consequence::PrivateClearingConsequenceError::ReplayCommitInterrupted(_),
            ) => {
                // The target turn is already committed. From this point on the
                // only safe operation is exact observation/recovery; retrying
                // the callback could apply the reward twice.
                self.recovery_only = true;
                return Err(error.into());
            }
            Err(error) => return Err(error.into()),
        };
        let game_state_root = post_state
            .get()
            .ok_or(PrivateBazaarJourneyError::MissingGameStateRoot)?;
        Ok(self.install_settled(consequence, game_state_root))
    }

    /// Recover a target game turn that committed before the public settled
    /// receipt persisted. `observe` must query the target engine's durable
    /// receipt/state index and return only an exact routing match; the existing
    /// consequence gate performs the final id/target/tag and receipt checks.
    pub fn recover_verified<O>(
        &mut self,
        session: &crate::DarkBazaarSession,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
        observe: O,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError>
    where
        O: FnOnce(
            [u8; 32],
            dregg_app_framework::CellId,
            crate::private_clearing_consequence::PrivateClearingConsequenceTag,
        ) -> Result<
            Option<crate::private_clearing_consequence::PrivateClearingCommittedObservation>,
            String,
        >,
    {
        self.require_pending(private_receipt)?;
        let allocation = self.allocation(private_receipt)?;
        let target = allocation.selected_member().character_cell;
        let mut gate = allocation.consequence_gate();
        let post_state = std::cell::Cell::new(None::<[u8; 32]>);
        let consequence = gate.recover_committed_game_turn(
            session,
            private_receipt,
            target,
            |id, observed_target, tag| {
                let observation = observe(id, observed_target, tag)?;
                if let Some(committed) = observation.as_ref() {
                    post_state.set(Some(committed.game_receipt().post_state_hash));
                }
                Ok(observation)
            },
        )?;
        let game_state_root = post_state
            .get()
            .ok_or(PrivateBazaarJourneyError::MissingGameStateRoot)?;
        Ok(self.install_settled(consequence, game_state_root))
    }

    fn require_pending(
        &self,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
    ) -> Result<(), PrivateBazaarJourneyError> {
        match self.receipt.as_ref().map(|receipt| receipt.phase) {
            None => return Err(PrivateBazaarJourneyError::SettlementBeforeEnter),
            Some(PrivateBazaarPublicPhase::Settled) => {
                return Err(PrivateBazaarJourneyError::SettlementAlreadyApplied);
            }
            Some(PrivateBazaarPublicPhase::Pending) => {}
        }
        if private_receipt.statement.session != self.market_session {
            return Err(PrivateBazaarJourneyError::MarketNotReady);
        }
        Ok(())
    }

    fn allocation(
        &self,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
    ) -> Result<
        crate::private_clearing_guild_allocation::PrivateClearingGuildAllocation,
        PrivateBazaarJourneyError,
    > {
        let source = crate::private_clearing_consequence::PrivateClearingConsequenceSource::from_verified_receipt(private_receipt)?;
        Ok(
            crate::private_clearing_guild_allocation::PrivateClearingGuildAllocation::new(
                source,
                self.roster.clone(),
                self.roster.digest(),
                self.reward.clone(),
            )?,
        )
    }

    fn install_settled(
        &mut self,
        consequence: crate::private_clearing_consequence::PrivateClearingConsequenceReceipt,
        game_state_root: [u8; 32],
    ) -> &PrivateBazaarPublicReceipt {
        let (journey_id, participant_count, roster_commitment, reward_commitment) = {
            let pending = self.receipt.as_ref().expect("checked pending");
            (
                pending.journey_id,
                pending.participant_count,
                pending.roster_commitment,
                pending.reward_commitment,
            )
        };
        self.receipt = Some(PrivateBazaarPublicReceipt {
            journey_id,
            phase: PrivateBazaarPublicPhase::Settled,
            participant_count,
            roster_commitment,
            reward_commitment,
            proof_session: Some(consequence.private_session),
            input_root: Some(consequence.private_root),
            consequence_id: Some(consequence.consequence_id),
            settlement_turn_hash: Some(consequence.settlement_turn_hash),
            game_turn_hash: Some(consequence.game_turn_hash),
            game_state_root: Some(game_state_root),
        });
        self.receipt.as_ref().expect("settled receipt installed")
    }
}

fn hex32(bytes: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn hex_felts(felts: [u32; 8]) -> String {
    felts
        .into_iter()
        .map(|felt| format!("{felt:08x}"))
        .collect::<String>()
}

fn short_hex(bytes: [u8; 32]) -> String {
    format!("{}…", &hex32(bytes)[..16])
}

fn short_felts(felts: [u32; 8]) -> String {
    format!("{}…", &hex_felts(felts)[..16])
}

#[cfg(feature = "private-clearing")]
fn reward_commitment(kind: &str, amount: u64) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(REWARD_DOMAIN)
        .update(&(kind.len() as u64).to_be_bytes())
        .update(kind.as_bytes())
        .update(&amount.to_be_bytes())
        .finalize()
        .as_bytes()
}

#[cfg(feature = "private-clearing")]
fn journey_id(
    market_session: u32,
    roster_commitment: [u8; 32],
    reward_commitment: [u8; 32],
    participant_count: u32,
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(JOURNEY_DOMAIN)
        .update(&market_session.to_be_bytes())
        .update(&roster_commitment)
        .update(&reward_commitment)
        .update(&participant_count.to_be_bytes())
        .finalize()
        .as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_action_grammar_has_no_secret_payload_lane() {
        for semantic in [
            PrivateBazaarPublicAction::Enter,
            PrivateBazaarPublicAction::Refresh,
        ] {
            let action = semantic.offering_action();
            assert_eq!(
                PrivateBazaarPublicAction::from_offering_action(&action),
                Ok(semantic)
            );
            assert_eq!(action.arg, 0);
            assert!(action.text.is_none());
            assert!(!action.wants_text);
        }

        let with_number = Action::new("enter", TURN_ENTER_PRIVATE_BAZAAR, 7, true);
        assert_eq!(
            PrivateBazaarPublicAction::from_offering_action(&with_number),
            Err(PrivateBazaarJourneyError::PublicActionCarriesPayload)
        );
        let with_bytes = Action::new("enter", TURN_ENTER_PRIVATE_BAZAAR, 0, true)
            .with_text("private bid or witness");
        assert_eq!(
            PrivateBazaarPublicAction::from_offering_action(&with_bytes),
            Err(PrivateBazaarJourneyError::PublicActionCarriesPayload)
        );
    }

    #[test]
    fn pending_receipt_is_one_viewer_blind_surface_and_allowlisted_fields() {
        let receipt = PrivateBazaarPublicReceipt::pending([1; 32], 4, [2; 32], [3; 32]);
        let surface = format!("{:?}", receipt.surface().view());
        let fields = receipt.public_fields();
        assert!(surface.contains("pending"));
        assert!(!surface.contains("winner"));
        assert!(!surface.contains("price"));
        assert!(!surface.contains("bid"));
        assert!(fields.iter().all(|(name, _)| !matches!(
            name.as_str(),
            "winner" | "price" | "reserve" | "actor" | "proofBytes" | "witness"
        )));
    }
}
