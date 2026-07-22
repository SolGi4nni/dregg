//! Viewer-blind public journey for a private Dark Bazaar game consequence.
//!
//! This module is deliberately presentation and deployment policy, not an
//! alternate authorization system.  A player can only submit the fixed,
//! payload-free `enter` and `refresh` actions.  The server binds that public
//! shell to:
//!
//! * a full market-instance digest (deployment, listing cell, seller, reserve,
//!   deterministic seed), rather than the relation's 32-bit field element;
//! * a deployment-owned roster and reward pin loaded independently from the
//!   runtime values; and
//! * a structural pending-or-settled receipt whose constructors are private.
//!
//! The sibling `private_bazaar_authority` module owns prepare-before-dispatch,
//! durable source-use reservation, executor receipt/finality verification, and
//! minting the opaque committed-effect authority.  A public receipt is never an
//! authorization capability.

#[cfg(feature = "private-clearing")]
use std::collections::{BTreeMap, BTreeSet};

use deos_view::ViewNode;
use dreggnet_offerings::{Action, Surface};

pub const TURN_ENTER_PRIVATE_BAZAAR: &str = "enter-private-bazaar";
pub const TURN_REFRESH_PRIVATE_BAZAAR: &str = "refresh-private-bazaar";

#[cfg(any(feature = "private-clearing", test))]
const JOURNEY_DOMAIN: &str = "dreggnet-market/private-bazaar-player-journey/v2";
const PUBLIC_RECEIPT_DOMAIN: &str = "dreggnet-market/private-bazaar-public-receipt/v1";
#[cfg(feature = "private-clearing")]
// v3 names the logical replay-stable listing, not the embedded executor's
// ephemeral agent key or the physical auction cell derived from that key.
// `SessionConfig::seed` is the listing nonce at this application boundary.
const MARKET_INSTANCE_DOMAIN: &str = "dreggnet-market/private-bazaar-market-instance/v3";
#[cfg(feature = "private-clearing")]
const POLICY_DOMAIN: &str = "dreggnet-market/private-bazaar-deployment-policy/v1";
#[cfg(feature = "private-clearing")]
const REWARD_DOMAIN: &str = "dreggnet-market/private-bazaar-public-reward/v2";
#[cfg(feature = "private-clearing")]
const PROGRESSION_GENESIS_DOMAIN: &str =
    "dreggnet-market/private-bazaar-raid-progression-genesis/v1";
#[cfg(feature = "private-clearing")]
const PROGRESSION_RECEIPT_DOMAIN: &str =
    "dreggnet-market/private-bazaar-raid-progression-receipt/v1";

/// Frontend-neutral operation name for a viewer-blind raid progression receipt.
///
/// The current private/proven raid is not yet mounted in the catalog's common
/// `GameSessionRef` classifier.  This stable name and
/// [`PrivateBazaarProgressionAdapterPayload`] are the engine-side handoff for
/// that later mount; they do not claim the mount already exists.
#[cfg(feature = "private-clearing")]
pub const PRIVATE_BAZAAR_PROGRESSION_OPERATION: &str = "private-bazaar.raid-progression.v1";

/// Complete public action vocabulary.  Neither action can transport a bid,
/// witness, identity, proof, target, reward, or arbitrary bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBazaarPublicAction {
    Enter,
    Refresh,
}

impl PrivateBazaarPublicAction {
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

/// Fields common to both receipt variants.  All fields are private so callers
/// cannot manufacture a contradictory phase/field combination with a struct
/// literal.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PrivateBazaarPublicContext {
    journey_id: [u8; 32],
    deployment_id: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    participant_count: u32,
    roster_commitment: [u8; 32],
    reward_commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarPendingReceipt {
    context: PrivateBazaarPublicContext,
}

/// A settled receipt cannot exist without every committed field.  This removes
/// the earlier public `{ phase, Option<_>, ... }` shape in which a caller could
/// construct `Settled` with missing evidence (or `Pending` with landed hashes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarSettledReceipt {
    context: PrivateBazaarPublicContext,
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    proof_session: u32,
    input_root: [u32; 8],
    settlement_turn_hash: [u8; 32],
    game_receipt_hash: [u8; 32],
    game_turn_hash: [u8; 32],
    game_post_state: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBazaarPublicReceipt {
    Pending(PrivateBazaarPendingReceipt),
    Settled(PrivateBazaarSettledReceipt),
}

impl PrivateBazaarPublicReceipt {
    #[cfg(any(feature = "private-clearing", test))]
    fn pending(context: PrivateBazaarPublicContext) -> Self {
        Self::Pending(PrivateBazaarPendingReceipt { context })
    }

    #[cfg(any(feature = "private-clearing", test))]
    #[allow(clippy::too_many_arguments)]
    fn settled(
        context: PrivateBazaarPublicContext,
        source_use_id: [u8; 32],
        operation_id: [u8; 32],
        proof_session: u32,
        input_root: [u32; 8],
        settlement_turn_hash: [u8; 32],
        game_receipt_hash: [u8; 32],
        game_turn_hash: [u8; 32],
        game_post_state: [u8; 32],
    ) -> Result<Self, PrivateBazaarJourneyError> {
        if [
            source_use_id,
            operation_id,
            settlement_turn_hash,
            game_receipt_hash,
            game_turn_hash,
            game_post_state,
        ]
        .contains(&[0; 32])
            || input_root == [0; 8]
        {
            return Err(PrivateBazaarJourneyError::InvalidCommittedAuthority);
        }
        Ok(Self::Settled(PrivateBazaarSettledReceipt {
            context,
            source_use_id,
            operation_id,
            proof_session,
            input_root,
            settlement_turn_hash,
            game_receipt_hash,
            game_turn_hash,
            game_post_state,
        }))
    }

    fn context(&self) -> &PrivateBazaarPublicContext {
        match self {
            Self::Pending(receipt) => &receipt.context,
            Self::Settled(receipt) => &receipt.context,
        }
    }

    pub const fn phase(&self) -> PrivateBazaarPublicPhase {
        match self {
            Self::Pending(_) => PrivateBazaarPublicPhase::Pending,
            Self::Settled(_) => PrivateBazaarPublicPhase::Settled,
        }
    }

    pub fn journey_id(&self) -> [u8; 32] {
        self.context().journey_id
    }

    /// Deployment identity bound by the independently loaded raid policy.
    pub fn deployment_id(&self) -> [u8; 32] {
        self.context().deployment_id
    }

    pub fn market_instance_id(&self) -> [u8; 32] {
        self.context().market_instance_id
    }

    pub fn policy_id(&self) -> [u8; 32] {
        self.context().policy_id
    }

    pub fn participant_count(&self) -> u32 {
        self.context().participant_count
    }

    pub fn roster_commitment(&self) -> [u8; 32] {
        self.context().roster_commitment
    }

    pub fn reward_commitment(&self) -> [u8; 32] {
        self.context().reward_commitment
    }

    pub fn source_use_id(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.source_use_id),
        }
    }

    pub fn operation_id(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.operation_id),
        }
    }

    pub fn proof_session(&self) -> Option<u32> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.proof_session),
        }
    }

    pub fn input_root(&self) -> Option<[u32; 8]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.input_root),
        }
    }

    pub fn settlement_turn_hash(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.settlement_turn_hash),
        }
    }

    pub fn game_receipt_hash(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.game_receipt_hash),
        }
    }

    pub fn game_post_state(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.game_post_state),
        }
    }

    pub fn game_turn_hash(&self) -> Option<[u8; 32]> {
        match self {
            Self::Pending(_) => None,
            Self::Settled(receipt) => Some(receipt.game_turn_hash),
        }
    }

    /// Commitment to this exact structural pending or settled receipt.
    ///
    /// This is a portable integrity/linking identity, not authorization to
    /// replay the private market result or its game consequence.
    pub fn receipt_id(&self) -> [u8; 32] {
        public_receipt_id(self)
    }

    pub fn public_fields(&self) -> Vec<(String, String)> {
        let context = self.context();
        let mut fields = vec![
            ("phase".to_owned(), self.phase().as_str().to_owned()),
            (
                "participant".to_owned(),
                context.participant_count.to_string(),
            ),
            ("requestDigest".to_owned(), hex32(context.journey_id)),
            (
                "marketInstanceDigest".to_owned(),
                hex32(context.market_instance_id),
            ),
            ("policyDigest".to_owned(), hex32(context.policy_id)),
            (
                "decisionBundleDigest".to_owned(),
                hex32(context.roster_commitment),
            ),
            (
                "decisionClaimDigest".to_owned(),
                hex32(context.reward_commitment),
            ),
            ("receiptDigest".to_owned(), hex32(self.receipt_id())),
        ];
        if let Self::Settled(receipt) = self {
            fields.extend([
                ("sourceUseDigest".to_owned(), hex32(receipt.source_use_id)),
                ("statementDigest".to_owned(), hex32(receipt.operation_id)),
                ("proofSession".to_owned(), receipt.proof_session.to_string()),
                ("inputRoot".to_owned(), hex_felts(receipt.input_root)),
                (
                    "proofDigest".to_owned(),
                    hex32(receipt.settlement_turn_hash),
                ),
                ("outcome".to_owned(), hex32(receipt.game_receipt_hash)),
                ("gameTurnDigest".to_owned(), hex32(receipt.game_turn_hash)),
                ("newRoot".to_owned(), hex32(receipt.game_post_state)),
            ]);
        }
        fields
    }

    pub fn surface(&self) -> Surface {
        let context = self.context();
        let state = match self {
            Self::Pending(_) => vec![
                ViewNode::Text(
                    "The party entered. Private inputs remain with their owning protocol while the executor receipt is pending."
                        .to_owned(),
                ),
                ViewNode::Text(format!(
                    "{} committed participants · roster {} · reward {}",
                    context.participant_count,
                    short_hex(context.roster_commitment),
                    short_hex(context.reward_commitment),
                )),
            ],
            Self::Settled(receipt) => vec![
                ViewNode::Text(
                    "Settled: one finalized, executor-authenticated private result caused one exact game effect."
                        .to_owned(),
                ),
                ViewNode::Text(format!(
                    "source {} · operation {} · game state {}",
                    short_hex(receipt.source_use_id),
                    short_hex(receipt.operation_id),
                    short_hex(receipt.game_post_state),
                )),
            ],
        };
        Surface(ViewNode::Section {
            title: format!("Dark Bazaar raid · {}", self.phase().as_str()),
            tag: if self.phase() == PrivateBazaarPublicPhase::Settled {
                "good".to_owned()
            } else {
                "accent".to_owned()
            },
            children: vec![
                ViewNode::Text(format!("Public journey {}", short_hex(context.journey_id))),
                ViewNode::Text(format!("Receipt {}", short_hex(self.receipt_id()))),
                ViewNode::Section {
                    title: "Viewer-blind receipt".to_owned(),
                    tag: "muted".to_owned(),
                    children: state,
                },
            ],
        })
    }
}

/// The already-committed terminal core from which public raid progression may
/// be derived.
///
/// Callers cannot construct this type from public fields.  It is projected only
/// from the settled receipt installed after the private clearing verifier and
/// exact game-effect authority have agreed.  It remains a viewer-blind linking
/// object, not an authority to perform another game effect.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarCommittedTerminalCore {
    deployment_id: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    terminal_receipt_id: [u8; 32],
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    reward_commitment: [u8; 32],
    game_receipt_hash: [u8; 32],
    game_turn_hash: [u8; 32],
    game_post_state: [u8; 32],
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarCommittedTerminalCore {
    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }

    /// Logical private-market session identity.  It commits the deployment,
    /// listing seed, reserve, and seller without publishing those preimages.
    pub const fn market_instance_id(&self) -> [u8; 32] {
        self.market_instance_id
    }

    pub const fn policy_id(&self) -> [u8; 32] {
        self.policy_id
    }

    pub const fn terminal_receipt_id(&self) -> [u8; 32] {
        self.terminal_receipt_id
    }
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarPublicReceipt {
    /// Project a progression source only from a terminal committed receipt.
    pub fn committed_terminal_core(
        &self,
    ) -> Result<PrivateBazaarCommittedTerminalCore, PrivateBazaarProgressionError> {
        let Self::Settled(receipt) = self else {
            return Err(PrivateBazaarProgressionError::SourceNotSettled);
        };
        Ok(PrivateBazaarCommittedTerminalCore {
            deployment_id: receipt.context.deployment_id,
            market_instance_id: receipt.context.market_instance_id,
            policy_id: receipt.context.policy_id,
            terminal_receipt_id: self.receipt_id(),
            source_use_id: receipt.source_use_id,
            operation_id: receipt.operation_id,
            reward_commitment: receipt.context.reward_commitment,
            game_receipt_hash: receipt.game_receipt_hash,
            game_turn_hash: receipt.game_turn_hash,
            game_post_state: receipt.game_post_state,
        })
    }
}

/// Viewer-blind result of consuming one committed Bazaar terminal receipt into
/// a public raid objective.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarProgressionResult {
    sequence: u64,
    required: u64,
    complete: bool,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarProgressionResult {
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn required(&self) -> u64 {
        self.required
    }

    pub const fn complete(&self) -> bool {
        self.complete
    }
}

/// One exact state-machine receipt for viewer-blind raid progression.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarProgressionReceipt {
    deployment_id: [u8; 32],
    market_instance_id: [u8; 32],
    source_terminal_receipt_id: [u8; 32],
    predecessor_id: [u8; 32],
    progression_id: [u8; 32],
    result: PrivateBazaarProgressionResult,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarProgressionReceipt {
    pub const fn predecessor_id(&self) -> [u8; 32] {
        self.predecessor_id
    }

    pub const fn progression_id(&self) -> [u8; 32] {
        self.progression_id
    }

    pub const fn source_terminal_receipt_id(&self) -> [u8; 32] {
        self.source_terminal_receipt_id
    }

    pub const fn result(&self) -> PrivateBazaarProgressionResult {
        self.result
    }

    /// Exact, viewer-blind result carrier for a future common-game operation
    /// adapter.  It exposes no winner, actor, target, bid, price, reward value,
    /// private root, proof bytes, or game-state preimage.
    pub fn adapter_payload(&self) -> PrivateBazaarProgressionAdapterPayload {
        PrivateBazaarProgressionAdapterPayload {
            operation: PRIVATE_BAZAAR_PROGRESSION_OPERATION,
            receipt_id: self.progression_id,
            expected_predecessor: self.predecessor_id,
            public_fields: vec![
                ("sequence".to_owned(), self.result.sequence.to_string()),
                ("ended".to_owned(), self.result.complete.to_string()),
                (
                    "requestDigest".to_owned(),
                    hex32(self.source_terminal_receipt_id),
                ),
                ("statementDigest".to_owned(), hex32(self.progression_id)),
            ],
        }
    }

    pub fn surface(&self) -> Surface {
        Surface(ViewNode::Section {
            title: if self.result.complete {
                "Dark Bazaar raid objective · complete".to_owned()
            } else {
                "Dark Bazaar raid objective · advancing".to_owned()
            },
            tag: if self.result.complete {
                "good".to_owned()
            } else {
                "accent".to_owned()
            },
            children: vec![
                ViewNode::Text(format!(
                    "Verified private consequences {}/{}",
                    self.result.sequence, self.result.required
                )),
                ViewNode::Text(format!(
                    "Progress receipt {} · source {}",
                    short_hex(self.progression_id),
                    short_hex(self.source_terminal_receipt_id)
                )),
            ],
        })
    }

    /// Recompute the complete progression binding against its committed
    /// terminal source.  This checks receipt integrity only; it does not
    /// authorize another private clearing or game effect.
    pub fn binding_verifies(
        &self,
        objective_id: [u8; 32],
        policy_id: [u8; 32],
        terminal: &PrivateBazaarCommittedTerminalCore,
    ) -> bool {
        self.deployment_id == terminal.deployment_id
            && self.market_instance_id == terminal.market_instance_id
            && self.source_terminal_receipt_id == terminal.terminal_receipt_id
            && self.progression_id
                == progression_receipt_id(
                    objective_id,
                    policy_id,
                    self.predecessor_id,
                    terminal,
                    self.result,
                )
    }
}

/// An explicit engine-to-adapter payload for eventual common-spine
/// classification.
///
/// The fields intentionally match the existing public-game scalar/digest
/// grammar, but no claim is made that `private-bazaar-raid` is already a
/// `GameSessionRef` route.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarProgressionAdapterPayload {
    operation: &'static str,
    receipt_id: [u8; 32],
    expected_predecessor: [u8; 32],
    public_fields: Vec<(String, String)>,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarProgressionAdapterPayload {
    pub const fn operation(&self) -> &'static str {
        self.operation
    }

    pub const fn receipt_id(&self) -> [u8; 32] {
        self.receipt_id
    }

    pub const fn expected_predecessor(&self) -> [u8; 32] {
        self.expected_predecessor
    }

    pub fn public_fields(&self) -> &[(String, String)] {
        &self.public_fields
    }
}

/// A small receipt-derived raid objective.  Each logical private-market
/// session may advance it once, only at the exact observed predecessor.
///
/// This state machine does not perform or authorize a market/game effect.  It
/// consumes the already committed terminal receipt as evidence for a public,
/// viewer-blind consequence counter.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug)]
pub struct PrivateBazaarRaidProgression {
    deployment_id: [u8; 32],
    policy_id: [u8; 32],
    objective_id: [u8; 32],
    required: u64,
    sequence: u64,
    head: [u8; 32],
    terminal_by_session: BTreeMap<[u8; 32], [u8; 32]>,
    consumed_source_uses: BTreeSet<[u8; 32]>,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarRaidProgression {
    pub fn new(
        deployment_id: [u8; 32],
        policy_id: [u8; 32],
        objective_id: [u8; 32],
        required: u64,
    ) -> Result<Self, PrivateBazaarProgressionError> {
        if deployment_id == [0; 32] || policy_id == [0; 32] || objective_id == [0; 32] {
            return Err(PrivateBazaarProgressionError::InvalidConfiguration(
                "deployment, policy, and objective ids must be nonzero",
            ));
        }
        if required == 0 {
            return Err(PrivateBazaarProgressionError::InvalidConfiguration(
                "required terminal receipt count must be positive",
            ));
        }
        let head = progression_genesis_id(deployment_id, policy_id, objective_id, required);
        Ok(Self {
            deployment_id,
            policy_id,
            objective_id,
            required,
            sequence: 0,
            head,
            terminal_by_session: BTreeMap::new(),
            consumed_source_uses: BTreeSet::new(),
        })
    }

    pub const fn head(&self) -> [u8; 32] {
        self.head
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn complete(&self) -> bool {
        self.sequence == self.required
    }

    /// Advance exactly once from `expected_predecessor` using one committed
    /// viewer-blind terminal receipt.
    pub fn advance(
        &mut self,
        expected_predecessor: [u8; 32],
        receipt: &PrivateBazaarPublicReceipt,
    ) -> Result<PrivateBazaarProgressionReceipt, PrivateBazaarProgressionError> {
        let terminal = receipt.committed_terminal_core()?;
        if terminal.deployment_id != self.deployment_id {
            return Err(PrivateBazaarProgressionError::WrongDeployment);
        }
        if terminal.policy_id != self.policy_id {
            return Err(PrivateBazaarProgressionError::WrongPolicy);
        }
        if expected_predecessor != self.head {
            return Err(PrivateBazaarProgressionError::PredecessorMismatch);
        }
        if let Some(previous) = self.terminal_by_session.get(&terminal.market_instance_id) {
            return Err(if previous == &terminal.terminal_receipt_id {
                PrivateBazaarProgressionError::ReceiptReplay
            } else {
                PrivateBazaarProgressionError::SessionFork
            });
        }
        if self.consumed_source_uses.contains(&terminal.source_use_id) {
            return Err(PrivateBazaarProgressionError::SourceUseReplay);
        }
        if self.complete() {
            return Err(PrivateBazaarProgressionError::ObjectiveAlreadyComplete);
        }
        let sequence = self
            .sequence
            .checked_add(1)
            .ok_or(PrivateBazaarProgressionError::SequenceOverflow)?;
        let result = PrivateBazaarProgressionResult {
            sequence,
            required: self.required,
            complete: sequence == self.required,
        };
        let progression_id = progression_receipt_id(
            self.objective_id,
            self.policy_id,
            expected_predecessor,
            &terminal,
            result,
        );
        let progressed = PrivateBazaarProgressionReceipt {
            deployment_id: self.deployment_id,
            market_instance_id: terminal.market_instance_id,
            source_terminal_receipt_id: terminal.terminal_receipt_id,
            predecessor_id: expected_predecessor,
            progression_id,
            result,
        };
        debug_assert!(progressed.binding_verifies(self.objective_id, self.policy_id, &terminal));

        self.terminal_by_session
            .insert(terminal.market_instance_id, terminal.terminal_receipt_id);
        self.consumed_source_uses.insert(terminal.source_use_id);
        self.sequence = sequence;
        self.head = progression_id;
        Ok(progressed)
    }
}

#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBazaarProgressionError {
    SourceNotSettled,
    InvalidConfiguration(&'static str),
    WrongDeployment,
    WrongPolicy,
    PredecessorMismatch,
    ReceiptReplay,
    SessionFork,
    SourceUseReplay,
    ObjectiveAlreadyComplete,
    SequenceOverflow,
}

#[cfg(feature = "private-clearing")]
impl std::fmt::Display for PrivateBazaarProgressionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar raid progression refused: {self:?}")
    }
}

#[cfg(feature = "private-clearing")]
impl std::error::Error for PrivateBazaarProgressionError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBazaarJourneyError {
    UnknownPublicAction,
    PublicActionCarriesPayload,
    EnterAlreadySubmitted,
    RefreshBeforeEnter,
    SettlementBeforeEnter,
    SettlementAlreadyApplied,
    MarketNotReady,
    InvalidDeploymentPin(&'static str),
    RosterPinMismatch,
    RewardPinMismatch,
    MarketInstanceMismatch,
    InvalidCommittedAuthority,
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
impl From<crate::private_clearing_guild_allocation::PrivateClearingGuildAllocationError>
    for PrivateBazaarJourneyError
{
    fn from(
        error: crate::private_clearing_guild_allocation::PrivateClearingGuildAllocationError,
    ) -> Self {
        Self::Allocation(error)
    }
}

/// Immutable values loaded from deployment configuration before a runtime
/// roster/reward object is accepted.  A request cannot choose these values.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarDeploymentPin {
    deployment_id: [u8; 32],
    expected_roster_commitment: [u8; 32],
    expected_reward_commitment: [u8; 32],
    reward_method: String,
    reward_event_topic: [u8; 32],
    executor_pubkey: [u8; 32],
    executor_federation: [u8; 32],
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarDeploymentPin {
    pub fn new(
        deployment_id: [u8; 32],
        expected_roster_commitment: [u8; 32],
        expected_reward_commitment: [u8; 32],
        reward_method: impl Into<String>,
        reward_event_topic: [u8; 32],
        executor_pubkey: [u8; 32],
        executor_federation: [u8; 32],
    ) -> Result<Self, PrivateBazaarJourneyError> {
        let reward_method = reward_method.into();
        if deployment_id == [0; 32] {
            return Err(PrivateBazaarJourneyError::InvalidDeploymentPin(
                "zero deployment id",
            ));
        }
        if expected_roster_commitment == [0; 32] || expected_reward_commitment == [0; 32] {
            return Err(PrivateBazaarJourneyError::InvalidDeploymentPin(
                "zero policy commitment",
            ));
        }
        if reward_method.is_empty() || reward_method.len() > 256 || reward_event_topic == [0; 32] {
            return Err(PrivateBazaarJourneyError::InvalidDeploymentPin(
                "invalid reward method or event topic",
            ));
        }
        if executor_pubkey == [0; 32] || executor_federation == [0; 32] {
            return Err(PrivateBazaarJourneyError::InvalidDeploymentPin(
                "zero executor authority",
            ));
        }
        Ok(Self {
            deployment_id,
            expected_roster_commitment,
            expected_reward_commitment,
            reward_method,
            reward_event_topic,
            executor_pubkey,
            executor_federation,
        })
    }

    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }

    pub const fn expected_roster_commitment(&self) -> [u8; 32] {
        self.expected_roster_commitment
    }

    pub const fn expected_reward_commitment(&self) -> [u8; 32] {
        self.expected_reward_commitment
    }

    pub fn reward_method(&self) -> &str {
        &self.reward_method
    }

    pub const fn reward_event_topic(&self) -> [u8; 32] {
        self.reward_event_topic
    }

    pub const fn executor_pubkey(&self) -> [u8; 32] {
        self.executor_pubkey
    }

    pub const fn executor_federation(&self) -> [u8; 32] {
        self.executor_federation
    }
}

/// Runtime policy only after its roster and reward independently match the
/// deployment pins.  The journey accepts this opaque validated object, never a
/// caller-supplied `(value, expected_digest_of_that_same_value)` pair.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Debug)]
pub struct PrivateBazaarRaidPolicy {
    pin: PrivateBazaarDeploymentPin,
    roster: crate::private_clearing_guild_allocation::GuildRoster,
    reward: crate::private_clearing_guild_allocation::GuildReward,
    policy_id: [u8; 32],
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarRaidPolicy {
    pub fn load(
        pin: PrivateBazaarDeploymentPin,
        roster: crate::private_clearing_guild_allocation::GuildRoster,
        reward: crate::private_clearing_guild_allocation::GuildReward,
    ) -> Result<Self, PrivateBazaarJourneyError> {
        if roster.digest() != pin.expected_roster_commitment {
            return Err(PrivateBazaarJourneyError::RosterPinMismatch);
        }
        if reward_commitment(&reward.kind, reward.amount) != pin.expected_reward_commitment {
            return Err(PrivateBazaarJourneyError::RewardPinMismatch);
        }
        let policy_id = policy_id(&pin);
        Ok(Self {
            pin,
            roster,
            reward,
            policy_id,
        })
    }

    pub const fn policy_id(&self) -> [u8; 32] {
        self.policy_id
    }

    pub fn roster(&self) -> &crate::private_clearing_guild_allocation::GuildRoster {
        &self.roster
    }

    pub fn reward(&self) -> &crate::private_clearing_guild_allocation::GuildReward {
        &self.reward
    }

    pub fn pin(&self) -> &PrivateBazaarDeploymentPin {
        &self.pin
    }

    pub(crate) fn allocation_for_verified_receipt(
        &self,
        receipt: &crate::private_clearing::PrivateClearingReceipt,
    ) -> Result<
        crate::private_clearing_guild_allocation::PrivateClearingGuildAllocation,
        PrivateBazaarJourneyError,
    > {
        let source = crate::private_clearing_consequence::PrivateClearingConsequenceSource::from_verified_receipt(receipt)
            .map_err(|_| PrivateBazaarJourneyError::InvalidCommittedAuthority)?;
        Ok(
            crate::private_clearing_guild_allocation::PrivateClearingGuildAllocation::new(
                source,
                self.roster.clone(),
                self.pin.expected_roster_commitment,
                self.reward.clone(),
            )?,
        )
    }

    /// Worker-only routing helper for an out-of-band verified private receipt.
    /// It reveals no winner and returns only the policy-pinned target cell that
    /// the concrete game adapter will independently revalidate before dispatch.
    /// Public frontends never receive the raw receipt required to call it.
    pub fn worker_target_cell_for_verified_receipt(
        &self,
        receipt: &crate::private_clearing::PrivateClearingReceipt,
    ) -> Result<dregg_types::CellId, PrivateBazaarJourneyError> {
        Ok(self
            .allocation_for_verified_receipt(receipt)?
            .selected_member()
            .character_cell)
    }

    /// Offline/deployment tooling helper. Runtime code should load the returned
    /// digest from independent configuration, not recompute it from a request.
    pub fn reward_commitment_for_configuration(
        reward: &crate::private_clearing_guild_allocation::GuildReward,
    ) -> [u8; 32] {
        reward_commitment(&reward.kind, reward.amount)
    }
}

/// Full stable identity of one market listing under one deployment.
#[cfg(feature = "private-clearing")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarMarketIdentity {
    digest: [u8; 32],
    proof_session: u32,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarMarketIdentity {
    pub(crate) fn from_session(
        session: &crate::DarkBazaarSession,
        deployment_id: [u8; 32],
    ) -> Result<Self, PrivateBazaarJourneyError> {
        let market = &session.market;
        market
            .auction_cell
            .ok_or(PrivateBazaarJourneyError::MarketNotReady)?;
        let seller = market
            .seller
            .as_ref()
            .ok_or(PrivateBazaarJourneyError::MarketNotReady)?;
        let mut hasher = blake3::Hasher::new_derive_key(MARKET_INSTANCE_DOMAIN);
        hasher.update(&deployment_id);
        hasher.update(&market.seed.to_be_bytes());
        hasher.update(&market.reserve.to_be_bytes());
        hasher.update(&(seller.0.len() as u64).to_be_bytes());
        hasher.update(seller.0.as_bytes());
        Ok(Self {
            digest: *hasher.finalize().as_bytes(),
            proof_session: session.private_proof_session(),
        })
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub const fn proof_session(&self) -> u32 {
        self.proof_session
    }
}

/// Per-host public shell. Exactly-once authority is intentionally not stored in
/// this object; all journey instances converge on the sibling durable authority
/// store by full source/operation id.
#[cfg(feature = "private-clearing")]
pub struct PrivateBazaarRaidJourney {
    market: PrivateBazaarMarketIdentity,
    policy: PrivateBazaarRaidPolicy,
    context: PrivateBazaarPublicContext,
    receipt: Option<PrivateBazaarPublicReceipt>,
}

#[cfg(feature = "private-clearing")]
impl PrivateBazaarRaidJourney {
    pub fn new(
        session: &crate::DarkBazaarSession,
        policy: PrivateBazaarRaidPolicy,
    ) -> Result<Self, PrivateBazaarJourneyError> {
        if !session.is_listed() || session.is_settled() {
            return Err(PrivateBazaarJourneyError::MarketNotReady);
        }
        let market = PrivateBazaarMarketIdentity::from_session(session, policy.pin.deployment_id)?;
        let participant_count = u32::try_from(policy.roster.ordered_members().len())
            .map_err(|_| PrivateBazaarJourneyError::InvalidDeploymentPin("roster length"))?;
        let journey_id = journey_id(market.digest, policy.policy_id, participant_count);
        let context = PrivateBazaarPublicContext {
            journey_id,
            deployment_id: policy.pin.deployment_id,
            market_instance_id: market.digest,
            policy_id: policy.policy_id,
            participant_count,
            roster_commitment: policy.pin.expected_roster_commitment,
            reward_commitment: policy.pin.expected_reward_commitment,
        };
        Ok(Self {
            market,
            policy,
            context,
            receipt: None,
        })
    }

    pub fn actions(&self) -> Vec<Action> {
        if self.receipt.is_none() {
            vec![PrivateBazaarPublicAction::Enter.offering_action()]
        } else {
            // Refresh is a read-controller verb. OfferingHost advances are
            // journaled mutations and must not fabricate a receipt for a read.
            Vec::new()
        }
    }

    pub fn receipt(&self) -> Option<&PrivateBazaarPublicReceipt> {
        self.receipt.as_ref()
    }

    pub fn market_identity(&self) -> PrivateBazaarMarketIdentity {
        self.market
    }

    pub fn policy(&self) -> &PrivateBazaarRaidPolicy {
        &self.policy
    }

    pub fn advance_public(
        &mut self,
        action: &Action,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError> {
        match PrivateBazaarPublicAction::from_offering_action(action)? {
            PrivateBazaarPublicAction::Enter => {
                if self.receipt.is_some() {
                    return Err(PrivateBazaarJourneyError::EnterAlreadySubmitted);
                }
                self.receipt = Some(PrivateBazaarPublicReceipt::pending(self.context.clone()));
            }
            PrivateBazaarPublicAction::Refresh => {
                if self.receipt.is_none() {
                    return Err(PrivateBazaarJourneyError::RefreshBeforeEnter);
                }
            }
        }
        Ok(self.receipt.as_ref().expect("enter or existing receipt"))
    }

    pub(crate) fn require_pending(
        &self,
        session: &crate::DarkBazaarSession,
    ) -> Result<(), PrivateBazaarJourneyError> {
        match self.receipt.as_ref().map(PrivateBazaarPublicReceipt::phase) {
            None => return Err(PrivateBazaarJourneyError::SettlementBeforeEnter),
            Some(PrivateBazaarPublicPhase::Settled) => {
                return Err(PrivateBazaarJourneyError::SettlementAlreadyApplied);
            }
            Some(PrivateBazaarPublicPhase::Pending) => {}
        }
        let live =
            PrivateBazaarMarketIdentity::from_session(session, self.policy.pin.deployment_id)?;
        if live != self.market {
            return Err(PrivateBazaarJourneyError::MarketInstanceMismatch);
        }
        Ok(())
    }

    /// Publish one terminal viewer-blind receipt only after the durable store
    /// has produced an opaque committed exact-effect authority.  Rejoining both
    /// opaque values to the live market, private receipt, full market instance,
    /// and deployment policy prevents a public caller from relabeling another
    /// turn or constructing a settled receipt directly.
    pub fn install_committed(
        &mut self,
        session: &crate::DarkBazaarSession,
        private_receipt: &crate::private_clearing::PrivateClearingReceipt,
        authority: &crate::private_bazaar_authority::PrivateBazaarExecutorAuthority,
        committed: &crate::private_bazaar_authority::CommittedPrivateBazaarEffect,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError> {
        self.require_pending(session)?;
        if !authority.matches_source(session, private_receipt, self.market, &self.policy)
            || !committed.matches_authority(authority)
            || authority.market_instance_id() != self.market.digest
            || authority.policy_id() != self.policy.policy_id
            || committed.effect().reward_kind() != self.policy.reward.kind
            || committed.effect().reward_amount() != self.policy.reward.amount
        {
            return Err(PrivateBazaarJourneyError::InvalidCommittedAuthority);
        }
        let receipt = PrivateBazaarPublicReceipt::settled(
            self.context.clone(),
            committed.source_use_id(),
            committed.operation_id(),
            private_receipt.statement.session,
            private_receipt.statement.order_root,
            private_receipt.settlement_turn.turn_hash,
            committed.game_receipt_hash(),
            committed.game_turn_hash(),
            committed.game_post_state(),
        )?;
        self.install_settled(receipt)
    }

    fn install_settled(
        &mut self,
        receipt: PrivateBazaarPublicReceipt,
    ) -> Result<&PrivateBazaarPublicReceipt, PrivateBazaarJourneyError> {
        self.require_pending_context()?;
        if receipt.phase() != PrivateBazaarPublicPhase::Settled
            || receipt.context() != &self.context
        {
            return Err(PrivateBazaarJourneyError::InvalidCommittedAuthority);
        }
        self.receipt = Some(receipt);
        Ok(self.receipt.as_ref().expect("settled receipt installed"))
    }

    fn require_pending_context(&self) -> Result<(), PrivateBazaarJourneyError> {
        match self.receipt.as_ref().map(PrivateBazaarPublicReceipt::phase) {
            None => Err(PrivateBazaarJourneyError::SettlementBeforeEnter),
            Some(PrivateBazaarPublicPhase::Pending) => Ok(()),
            Some(PrivateBazaarPublicPhase::Settled) => {
                Err(PrivateBazaarJourneyError::SettlementAlreadyApplied)
            }
        }
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
fn policy_id(pin: &PrivateBazaarDeploymentPin) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(POLICY_DOMAIN)
        .update(&pin.deployment_id)
        .update(&pin.expected_roster_commitment)
        .update(&pin.expected_reward_commitment)
        .update(&(pin.reward_method.len() as u64).to_be_bytes())
        .update(pin.reward_method.as_bytes())
        .update(&pin.reward_event_topic)
        .update(&pin.executor_pubkey)
        .update(&pin.executor_federation)
        .finalize()
        .as_bytes()
}

#[cfg(any(feature = "private-clearing", test))]
fn journey_id(
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    participant_count: u32,
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(JOURNEY_DOMAIN)
        .update(&market_instance_id)
        .update(&policy_id)
        .update(&participant_count.to_be_bytes())
        .finalize()
        .as_bytes()
}

fn public_receipt_id(receipt: &PrivateBazaarPublicReceipt) -> [u8; 32] {
    let context = receipt.context();
    let mut hasher = blake3::Hasher::new_derive_key(PUBLIC_RECEIPT_DOMAIN);
    hasher.update(&context.journey_id);
    hasher.update(&context.deployment_id);
    hasher.update(&context.market_instance_id);
    hasher.update(&context.policy_id);
    hasher.update(&context.participant_count.to_be_bytes());
    hasher.update(&context.roster_commitment);
    hasher.update(&context.reward_commitment);
    match receipt {
        PrivateBazaarPublicReceipt::Pending(_) => {
            hasher.update(&[0]);
        }
        PrivateBazaarPublicReceipt::Settled(settled) => {
            hasher.update(&[1]);
            hasher.update(&settled.source_use_id);
            hasher.update(&settled.operation_id);
            hasher.update(&settled.proof_session.to_be_bytes());
            for felt in settled.input_root {
                hasher.update(&felt.to_be_bytes());
            }
            hasher.update(&settled.settlement_turn_hash);
            hasher.update(&settled.game_receipt_hash);
            hasher.update(&settled.game_turn_hash);
            hasher.update(&settled.game_post_state);
        }
    }
    *hasher.finalize().as_bytes()
}

#[cfg(feature = "private-clearing")]
fn progression_genesis_id(
    deployment_id: [u8; 32],
    policy_id: [u8; 32],
    objective_id: [u8; 32],
    required: u64,
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(PROGRESSION_GENESIS_DOMAIN)
        .update(PRIVATE_BAZAAR_RAID_KEY_FOR_BINDING.as_bytes())
        .update(&deployment_id)
        .update(&policy_id)
        .update(&objective_id)
        .update(&required.to_be_bytes())
        .finalize()
        .as_bytes()
}

#[cfg(feature = "private-clearing")]
fn progression_receipt_id(
    objective_id: [u8; 32],
    policy_id: [u8; 32],
    predecessor_id: [u8; 32],
    terminal: &PrivateBazaarCommittedTerminalCore,
    result: PrivateBazaarProgressionResult,
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(PROGRESSION_RECEIPT_DOMAIN)
        .update(PRIVATE_BAZAAR_RAID_KEY_FOR_BINDING.as_bytes())
        .update(&terminal.deployment_id)
        .update(&terminal.market_instance_id)
        .update(&terminal.policy_id)
        .update(&policy_id)
        .update(&objective_id)
        .update(&terminal.terminal_receipt_id)
        .update(&terminal.source_use_id)
        .update(&terminal.operation_id)
        .update(&terminal.reward_commitment)
        .update(&terminal.game_receipt_hash)
        .update(&terminal.game_turn_hash)
        .update(&terminal.game_post_state)
        .update(&predecessor_id)
        .update(&result.sequence.to_be_bytes())
        .update(&result.required.to_be_bytes())
        .update(&[u8::from(result.complete)])
        .finalize()
        .as_bytes()
}

#[cfg(feature = "private-clearing")]
const PRIVATE_BAZAAR_RAID_KEY_FOR_BINDING: &str = "private-bazaar-raid";

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "private-clearing")]
    #[derive(Clone, Copy)]
    struct TerminalFixture {
        deployment: [u8; 32],
        market: [u8; 32],
        policy: [u8; 32],
        source_use: [u8; 32],
        operation: [u8; 32],
        game_receipt: [u8; 32],
        game_turn: [u8; 32],
        game_state: [u8; 32],
    }

    #[cfg(feature = "private-clearing")]
    impl TerminalFixture {
        fn receipt(self) -> PrivateBazaarPublicReceipt {
            let context = PrivateBazaarPublicContext {
                journey_id: [0x10; 32],
                deployment_id: self.deployment,
                market_instance_id: self.market,
                policy_id: self.policy,
                participant_count: 4,
                roster_commitment: [0x20; 32],
                reward_commitment: [0x21; 32],
            };
            PrivateBazaarPublicReceipt::settled(
                context,
                self.source_use,
                self.operation,
                17,
                [0x31; 8],
                [0x32; 32],
                self.game_receipt,
                self.game_turn,
                self.game_state,
            )
            .expect("nonzero committed terminal fixture")
        }
    }

    #[cfg(feature = "private-clearing")]
    fn terminal_fixture(market_byte: u8, source_byte: u8) -> TerminalFixture {
        TerminalFixture {
            deployment: [0x41; 32],
            market: [market_byte; 32],
            policy: [0x42; 32],
            source_use: [source_byte; 32],
            operation: [source_byte.wrapping_add(1); 32],
            game_receipt: [source_byte.wrapping_add(2); 32],
            game_turn: [source_byte.wrapping_add(3); 32],
            game_state: [source_byte.wrapping_add(4); 32],
        }
    }

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
    fn structural_pending_receipt_is_viewer_blind() {
        let context = PrivateBazaarPublicContext {
            journey_id: [1; 32],
            deployment_id: [7; 32],
            market_instance_id: [2; 32],
            policy_id: [3; 32],
            participant_count: 4,
            roster_commitment: [5; 32],
            reward_commitment: [6; 32],
        };
        let receipt = PrivateBazaarPublicReceipt::pending(context);
        assert_eq!(receipt.phase(), PrivateBazaarPublicPhase::Pending);
        assert!(receipt.source_use_id().is_none());
        assert!(receipt.game_receipt_hash().is_none());
        let surface = format!("{:?}", receipt.surface().view());
        assert!(!surface.contains("winner"));
        assert!(!surface.contains("price"));
        assert!(!surface.contains("bid"));
    }

    #[test]
    fn settled_constructor_rejects_missing_committed_fields() {
        let context = PrivateBazaarPublicContext {
            journey_id: [1; 32],
            deployment_id: [7; 32],
            market_instance_id: [2; 32],
            policy_id: [3; 32],
            participant_count: 4,
            roster_commitment: [5; 32],
            reward_commitment: [6; 32],
        };
        assert_eq!(
            PrivateBazaarPublicReceipt::settled(
                context, [0; 32], [8; 32], 9, [1; 8], [10; 32], [11; 32], [12; 32], [13; 32],
            ),
            Err(PrivateBazaarJourneyError::InvalidCommittedAuthority)
        );
    }

    #[cfg(feature = "private-clearing")]
    #[test]
    fn committed_receipts_advance_a_predecessor_bound_viewer_blind_objective() {
        let first = terminal_fixture(0x51, 0x61).receipt();
        let second = terminal_fixture(0x52, 0x71).receipt();
        let first_core = first
            .committed_terminal_core()
            .expect("settled receipt projects a terminal core");
        assert_eq!(first_core.deployment_id(), [0x41; 32]);
        assert_eq!(first_core.market_instance_id(), [0x51; 32]);
        assert_eq!(first_core.policy_id(), [0x42; 32]);
        assert_eq!(first_core.terminal_receipt_id(), first.receipt_id());

        let mut objective =
            PrivateBazaarRaidProgression::new([0x41; 32], [0x42; 32], [0x43; 32], 2)
                .expect("valid objective");
        let genesis = objective.head();
        let first_progress = objective
            .advance(genesis, &first)
            .expect("first committed result advances");
        assert_eq!(first_progress.predecessor_id(), genesis);
        assert_eq!(first_progress.result().sequence(), 1);
        assert_eq!(first_progress.result().required(), 2);
        assert!(!first_progress.result().complete());
        assert_eq!(objective.head(), first_progress.progression_id());

        let second_progress = objective
            .advance(objective.head(), &second)
            .expect("second distinct session completes");
        assert_eq!(second_progress.result().sequence(), 2);
        assert!(second_progress.result().complete());
        assert!(objective.complete());

        let payload = second_progress.adapter_payload();
        assert_eq!(payload.operation(), PRIVATE_BAZAAR_PROGRESSION_OPERATION);
        assert_eq!(payload.receipt_id(), second_progress.progression_id());
        assert_eq!(
            payload.expected_predecessor(),
            first_progress.progression_id()
        );
        assert_eq!(
            payload.public_fields(),
            &[
                ("sequence".to_owned(), "2".to_owned()),
                ("ended".to_owned(), "true".to_owned()),
                ("requestDigest".to_owned(), hex32(second.receipt_id()),),
                (
                    "statementDigest".to_owned(),
                    hex32(second_progress.progression_id()),
                ),
            ]
        );
    }

    #[cfg(feature = "private-clearing")]
    #[test]
    fn pending_replay_stale_predecessor_and_source_reuse_are_refused_without_progress() {
        let pending = PrivateBazaarPublicReceipt::pending(PrivateBazaarPublicContext {
            journey_id: [1; 32],
            deployment_id: [0x41; 32],
            market_instance_id: [0x51; 32],
            policy_id: [0x42; 32],
            participant_count: 4,
            roster_commitment: [5; 32],
            reward_commitment: [6; 32],
        });
        let mut objective =
            PrivateBazaarRaidProgression::new([0x41; 32], [0x42; 32], [0x43; 32], 3).unwrap();
        let genesis = objective.head();
        assert_eq!(
            objective.advance(genesis, &pending),
            Err(PrivateBazaarProgressionError::SourceNotSettled)
        );
        assert_eq!(objective.head(), genesis);

        let first = terminal_fixture(0x51, 0x61).receipt();
        let landed = objective.advance(genesis, &first).unwrap();
        let after_first = objective.head();
        assert_eq!(
            objective.advance(after_first, &first),
            Err(PrivateBazaarProgressionError::ReceiptReplay)
        );
        assert_eq!(objective.head(), after_first);
        assert_eq!(objective.sequence(), 1);

        let distinct = terminal_fixture(0x52, 0x71).receipt();
        assert_eq!(
            objective.advance(landed.predecessor_id(), &distinct),
            Err(PrivateBazaarProgressionError::PredecessorMismatch)
        );
        assert_eq!(objective.head(), after_first);

        let reused_source = TerminalFixture {
            source_use: [0x61; 32],
            ..terminal_fixture(0x53, 0x81)
        }
        .receipt();
        assert_eq!(
            objective.advance(after_first, &reused_source),
            Err(PrivateBazaarProgressionError::SourceUseReplay)
        );
        assert_eq!(objective.head(), after_first);
        assert_eq!(objective.sequence(), 1);
    }

    #[cfg(feature = "private-clearing")]
    #[test]
    fn same_session_fork_and_wrong_deployment_or_policy_are_refused() {
        let first = terminal_fixture(0x51, 0x61).receipt();
        let mut objective =
            PrivateBazaarRaidProgression::new([0x41; 32], [0x42; 32], [0x43; 32], 3).unwrap();
        objective.advance(objective.head(), &first).unwrap();
        let head = objective.head();

        let fork = terminal_fixture(0x51, 0x71).receipt();
        assert_ne!(fork.receipt_id(), first.receipt_id());
        assert_eq!(
            objective.advance(head, &fork),
            Err(PrivateBazaarProgressionError::SessionFork)
        );
        assert_eq!(objective.head(), head);

        let wrong_deployment = TerminalFixture {
            deployment: [0x91; 32],
            ..terminal_fixture(0x52, 0x81)
        }
        .receipt();
        assert_eq!(
            objective.advance(head, &wrong_deployment),
            Err(PrivateBazaarProgressionError::WrongDeployment)
        );

        let wrong_policy = TerminalFixture {
            policy: [0x92; 32],
            ..terminal_fixture(0x52, 0x81)
        }
        .receipt();
        assert_eq!(
            objective.advance(head, &wrong_policy),
            Err(PrivateBazaarProgressionError::WrongPolicy)
        );
        assert_eq!(objective.head(), head);
        assert_eq!(objective.sequence(), 1);
    }

    #[cfg(feature = "private-clearing")]
    #[test]
    fn progression_binding_covers_result_and_public_adapter_leaks_no_private_fields() {
        let fixture = terminal_fixture(0x51, 0x61);
        let terminal = fixture.receipt();
        let core = terminal.committed_terminal_core().unwrap();
        let mut objective =
            PrivateBazaarRaidProgression::new([0x41; 32], [0x42; 32], [0x43; 32], 2).unwrap();
        let progressed = objective.advance(objective.head(), &terminal).unwrap();
        assert!(progressed.binding_verifies([0x43; 32], [0x42; 32], &core));

        let mut forged_result = progressed.clone();
        forged_result.result.complete = true;
        assert!(!forged_result.binding_verifies([0x43; 32], [0x42; 32], &core));
        let mut forged_predecessor = progressed.clone();
        forged_predecessor.predecessor_id = [0x99; 32];
        assert!(!forged_predecessor.binding_verifies([0x43; 32], [0x42; 32], &core));

        let published = format!(
            "{:?}\n{:?}",
            progressed.adapter_payload(),
            progressed.surface().view()
        );
        for forbidden_word in [
            "winner",
            "actor",
            "target",
            "bid",
            "price",
            "reward value",
            "proof bytes",
            "private root",
        ] {
            assert!(
                !published.contains(forbidden_word),
                "viewer-blind adapter leaked {forbidden_word}: {published}"
            );
        }
        for private_value in [
            fixture.deployment,
            fixture.market,
            fixture.policy,
            fixture.source_use,
            fixture.operation,
            fixture.game_receipt,
            fixture.game_turn,
            fixture.game_state,
        ] {
            assert!(
                !published.contains(&hex32(private_value)),
                "viewer-blind adapter leaked a private routing/effect field: {published}"
            );
        }
    }
}
