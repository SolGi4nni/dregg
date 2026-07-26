//! The shared game-session spine.
//!
//! Dungeon, Descent, the Dark Bazaar, and the other catalog games keep their
//! own rule interpreters and session types.  What they share is the existing
//! [`OfferingHost`] protocol: an exact `(offering, session)` address, audience-
//! scoped affordances, real turn or binary-operation receipts, verification,
//! and replay.  This module gives frontends one typed view of that protocol;
//! it does not introduce a second game engine.

use std::collections::BTreeSet;

use dreggnet_offerings::{
    Action, Attribution, Audience, AudienceProjection, BinaryArtifactDescriptor,
    BinaryOperationDescriptor, DreggIdentity, HostArtifactError, HostOperationError, OfferingHost,
    Outcome, RunCost, SessionId, SignedAction, SignedError, TurnSigner, VerifyReport,
    verify_detached,
};

/// The distinct rule families mounted in the shared game catalog.
///
/// This is presentation metadata only.  Admission remains the concrete
/// offering's executor/proof verifier; a frontend must never branch on this
/// enum to decide whether a move is legal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GameKind {
    Descent,
    DescentCampaign,
    Dungeon,
    /// The catalog's public/check-level CRAWL, not the separately hosted
    /// encrypted `DarkAmmGameOffering` apex.
    DarkBazaarCrawl,
    /// The opt-in encrypted Dark AMM game registered under `dark-pool`.
    DarkPool,
    TacticalRaid,
    Council,
    Market,
    MultiwayTug,
    Automatafl,
}

impl GameKind {
    /// Stable player-facing family name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Descent => "descent",
            Self::DescentCampaign => "descent-campaign",
            Self::Dungeon => "dungeon",
            Self::DarkBazaarCrawl => "dark-bazaar-crawl",
            Self::DarkPool => "dark-pool",
            Self::TacticalRaid => "tactical-raid",
            Self::Council => "council",
            Self::Market => "market",
            Self::MultiwayTug => "multiway-tug",
            Self::Automatafl => "automatafl",
        }
    }
}

/// Classify one catalog route as a game rule family.
///
/// Services and RPG read/feature surfaces deliberately return `None`; they use
/// the same Offering substrate but are not mislabeled as games in game chrome.
pub fn game_kind(offering: &str) -> Option<GameKind> {
    match offering {
        "descent" => Some(GameKind::Descent),
        "descent-campaign" => Some(GameKind::DescentCampaign),
        "dungeon" => Some(GameKind::Dungeon),
        "bazaar" => Some(GameKind::DarkBazaarCrawl),
        "dark-pool" => Some(GameKind::DarkPool),
        "private-raid" => Some(GameKind::TacticalRaid),
        "council" => Some(GameKind::Council),
        "market" => Some(GameKind::Market),
        "tug" => Some(GameKind::MultiwayTug),
        "automatafl" => Some(GameKind::Automatafl),
        _ => None,
    }
}

/// A stable deployment/federation incarnation.
///
/// This value is routing authority, not actor authentication. A deployment
/// persists it across ordinary process restarts and replaces it when a new
/// host/federation is meant to be a distinct authority. The all-zero value is
/// refused so an uninitialised deployment cannot silently share an identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GameHostIncarnation([u8; 32]);

impl GameHostIncarnation {
    pub fn new(bytes: [u8; 32]) -> Result<Self, GameSpineError> {
        if bytes == [0; 32] {
            return Err(GameSpineError::InvalidReference(
                "host incarnation must not be the all-zero sentinel".to_string(),
            ));
        }
        Ok(Self(bytes))
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

/// The authority epoch carried by a game-session address.
///
/// `Bound` is the deployable form: it distinguishes two hosts with the same
/// human session name and distinguishes close/reopen generations within one
/// host. `LegacyUnbound` exists only so the already-deployed frontend adapters
/// can migrate without pretending their old two-field addresses are hardened.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GameSessionBinding {
    LegacyUnbound,
    Bound {
        host_incarnation: GameHostIncarnation,
        session_generation: u64,
    },
}

impl GameSessionBinding {
    pub const fn bound(host_incarnation: GameHostIncarnation, session_generation: u64) -> Self {
        Self::Bound {
            host_incarnation,
            session_generation,
        }
    }

    pub const fn is_bound(&self) -> bool {
        matches!(self, Self::Bound { .. })
    }
}

/// The exact, surface-independent address of one game session.
///
/// This is an address, never an authorization capability. It is intentionally
/// kept structured rather
/// than collapsed into a display hash: two games may legitimately use the same
/// session token, and the offering key is what keeps them distinct.  Web,
/// Discord, Telegram, and native clients resume the same game when they carry
/// this same pair.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GameSessionRef {
    offering: String,
    session: SessionId,
    binding: GameSessionBinding,
}

impl GameSessionRef {
    /// Address `session` under a registered game `offering` using the legacy
    /// two-field route. Bound APIs reject this compatibility form.
    pub fn new(offering: impl Into<String>, session: SessionId) -> Result<Self, GameSpineError> {
        Self::with_binding(offering, session, GameSessionBinding::LegacyUnbound)
    }

    /// Address one exact generation under a stable host/federation
    /// incarnation. This is the form new durable adapters should persist.
    pub fn bound(
        offering: impl Into<String>,
        session: SessionId,
        host_incarnation: GameHostIncarnation,
        session_generation: u64,
    ) -> Result<Self, GameSpineError> {
        Self::with_binding(
            offering,
            session,
            GameSessionBinding::bound(host_incarnation, session_generation),
        )
    }

    fn with_binding(
        offering: impl Into<String>,
        session: SessionId,
        binding: GameSessionBinding,
    ) -> Result<Self, GameSpineError> {
        let offering = offering.into();
        if offering.is_empty()
            || session.0.is_empty()
            || session.0.len() > 256
            || !session.0.bytes().all(|byte| {
                byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_' | b':')
            })
        {
            return Err(GameSpineError::InvalidReference(
                "session id must be 1..=256 stable ASCII identifier bytes [A-Za-z0-9._:-]"
                    .to_string(),
            ));
        }
        if game_kind(&offering).is_none() {
            return Err(GameSpineError::NotAGame(offering));
        }
        Ok(Self {
            offering,
            session,
            binding,
        })
    }

    pub fn offering(&self) -> &str {
        &self.offering
    }

    pub fn session_id(&self) -> &SessionId {
        &self.session
    }

    pub fn binding(&self) -> &GameSessionBinding {
        &self.binding
    }

    pub fn kind(&self) -> GameKind {
        game_kind(&self.offering).expect("GameSessionRef construction checks the catalog key")
    }
}

/// Exact executable identity of one ordinary action at one observed state head.
///
/// `turn`, `arg`, and `text` are the fields the executor resolves (and the
/// signed-turn wire binds), so all three are part of the identity. `label`,
/// `enabled`, and `wants_text` remain presentation decorations. A frontend
/// collecting free text must construct the final reference from the final
/// action, rather than reusing the empty input-slot template's reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GameActionRef {
    pub session: GameSessionRef,
    pub turn: String,
    pub arg: i64,
    pub text: Option<String>,
    /// Host surface head observed when the affordance was presented. This is a
    /// stale-command/TOCTOU guard, not a canonical state root or authorization.
    pub expected_pre_head: Vec<u8>,
}

impl GameActionRef {
    pub fn new(session: GameSessionRef, action: &Action, expected_pre_head: Vec<u8>) -> Self {
        Self {
            session,
            turn: action.turn.clone(),
            arg: action.arg,
            text: action.text.clone(),
            expected_pre_head,
        }
    }

    fn matches(&self, action: &Action) -> bool {
        self.turn == action.turn && self.arg == action.arg && self.text == action.text
    }

    /// Domain-separated identity of the exact router action preimage.
    ///
    /// This includes the host incarnation and session generation carried by
    /// `session`, as well as the complete executor-resolved action and observed
    /// head. It does not replace the underlying signed-turn envelope.
    pub fn routing_preimage_id(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg.game-action-preimage.v2");
        hash_session_ref(&mut hasher, &self.session);
        hash_field(&mut hasher, self.turn.as_bytes());
        hash_field(&mut hasher, &self.arg.to_be_bytes());
        match &self.text {
            Some(text) => {
                hash_field(&mut hasher, &[1]);
                hash_field(&mut hasher, text.as_bytes());
            }
            None => hash_field(&mut hasher, &[0]),
        }
        hash_field(&mut hasher, &self.expected_pre_head);
        *hasher.finalize().as_bytes()
    }
}

/// Domain for a client-signed game command. Its message signs the
/// [`GameActionRef::routing_preimage_id`] (therefore the exact host
/// incarnation, generation, session, action, and observed head) plus the
/// offering replay counter.
pub const GAME_ACTION_SIGNING_DOMAIN: &[u8] = b"dregg-game-action-command-v1:";

/// Canonical bytes signed by the outer game command envelope.
pub fn game_action_signing_message(reference: &GameActionRef, counter: u64) -> Vec<u8> {
    let mut message = Vec::with_capacity(GAME_ACTION_SIGNING_DOMAIN.len() + 32 + 8);
    message.extend_from_slice(GAME_ACTION_SIGNING_DOMAIN);
    message.extend_from_slice(&reference.routing_preimage_id());
    message.extend_from_slice(&counter.to_le_bytes());
    message
}

/// A client-signed game turn whose authority coordinates are part of the
/// signature, rather than a legacy [`SignedAction`] wrapped by the server after
/// receipt. The inner envelope remains for the OfferingHost replay-counter and
/// attribution machinery; `authority_signature` prevents it from being moved
/// to a different generation or state head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedGameAction {
    pub reference: GameActionRef,
    pub signed_action: SignedAction,
    pub authority_signature: [u8; 64],
}

/// Sign both the legacy offering envelope and the exact bound game command.
/// Custodial adapters and user-held clients must call this with the reference
/// presented by the rendered surface; recomputing a current reference at POST
/// time would reintroduce stale-tab replay.
pub fn sign_game_action(
    signer: &TurnSigner,
    reference: GameActionRef,
    counter: u64,
    action: Action,
) -> Result<SignedGameAction, GameSpineError> {
    if !reference.session.binding().is_bound() {
        return Err(GameSpineError::BindingContextRequired(
            reference.session.clone(),
        ));
    }
    if !reference.matches(&action) {
        return Err(GameSpineError::InvalidReference(
            "action does not match the exact signed game reference".to_string(),
        ));
    }
    let signed_action = signer.sign(
        reference.session.offering(),
        reference.session.session_id(),
        counter,
        action,
    );
    let authority_signature =
        signer.sign_detached(&game_action_signing_message(&reference, counter));
    Ok(SignedGameAction {
        reference,
        signed_action,
        authority_signature,
    })
}

/// Verify only the cryptographic actor/authority envelope. This is deliberately
/// non-consuming so a web boundary can derive the authenticated viewer before
/// any private projection; replay consumption remains atomic with execution in
/// [`OfferingHost::advance_signed`].
pub fn verify_signed_game_action(command: &SignedGameAction) -> Result<DreggIdentity, SignedError> {
    verify_detached(
        &command.signed_action.actor_pubkey_hex,
        &game_action_signing_message(&command.reference, command.signed_action.counter),
        &command.authority_signature,
    )
}

/// Stable identity of one opaque proof/attestation operation in a session.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GameOperationRef {
    pub session: GameSessionRef,
    pub operation: String,
    /// Host surface head observed when this operation was advertised.
    pub expected_pre_head: Vec<u8>,
}

/// Stable identity of one read-only session artifact.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GameArtifactRef {
    pub session: GameSessionRef,
    pub artifact: String,
    /// Host surface head at which this artifact was advertised.
    pub observed_head: Vec<u8>,
}

/// The provenance of a requested game projection.
///
/// A private projection is an information release. The common spine can carry
/// an adapter's asserted viewer identity, but cannot authenticate a Discord,
/// Telegram, or web user on the adapter's behalf. The explicit variant stops a
/// raw identity label from being mistaken for proof of access.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameAudience {
    Shared,
    AssertedPrivate(DreggIdentity),
}

impl GameAudience {
    fn offerings_audience(&self) -> Audience {
        match self {
            Self::Shared => Audience::Shared,
            Self::AssertedPrivate(viewer) => Audience::Private(viewer.clone()),
        }
    }

    fn attribution(&self) -> Option<Attribution> {
        match self {
            Self::Shared => None,
            Self::AssertedPrivate(viewer) => Some(Attribution::from(viewer.clone())),
        }
    }
}

/// One frontend-neutral player affordance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameAffordance {
    /// A normal executor-refereed game turn.
    Turn {
        reference: GameActionRef,
        action: Action,
        cost: RunCost,
    },
    /// An owning binary operation such as a shielded assignment or settlement.
    Operation {
        reference: GameOperationRef,
        descriptor: BinaryOperationDescriptor,
    },
}

/// One read-only resource published by the live session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GameArtifact {
    pub reference: GameArtifactRef,
    pub descriptor: BinaryArtifactDescriptor,
}

/// The common player-facing view of any live game session.
#[derive(Clone, Debug)]
pub struct GameSessionView {
    pub session: GameSessionRef,
    pub kind: GameKind,
    /// `None` for a shared projection; explicitly `Asserted` for the private
    /// viewer label supplied by an adapter. This never proves authentication.
    pub viewer_attribution: Option<Attribution>,
    /// Audience-safe surface and the exact ordinary actions painted with it.
    pub projection: AudienceProjection,
    /// Ordinary actions plus the currently advertised shielded/binary actions.
    pub affordances: Vec<GameAffordance>,
    pub artifacts: Vec<GameArtifact>,
    pub verification: VerifyReport,
    /// Whether a host replay journal exists. This does not claim that mutations
    /// performed outside this spine were journaled; spine operations themselves
    /// are preflighted to require offering-selected safe replay material.
    pub replay_journal_present: bool,
    /// Number of landed ordinary turns plus journaled binary operations after
    /// genesis, from the exact replay timeline.
    pub landed_steps: usize,
    /// Host fingerprint of the rendered surface plus verification summary.
    /// This is useful for restart equality but is not a canonical game-state
    /// root and must not be used as an authorization or proof input.
    pub surface_commitment: Vec<u8>,
}

/// Inspect a live game through one audience-safe, surface-independent call.
pub fn inspect_game_session(
    host: &OfferingHost,
    session: GameSessionRef,
    audience: &GameAudience,
) -> Result<GameSessionView, GameSpineError> {
    require_legacy_binding(&session)?;
    inspect_game_session_inner(host, session, audience)
}

/// Inspect one authority-bound game session.
///
/// `live_generation` comes from the deployment's durable session-name epoch
/// ledger. A restart supplies the same persisted host incarnation and current
/// generation; a replacement host or a close/reopen supplies a different one.
pub fn inspect_bound_game_session(
    host: &OfferingHost,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
    session: GameSessionRef,
    audience: &GameAudience,
) -> Result<GameSessionView, GameSpineError> {
    require_live_binding(&session, host_incarnation, live_generation)?;
    inspect_game_session_inner(host, session, audience)
}

fn inspect_game_session_inner(
    host: &OfferingHost,
    session: GameSessionRef,
    audience: &GameAudience,
) -> Result<GameSessionView, GameSpineError> {
    let surface_commitment = host
        .commitment(session.offering(), session.session_id())
        .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;
    let offerings_audience = audience.offerings_audience();
    let projection = host
        .project(
            session.offering(),
            session.session_id(),
            &offerings_audience,
        )
        .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;

    let mut action_ids = BTreeSet::new();
    let mut affordances = Vec::with_capacity(projection.actions.len());
    for action in &projection.actions {
        let reference = GameActionRef::new(session.clone(), action, surface_commitment.clone());
        if !action_ids.insert((
            reference.turn.clone(),
            reference.arg,
            reference.text.clone(),
        )) {
            return Err(GameSpineError::AmbiguousAffordance(format!(
                "duplicate action route ({:?}, {}, {:?}) in {} / {}",
                reference.turn,
                reference.arg,
                reference.text,
                session.offering(),
                session.session_id().0
            )));
        }
        let cost = host
            .price(session.offering(), session.session_id(), action)
            .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;
        affordances.push(GameAffordance::Turn {
            reference,
            action: action.clone(),
            cost,
        });
    }

    let operations = host
        .binary_operations(session.offering(), session.session_id())
        .map_err(GameSpineError::operation_discovery)?;
    let mut operation_ids = BTreeSet::new();
    for descriptor in operations {
        if descriptor.name.is_empty() || !operation_ids.insert(descriptor.name.clone()) {
            return Err(GameSpineError::AmbiguousAffordance(format!(
                "empty or duplicate binary operation route {:?} in {} / {}",
                descriptor.name,
                session.offering(),
                session.session_id().0
            )));
        }
        affordances.push(GameAffordance::Operation {
            reference: GameOperationRef {
                session: session.clone(),
                operation: descriptor.name.clone(),
                expected_pre_head: surface_commitment.clone(),
            },
            descriptor,
        });
    }

    let artifact_descriptors = host
        .binary_artifacts(session.offering(), session.session_id())
        .map_err(GameSpineError::artifact_discovery)?;
    let mut artifact_ids = BTreeSet::new();
    let mut artifacts = Vec::with_capacity(artifact_descriptors.len());
    for descriptor in artifact_descriptors {
        if descriptor.name.is_empty() || !artifact_ids.insert(descriptor.name.clone()) {
            return Err(GameSpineError::AmbiguousAffordance(format!(
                "empty or duplicate binary artifact route {:?} in {} / {}",
                descriptor.name,
                session.offering(),
                session.session_id().0
            )));
        }
        artifacts.push(GameArtifact {
            reference: GameArtifactRef {
                session: session.clone(),
                artifact: descriptor.name.clone(),
                observed_head: surface_commitment.clone(),
            },
            descriptor,
        });
    }
    let verification = host
        .verify(session.offering(), session.session_id())
        .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;
    let log = host.move_log(session.offering(), session.session_id());
    let landed_steps = log
        .as_ref()
        .map(|log| log.moves.len().saturating_add(log.operations.len()))
        .unwrap_or(0);

    Ok(GameSessionView {
        kind: session.kind(),
        session,
        viewer_attribution: audience.attribution(),
        projection,
        affordances,
        artifacts,
        verification,
        replay_journal_present: log.is_some(),
        landed_steps,
        surface_commitment,
    })
}

/// A frontend-neutral command collected from any game surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameCommand {
    Turn {
        reference: GameActionRef,
        action: Action,
    },
    Operation {
        reference: GameOperationRef,
        payload: Vec<u8>,
    },
}

impl GameCommand {
    pub fn session(&self) -> &GameSessionRef {
        match self {
            Self::Turn { reference, .. } => &reference.session,
            Self::Operation { reference, .. } => &reference.session,
        }
    }
}

/// The common receipt vocabulary returned after any game command lands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameReceipt {
    Turn {
        action: GameActionRef,
        /// Exact trust level of the player attribution used for this turn.
        attribution: Attribution,
        /// The actual executor cell carried by the underlying TurnReceipt.
        executor_agent: [u8; 32],
        /// Router receipt over the full action preimage, provenance, and the
        /// concrete receipt. This is the ID exposed by [`Self::receipt_id`].
        bound_receipt_id: [u8; 32],
        /// Receipt produced by the concrete offering before router binding.
        inner_receipt_id: [u8; 32],
        previous_receipt_id: Option<[u8; 32]>,
        ended: bool,
    },
    Operation {
        operation: GameOperationRef,
        /// Binary operations currently have no signed host path. This is
        /// therefore always explicit asserted adapter attribution.
        attribution: Attribution,
        /// Domain-separated routing receipt over the exact host address,
        /// asserted actor, operation, payload digest, inner receipt, and the
        /// observed before/after heads.
        bound_receipt_id: [u8; 32],
        /// The concrete game's receipt. It may bind a private internal session,
        /// but must not be presented as bound to the host `SessionId`.
        inner_receipt_id: [u8; 32],
        payload_digest: [u8; 32],
        before: Vec<u8>,
        after: Vec<u8>,
        public_fields: Vec<(String, String)>,
    },
}

impl GameReceipt {
    pub fn receipt_id(&self) -> [u8; 32] {
        match self {
            Self::Turn {
                bound_receipt_id, ..
            } => *bound_receipt_id,
            Self::Operation {
                bound_receipt_id, ..
            } => *bound_receipt_id,
        }
    }

    /// The concrete operation receipt before router binding.
    pub fn inner_receipt_id(&self) -> Option<[u8; 32]> {
        match self {
            Self::Turn { .. } => None,
            Self::Operation {
                inner_receipt_id, ..
            } => Some(*inner_receipt_id),
        }
    }

    pub fn session(&self) -> &GameSessionRef {
        match self {
            Self::Turn { action, .. } => &action.session,
            Self::Operation { operation, .. } => &operation.session,
        }
    }

    /// Honest provenance for the player identity routed through OfferingHost.
    pub fn attribution(&self) -> &Attribution {
        match self {
            Self::Turn { attribution, .. } | Self::Operation { attribution, .. } => attribution,
        }
    }

    /// Recompute the complete router binding carried by any landed receipt.
    ///
    /// This checks envelope integrity only. An `Asserted` actor remains
    /// asserted even when the digest is internally consistent.
    pub fn routing_binding_valid(&self) -> bool {
        match self {
            Self::Turn {
                action,
                attribution,
                executor_agent,
                bound_receipt_id,
                inner_receipt_id,
                previous_receipt_id,
                ended,
            } => {
                turn_routing_receipt_id(
                    action,
                    attribution,
                    *executor_agent,
                    *inner_receipt_id,
                    *previous_receipt_id,
                    *ended,
                ) == *bound_receipt_id
            }
            Self::Operation {
                operation,
                attribution,
                bound_receipt_id,
                inner_receipt_id,
                payload_digest,
                before,
                after,
                ..
            } => {
                operation_routing_receipt_id(
                    &operation.session,
                    attribution,
                    &operation.operation,
                    *payload_digest,
                    *inner_receipt_id,
                    before,
                    after,
                ) == *bound_receipt_id
            }
        }
    }

    /// Compatibility name for operation-only callers.
    pub fn operation_routing_binding_valid(&self) -> bool {
        !matches!(self, Self::Operation { .. }) || self.routing_binding_valid()
    }
}

/// A command either lands one receipt or is refused without one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameResult {
    Landed(GameReceipt),
    Refused {
        session: GameSessionRef,
        reason: String,
    },
}

/// One bound ordinary-turn execution, preserving both the frontend's original
/// substrate [`Outcome`] and the game-spine routing result.
///
/// Frontend adapters with an established `Outcome`-based API can therefore
/// migrate onto exact bound execution without executing twice or discarding
/// the domain-bound routing receipt.
#[derive(Clone, Debug)]
pub struct BoundGameTurnExecution {
    pub outcome: Outcome,
    pub result: GameResult,
}

impl GameResult {
    pub fn receipt(&self) -> Option<&GameReceipt> {
        match self {
            Self::Landed(receipt) => Some(receipt),
            Self::Refused { .. } => None,
        }
    }
}

/// Execute a command using an adapter-asserted actor label.
///
/// The name is intentionally explicit: this path does not authenticate the
/// actor. Signed ordinary turns should use [`execute_signed_game_turn`]. A
/// binary-operation adapter must authenticate its transport principal before
/// choosing the asserted identity because OfferingHost has no signed opaque-
/// operation envelope yet.
pub fn execute_asserted_game_command(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    command: GameCommand,
    actor: DreggIdentity,
) -> Result<GameResult, GameSpineError> {
    require_legacy_binding(session)?;
    execute_asserted_game_command_inner(host, session, command, actor)
}

/// Execute an adapter-attributed command under an exact live host/session
/// authority epoch.
pub fn execute_bound_asserted_game_command(
    host: &mut OfferingHost,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
    session: &GameSessionRef,
    command: GameCommand,
    actor: DreggIdentity,
) -> Result<GameResult, GameSpineError> {
    require_live_binding(session, host_incarnation, live_generation)?;
    execute_asserted_game_command_inner(host, session, command, actor)
}

/// Execute one adapter-attributed ordinary turn under an exact live authority
/// epoch while preserving the original substrate outcome for frontend APIs.
pub fn execute_bound_asserted_game_turn(
    host: &mut OfferingHost,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
    session: &GameSessionRef,
    reference: GameActionRef,
    action: Action,
    actor: DreggIdentity,
) -> Result<BoundGameTurnExecution, GameSpineError> {
    require_live_binding(session, host_incarnation, live_generation)?;
    execute_asserted_game_turn_inner(host, session, reference, action, actor)
}

fn execute_asserted_game_command_inner(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    command: GameCommand,
    actor: DreggIdentity,
) -> Result<GameResult, GameSpineError> {
    if command.session() != session {
        return Err(GameSpineError::AddressMismatch {
            expected: session.clone(),
            presented: command.session().clone(),
        });
    }

    match command {
        GameCommand::Turn { reference, action } => {
            Ok(execute_asserted_game_turn_inner(host, session, reference, action, actor)?.result)
        }
        GameCommand::Operation { reference, payload } => {
            check_expected_head(host, session, &reference.expected_pre_head)?;
            let descriptors = host
                .binary_operations(session.offering(), session.session_id())
                .map_err(GameSpineError::operation_discovery)?;
            let mut matches = descriptors
                .iter()
                .filter(|descriptor| descriptor.name == reference.operation);
            let descriptor = matches.next().ok_or_else(|| {
                GameSpineError::InvalidReference(format!(
                    "operation {:?} is no longer advertised",
                    reference.operation
                ))
            })?;
            if matches.next().is_some() {
                return Err(GameSpineError::AmbiguousAffordance(format!(
                    "duplicate live operation route {:?}",
                    reference.operation
                )));
            }
            if payload.len() > descriptor.max_input_bytes {
                return Err(GameSpineError::PayloadTooLarge {
                    operation: reference.operation.clone(),
                    actual: payload.len(),
                    maximum: descriptor.max_input_bytes,
                });
            }
            match host.binary_operation_replayable(
                session.offering(),
                session.session_id(),
                &reference.operation,
                &payload,
            ) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(GameSpineError::UnreplayableOperation(
                        reference.operation.clone(),
                    ));
                }
                Err(HostOperationError::Operation(error)) => {
                    return Ok(GameResult::Refused {
                        session: session.clone(),
                        reason: error.to_string(),
                    });
                }
                Err(error) => return Err(GameSpineError::operation_discovery(error)),
            }
            let payload_digest = *blake3::hash(&payload).as_bytes();
            match host.invoke_binary_operation_bound(
                session.offering(),
                session.session_id(),
                &reference.operation,
                &payload,
                actor.clone(),
            ) {
                Ok(applied) => {
                    if applied.offering != session.offering()
                        || &applied.session != session.session_id()
                        || applied.actor != actor
                        || applied.receipt.operation != reference.operation
                    {
                        return Err(GameSpineError::InvalidHostReceipt(
                            "bound operation result disagrees with the requested route".to_string(),
                        ));
                    }
                    let bound_receipt_id = operation_routing_receipt_id(
                        &reference.session,
                        &Attribution::from(applied.actor.clone()),
                        &applied.receipt.operation,
                        payload_digest,
                        applied.receipt.receipt_id,
                        &applied.before,
                        &applied.after,
                    );
                    Ok(GameResult::Landed(GameReceipt::Operation {
                        operation: reference,
                        attribution: Attribution::from(actor),
                        bound_receipt_id,
                        inner_receipt_id: applied.receipt.receipt_id,
                        payload_digest,
                        before: applied.before,
                        after: applied.after,
                        public_fields: applied.receipt.public_fields,
                    }))
                }
                Err(HostOperationError::Operation(error)) => Ok(GameResult::Refused {
                    session: session.clone(),
                    reason: error.to_string(),
                }),
                Err(error) => Err(GameSpineError::operation_discovery(error)),
            }
        }
    }
}

fn execute_asserted_game_turn_inner(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    reference: GameActionRef,
    action: Action,
    actor: DreggIdentity,
) -> Result<BoundGameTurnExecution, GameSpineError> {
    if &reference.session != session {
        return Err(GameSpineError::AddressMismatch {
            expected: session.clone(),
            presented: reference.session.clone(),
        });
    }
    check_expected_head(host, session, &reference.expected_pre_head)?;
    if !reference.matches(&action) {
        return Err(GameSpineError::InvalidReference(
            "action payload does not match its exact {turn, arg, text} reference".to_string(),
        ));
    }
    let outcome = host
        .advance(
            session.offering(),
            session.session_id(),
            action,
            actor.clone(),
        )
        .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;
    let result = match &outcome {
        Outcome::Landed { receipt, ended } => {
            let attribution = Attribution::from(actor);
            let executor_agent = *receipt.agent.as_bytes();
            let inner_receipt_id = receipt.receipt_hash();
            let bound_receipt_id = turn_routing_receipt_id(
                &reference,
                &attribution,
                executor_agent,
                inner_receipt_id,
                receipt.previous_receipt_hash,
                *ended,
            );
            GameResult::Landed(GameReceipt::Turn {
                action: reference,
                attribution,
                executor_agent,
                bound_receipt_id,
                inner_receipt_id,
                previous_receipt_id: receipt.previous_receipt_hash,
                ended: *ended,
            })
        }
        Outcome::Refused(reason) => GameResult::Refused {
            session: session.clone(),
            reason: reason.clone(),
        },
    };
    Ok(BoundGameTurnExecution { outcome, result })
}

/// Execute one cryptographically signed ordinary turn at its observed head.
pub fn execute_signed_game_turn(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    reference: GameActionRef,
    signed: SignedAction,
) -> Result<GameResult, GameSpineError> {
    require_legacy_binding(session)?;
    execute_signed_game_turn_inner(host, session, reference, signed)
        .map(|execution| execution.result)
}

/// Execute a signed ordinary turn under an exact live host/session authority
/// epoch. The router binding is additional to (and does not change) the
/// offering's existing signed-turn wire.
pub fn execute_bound_signed_game_turn(
    host: &mut OfferingHost,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
    session: &GameSessionRef,
    command: SignedGameAction,
) -> Result<GameResult, GameSpineError> {
    require_live_binding(session, host_incarnation, live_generation)?;
    execute_bound_signed_game_turn_inner(host, session, command).map(|execution| execution.result)
}

/// Execute one signed game turn under a live authority epoch while retaining
/// the concrete executor outcome beside its viewer-independent routing result.
/// This is the signed analogue of [`execute_bound_asserted_game_turn`].
pub fn execute_bound_signed_game_turn_with_outcome(
    host: &mut OfferingHost,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
    session: &GameSessionRef,
    command: SignedGameAction,
) -> Result<BoundGameTurnExecution, GameSpineError> {
    require_live_binding(session, host_incarnation, live_generation)?;
    execute_bound_signed_game_turn_inner(host, session, command)
}

fn execute_bound_signed_game_turn_inner(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    command: SignedGameAction,
) -> Result<BoundGameTurnExecution, GameSpineError> {
    if &command.reference.session != session {
        return Err(GameSpineError::AddressMismatch {
            expected: session.clone(),
            presented: command.reference.session.clone(),
        });
    }
    // Authenticate the client-presented generation/head coordinates before
    // looking at state or private affordances. The host consumes the legacy
    // replay counter only after this outer authority signature passes.
    verify_signed_game_action(&command).map_err(|error| GameSpineError::Host(error.to_string()))?;
    execute_signed_game_turn_inner(host, session, command.reference, command.signed_action)
}

fn execute_signed_game_turn_inner(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    reference: GameActionRef,
    signed: SignedAction,
) -> Result<BoundGameTurnExecution, GameSpineError> {
    if &reference.session != session {
        return Err(GameSpineError::AddressMismatch {
            expected: session.clone(),
            presented: reference.session.clone(),
        });
    }
    check_expected_head(host, session, &reference.expected_pre_head)?;
    if !reference.matches(&signed.action) {
        return Err(GameSpineError::InvalidReference(
            "signed action does not match its exact {turn, arg, text} reference".to_string(),
        ));
    }
    let signer = signed.actor_pubkey_hex.to_ascii_lowercase();
    let outcome = host
        .advance_signed(session.offering(), session.session_id(), signed)
        .map_err(|error| GameSpineError::Host(error.to_string()))?;
    let result = match &outcome {
        Outcome::Landed { receipt, ended } => {
            let attribution = Attribution::Signed { pubkey_hex: signer };
            let executor_agent = *receipt.agent.as_bytes();
            let inner_receipt_id = receipt.receipt_hash();
            let bound_receipt_id = turn_routing_receipt_id(
                &reference,
                &attribution,
                executor_agent,
                inner_receipt_id,
                receipt.previous_receipt_hash,
                *ended,
            );
            GameResult::Landed(GameReceipt::Turn {
                action: reference,
                attribution,
                executor_agent,
                bound_receipt_id,
                inner_receipt_id,
                previous_receipt_id: receipt.previous_receipt_hash,
                ended: *ended,
            })
        }
        Outcome::Refused(reason) => GameResult::Refused {
            session: session.clone(),
            reason: reason.clone(),
        },
    };
    Ok(BoundGameTurnExecution { outcome, result })
}

fn check_expected_head(
    host: &OfferingHost,
    session: &GameSessionRef,
    expected: &[u8],
) -> Result<(), GameSpineError> {
    let actual = host
        .commitment(session.offering(), session.session_id())
        .ok_or_else(|| GameSpineError::UnknownSession(session.clone()))?;
    if actual != expected {
        return Err(GameSpineError::StaleCommand {
            session: session.clone(),
            expected: expected.to_vec(),
            actual,
        });
    }
    Ok(())
}

fn require_legacy_binding(session: &GameSessionRef) -> Result<(), GameSpineError> {
    if session.binding().is_bound() {
        return Err(GameSpineError::BindingContextRequired(session.clone()));
    }
    Ok(())
}

fn require_live_binding(
    session: &GameSessionRef,
    host_incarnation: GameHostIncarnation,
    live_generation: u64,
) -> Result<(), GameSpineError> {
    let expected = GameSessionBinding::bound(host_incarnation, live_generation);
    if session.binding() != &expected {
        return Err(GameSpineError::AuthorityEpochMismatch {
            session: session.clone(),
            expected,
            presented: session.binding().clone(),
        });
    }
    Ok(())
}

fn hash_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn hash_session_ref(hasher: &mut blake3::Hasher, session: &GameSessionRef) {
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

fn hash_attribution(hasher: &mut blake3::Hasher, attribution: &Attribution) {
    match attribution {
        Attribution::Asserted { label } => {
            hash_field(hasher, &[0]);
            hash_field(hasher, label.as_bytes());
        }
        Attribution::Signed { pubkey_hex } => {
            hash_field(hasher, &[1]);
            hash_field(hasher, pubkey_hex.as_bytes());
        }
    }
}

fn turn_routing_receipt_id(
    action: &GameActionRef,
    attribution: &Attribution,
    executor_agent: [u8; 32],
    inner_receipt_id: [u8; 32],
    previous_receipt_id: Option<[u8; 32]>,
    ended: bool,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg.game-turn-routing-receipt.v2");
    hash_field(&mut hasher, &action.routing_preimage_id());
    hash_attribution(&mut hasher, attribution);
    hash_field(&mut hasher, &executor_agent);
    hash_field(&mut hasher, &inner_receipt_id);
    match previous_receipt_id {
        Some(previous) => {
            hash_field(&mut hasher, &[1]);
            hash_field(&mut hasher, &previous);
        }
        None => hash_field(&mut hasher, &[0]),
    }
    hash_field(&mut hasher, &[u8::from(ended)]);
    *hasher.finalize().as_bytes()
}

fn operation_routing_receipt_id(
    session: &GameSessionRef,
    attribution: &Attribution,
    operation: &str,
    payload_digest: [u8; 32],
    inner_receipt_id: [u8; 32],
    before: &[u8],
    after: &[u8],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg.game-operation-routing-receipt.v2");
    hash_session_ref(&mut hasher, session);
    hash_attribution(&mut hasher, attribution);
    hash_field(&mut hasher, operation.as_bytes());
    hash_field(&mut hasher, &payload_digest);
    hash_field(&mut hasher, &inner_receipt_id);
    hash_field(&mut hasher, before);
    hash_field(&mut hasher, after);
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameSpineError {
    InvalidReference(String),
    NotAGame(String),
    /// A bound reference was presented through the compatibility API, where no
    /// live authority epoch is available for comparison.
    BindingContextRequired(GameSessionRef),
    AuthorityEpochMismatch {
        session: GameSessionRef,
        expected: GameSessionBinding,
        presented: GameSessionBinding,
    },
    UnknownSession(GameSessionRef),
    AmbiguousAffordance(String),
    AddressMismatch {
        expected: GameSessionRef,
        presented: GameSessionRef,
    },
    StaleCommand {
        session: GameSessionRef,
        expected: Vec<u8>,
        actual: Vec<u8>,
    },
    PayloadTooLarge {
        operation: String,
        actual: usize,
        maximum: usize,
    },
    UnreplayableOperation(String),
    InvalidHostReceipt(String),
    Host(String),
}

impl GameSpineError {
    /// ⚑ **Did the command present NO route authority at all**, as opposed to presenting one this
    /// spine rejected?
    ///
    /// The distinction is not cosmetic and it is not the player's: a command carrying none of the four
    /// `game_*` route fields is almost always a TEST that stopped presenting them (and whose every
    /// downstream assertion is therefore about a turn that never happened), while a command carrying
    /// wrong ones is a real stale tab — a property tests SHOULD assert. `dreggnet-web`'s dark-act
    /// tripwire keys on exactly that split.
    ///
    /// It used to key on the refusal's PROSE, because the prose was in the response body — and the
    /// prose was in the response body because the body was the raw `to_string()` of this error, which
    /// is the leak the refusal audit closed. So the split has to be answerable HERE, structurally,
    /// rather than by pattern-matching a sentence a player reads: the surface turns this into a
    /// machine-readable header (`dreggnet_web::REFUSAL_KIND_HEADER`) and the player copy stays copy.
    ///
    /// The four "missing/malformed" reasons are the ones
    /// `dreggnet_web::CatalogState::presented_game_action_for` mints for an ABSENT field, and each one
    /// begins with `missing`. Keeping the predicate in the crate that owns those strings is the point:
    /// a reworded reason is a change to this file, one line from its own predicate.
    pub fn is_missing_route_authority(&self) -> bool {
        matches!(self, Self::InvalidReference(reason) if reason.starts_with("missing"))
    }

    fn operation_discovery(error: HostOperationError) -> Self {
        Self::Host(error.to_string())
    }

    fn artifact_discovery(error: HostArtifactError) -> Self {
        Self::Host(error.to_string())
    }
}

impl std::fmt::Display for GameSpineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidReference(reason) => write!(f, "invalid game reference: {reason}"),
            Self::NotAGame(key) => write!(f, "catalog key {key:?} is not a game"),
            Self::BindingContextRequired(session) => write!(
                f,
                "bound game session {} / {} requires an authority-aware spine call",
                session.offering(),
                session.session_id().0
            ),
            // ⚑ NO `{expected:?}` / `{presented:?}`. Those two `{:?}`s Debug-dumped a
            // `GameSessionBinding` — an internal binding struct, braces and field names and all —
            // and this error reaches players: it is a `CatalogGameError::Spine` on the act path, and
            // the web/Discord/Telegram hosts render its `Display`. The two bindings are also
            // redundant to the reader, since this variant only exists when they differ. What is left
            // is the address of the session that moved on, which is the operator's coordinate; the
            // sentence a PLAYER sees for this condition is
            // `dreggnet_web::refused_game_route_response`'s stale-page copy, chosen at the surface.
            Self::AuthorityEpochMismatch { session, .. } => write!(
                f,
                "game authority epoch changed under a presented command for {} / {} (the session was \
                 restarted or re-bound since the command was drawn)",
                session.offering(),
                session.session_id().0
            ),
            Self::UnknownSession(session) => write!(
                f,
                "unknown game session {} / {}",
                session.offering(),
                session.session_id().0
            ),
            Self::AmbiguousAffordance(reason) => write!(f, "ambiguous game affordance: {reason}"),
            Self::AddressMismatch {
                expected,
                presented,
            } => write!(
                f,
                "command addressed to {} / {}, expected {} / {}",
                presented.offering(),
                presented.session_id().0,
                expected.offering(),
                expected.session_id().0
            ),
            Self::StaleCommand { session, .. } => write!(
                f,
                "stale game command for {} / {} (observed head no longer current)",
                session.offering(),
                session.session_id().0
            ),
            Self::PayloadTooLarge {
                operation,
                actual,
                maximum,
            } => write!(
                f,
                "operation {operation:?} payload is {actual} bytes; maximum is {maximum}"
            ),
            Self::UnreplayableOperation(operation) => write!(
                f,
                "operation {operation:?} has no offering-selected safe replay material"
            ),
            Self::InvalidHostReceipt(reason) => {
                write!(f, "invalid host operation receipt: {reason}")
            }
            Self::Host(reason) => write!(f, "game host refused: {reason}"),
        }
    }
}

impl std::error::Error for GameSpineError {}
