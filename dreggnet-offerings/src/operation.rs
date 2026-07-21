//! Transport-bearing deos affordances.
//!
//! Ordinary [`crate::Action`]s are tiny `{turn, arg}` controls.  Some real
//! operations consume an owning, canonical binary object instead: a proof, an
//! attested transcript, or a shielded settlement bundle.  This module gives
//! those operations one frontend-neutral descriptor and result shape without
//! teaching the offering core any particular proof system or media type.
//!
//! The bytes remain opaque here.  The concrete offering is the only decoder and
//! executor; web, Discord, Telegram, and native adapters only enforce their
//! transport/authentication boundary and call the same host method.

use std::collections::BTreeSet;

use crate::resume::{LoggedBinaryOperation, SessionMoveLog, SessionResumeStore};
use crate::{DreggIdentity, SessionId};

/// Absolute byte ceiling for an opaque operation submitted through an ordinary
/// chat attachment.
///
/// Telegram's hosted `getFile` edge is deliberately smaller than the general
/// HTTP upload surface, and chat attachments otherwise invite an adapter to
/// buffer an attacker-selected object before it has consulted the live
/// descriptor.  The chat adapters therefore preflight against both this cap
/// and the operation's own (possibly smaller) cap, then enforce the same bound
/// while streaming the body.  The private preference, fair-shuffle, and
/// private-quest receipts are all advertised at or below this ceiling.
pub const MAX_CHAT_BINARY_OPERATION_BYTES: usize = 8 * 1024 * 1024;

/// Absolute ceiling for one opaque operation admitted by the generic host.
///
/// Individual offerings normally choose much smaller bounds. This host-wide
/// ceiling keeps the web/native descriptor path bounded while allowing it to
/// remain larger than the deliberately conservative chat attachment ceiling.
pub const MAX_HOSTED_BINARY_OPERATION_BYTES: usize = 64 * 1024 * 1024;

/// Absolute ceiling for one artifact crossing the generic hosting seam.
///
/// A concrete descriptor may select a smaller bound. It cannot silently turn
/// this read-only route into an unbounded memory response by advertising a
/// larger one.
pub const MAX_HOSTED_ARTIFACT_BYTES: usize = 64 * 1024 * 1024;

/// Who may retrieve a hosted binary artifact.
///
/// This is explicit because neither the host nor a frontend is allowed to
/// infer secrecy from a media type, title, or the bytes themselves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryArtifactVisibility {
    /// The artifact is deliberately public and may be fetched anonymously.
    Public,
    /// The artifact is not public; a surface must establish an attributed
    /// viewer before asking the host for it.
    Authenticated,
}

impl BinaryArtifactVisibility {
    /// Stable transport spelling used by discovery responses.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Public => "public",
            Self::Authenticated => "authenticated",
        }
    }
}

/// A discoverable, read-only binary artifact of one live offering session.
///
/// Typical artifacts are canonical worker tasks, public proving inputs, or a
/// receipt export. Publishing this descriptor does not itself publish bytes:
/// [`visibility`](Self::visibility) is the explicit retrieval policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryArtifactDescriptor {
    /// Stable protocol/artifact identity within this offering.
    pub name: String,
    /// Human-facing download label.
    pub title: String,
    /// Exact response media type, without content negotiation.
    pub media_type: String,
    /// Offering-selected cap, itself bounded by
    /// [`MAX_HOSTED_ARTIFACT_BYTES`].
    pub max_bytes: usize,
    /// Exact disclosure every renderer must show verbatim.
    pub disclosure: String,
    /// Explicit anonymous-versus-attributed retrieval policy.
    pub visibility: BinaryArtifactVisibility,
}

/// A host-validated artifact ready for an adapter to return.
///
/// The concrete offering supplies only the canonical bytes. The host copies
/// the exact media type from the live descriptor and computes the digest, so
/// those transport claims cannot disagree with the body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryArtifact {
    /// Stable artifact identity that was requested.
    pub name: String,
    /// Exact response media type selected by the live offering descriptor.
    pub media_type: String,
    /// Canonical body bytes.
    pub bytes: Vec<u8>,
    /// BLAKE3 digest of `bytes`.
    pub digest: [u8; 32],
}

/// A concrete offering's refusal while exporting a read-only artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryArtifactError {
    /// This live offering/session does not publish the requested artifact.
    UnknownArtifact(String),
    /// The artifact is explicitly authenticated and no viewer was established.
    AuthenticationRequired,
    /// A descriptor or returned body violated the generic bounded/exact seam.
    InvalidArtifact(String),
    /// The artifact exists, but is not available in the session's current state.
    Refused(String),
}

impl std::fmt::Display for BinaryArtifactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownArtifact(name) => write!(f, "unknown binary artifact {name:?}"),
            Self::AuthenticationRequired => {
                write!(f, "artifact requires an authenticated viewer")
            }
            Self::InvalidArtifact(reason) => write!(f, "invalid hosted artifact: {reason}"),
            Self::Refused(reason) => write!(f, "artifact export refused: {reason}"),
        }
    }
}

impl std::error::Error for BinaryArtifactError {}

/// A discoverable, transport-bearing operation on one live offering session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryOperationDescriptor {
    /// Stable protocol/operation identity.
    pub name: String,
    /// Human-facing control label.
    pub title: String,
    /// Exact request media type.
    pub input_media_type: String,
    /// Hard upper bound adapters must enforce before decoding.
    pub max_input_bytes: usize,
    /// The security disclosure every renderer must show verbatim.
    pub disclosure: String,
}

/// The transport policy selected for one ordinary-chat attachment.
///
/// This is intentionally a copy of the live descriptor rather than a new
/// operation vocabulary.  Telegram and Discord use it between metadata
/// preflight and body download; after download [`validate_body_len`](Self::validate_body_len)
/// closes the dishonest-size race before the opaque bytes reach the offering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChatBinaryOperationPolicy {
    /// The exact live operation descriptor.
    pub descriptor: BinaryOperationDescriptor,
    /// `min(descriptor.max_input_bytes, MAX_CHAT_BINARY_OPERATION_BYTES)`.
    pub transport_max_bytes: usize,
    /// The size the chat platform declared before download.
    pub declared_bytes: usize,
}

impl ChatBinaryOperationPolicy {
    /// Re-check the downloaded byte count against both the declared metadata
    /// and the bounded live policy.  A platform/CDN disagreement fails closed;
    /// callers never "fix up" the declaration after allocating the body.
    pub fn validate_body_len(&self, actual_bytes: usize) -> Result<(), ChatBinaryOperationError> {
        if actual_bytes != self.declared_bytes {
            return Err(ChatBinaryOperationError::SizeChanged {
                declared: self.declared_bytes,
                actual: actual_bytes,
            });
        }
        if actual_bytes > self.transport_max_bytes {
            return Err(ChatBinaryOperationError::TooLarge {
                actual: actual_bytes,
                maximum: self.transport_max_bytes,
            });
        }
        Ok(())
    }
}

/// A refusal at the ordinary Telegram/Discord attachment boundary.
///
/// These are transport refusals, before the concrete offering decoder.  Proof,
/// canonicality, actor, replay, and state binding remain the offering's own
/// [`BinaryOperationError`] domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChatBinaryOperationError {
    /// The live session did not advertise the requested operation.
    UnknownOperation(String),
    /// More than one live descriptor used the same route name, so selecting a
    /// byte policy would be ambiguous.
    DuplicateOperation(String),
    /// The platform's pre-download metadata already exceeds the effective
    /// chat/descriptor cap.
    TooLarge { actual: usize, maximum: usize },
    /// The CDN body length differed from the platform metadata used for the
    /// cheap preflight.
    SizeChanged { declared: usize, actual: usize },
}

impl std::fmt::Display for ChatBinaryOperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownOperation(name) => {
                write!(f, "this live session does not offer operation {name:?}")
            }
            Self::DuplicateOperation(name) => {
                write!(f, "live operation name {name:?} is ambiguous")
            }
            Self::TooLarge { actual, maximum } => write!(
                f,
                "chat attachment is {actual} bytes; this operation accepts at most {maximum}"
            ),
            Self::SizeChanged { declared, actual } => write!(
                f,
                "chat attachment changed size during download ({declared} declared, {actual} received)"
            ),
        }
    }
}

impl std::error::Error for ChatBinaryOperationError {}

/// Select and preflight one operation from the exact live descriptor list.
///
/// The operation name is the trusted router chosen by the player's explicit
/// command; an attachment's MIME metadata is not an authentication input (both
/// Telegram and Discord derive it heuristically and clients cannot reliably
/// set vendor media types).  The expected media type remains visible in the
/// affordance, while the owning offering canonically decodes the bytes.
pub fn preflight_chat_binary_operation(
    operations: &[BinaryOperationDescriptor],
    name: &str,
    declared_bytes: usize,
) -> Result<ChatBinaryOperationPolicy, ChatBinaryOperationError> {
    let mut matches = operations
        .iter()
        .filter(|descriptor| descriptor.name == name);
    let Some(descriptor) = matches.next() else {
        return Err(ChatBinaryOperationError::UnknownOperation(name.to_string()));
    };
    if matches.next().is_some() {
        return Err(ChatBinaryOperationError::DuplicateOperation(
            name.to_string(),
        ));
    }
    let transport_max_bytes = descriptor
        .max_input_bytes
        .min(MAX_CHAT_BINARY_OPERATION_BYTES);
    if declared_bytes > transport_max_bytes {
        return Err(ChatBinaryOperationError::TooLarge {
            actual: declared_bytes,
            maximum: transport_max_bytes,
        });
    }
    Ok(ChatBinaryOperationPolicy {
        descriptor: descriptor.clone(),
        transport_max_bytes,
        declared_bytes,
    })
}

/// Public, non-secret output of a successfully applied operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryOperationReceipt {
    /// Stable operation identity that was applied.
    pub operation: String,
    /// Canonical public receipt/claim digest.
    pub receipt_id: [u8; 32],
    /// Small public result fields for surface rendering.
    pub public_fields: Vec<(String, String)>,
}

/// One operation that actually passed through an [`crate::OfferingHost`], bound to the exact
/// source session heads observed immediately before and after it.
///
/// This is the lower-level game-composition seam. A catalog or game spine can project it into its
/// own receipt vocabulary without teaching this substrate crate about a market, quest, or UI.
/// `actor` is the attribution supplied to the host operation; this type does not upgrade asserted
/// attribution into a signature. Signed frontends must verify before constructing the call.
/// Likewise, `session` is the host route and journal key observed around the invocation; a
/// concrete operation receipt need not cryptographically include that `SessionId`. A destination
/// requiring portable authority must reverify the source journal/proof, not trust this struct as a
/// free-standing signed credential.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AppliedBinaryOperation {
    /// Stable offering key at which the operation landed.
    pub offering: String,
    /// Exact hosted session at which it landed.
    pub session: SessionId,
    /// Operation attribution supplied by the owning frontend/adapter.
    pub actor: DreggIdentity,
    /// Host commitment immediately before the operation.
    pub before: Vec<u8>,
    /// Host commitment immediately after the operation.
    pub after: Vec<u8>,
    /// The concrete offering's public operation receipt.
    pub receipt: BinaryOperationReceipt,
}

/// A rule that turns one exact public operation result into a narrow one-shot consequence grant.
///
/// For example, the shielded preference result `plan = barter in the Dark Bazaar` may grant the
/// `dark-bazaar.enter.v1` endpoint. The rule never calls or depends on the market implementation;
/// the receiving organ implements [`OperationConsequenceEndpoint`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationConsequenceRule {
    source_operation: String,
    public_field: String,
    expected_value: String,
    destination: String,
}

impl OperationConsequenceRule {
    pub fn new(
        source_operation: impl Into<String>,
        public_field: impl Into<String>,
        expected_value: impl Into<String>,
        destination: impl Into<String>,
    ) -> Result<Self, OperationConsequenceError> {
        let rule = Self {
            source_operation: source_operation.into(),
            public_field: public_field.into(),
            expected_value: expected_value.into(),
            destination: destination.into(),
        };
        for (name, value) in [
            ("source operation", rule.source_operation.as_str()),
            ("public field", rule.public_field.as_str()),
            ("destination", rule.destination.as_str()),
        ] {
            if value.is_empty()
                || value.len() > 256
                || !value.bytes().all(|byte| {
                    byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_' | b':')
                })
            {
                return Err(OperationConsequenceError::InvalidRule(format!(
                    "{name} is not a bounded stable identifier"
                )));
            }
        }
        if rule.expected_value.is_empty() || rule.expected_value.len() > 1024 {
            return Err(OperationConsequenceError::InvalidRule(
                "expected public value is empty or overlong".to_string(),
            ));
        }
        Ok(rule)
    }

    /// Admit only an exact source operation with exactly one matching public result field.
    pub fn admit(
        &self,
        applied: &AppliedBinaryOperation,
    ) -> Result<OperationConsequenceGrant, OperationConsequenceError> {
        if applied.receipt.operation != self.source_operation {
            return Err(OperationConsequenceError::WrongSourceOperation {
                expected: self.source_operation.clone(),
                got: applied.receipt.operation.clone(),
            });
        }
        let mut values = applied
            .receipt
            .public_fields
            .iter()
            .filter(|(name, _)| name == &self.public_field)
            .map(|(_, value)| value);
        let Some(value) = values.next() else {
            return Err(OperationConsequenceError::MissingPublicField(
                self.public_field.clone(),
            ));
        };
        if values.next().is_some() {
            return Err(OperationConsequenceError::AmbiguousPublicField(
                self.public_field.clone(),
            ));
        }
        if value != &self.expected_value {
            return Err(OperationConsequenceError::WrongPublicValue {
                field: self.public_field.clone(),
                expected: self.expected_value.clone(),
                got: value.clone(),
            });
        }
        if applied.before == applied.after {
            return Err(OperationConsequenceError::UnchangedSourceHead);
        }
        let id = consequence_id(applied, &self.destination);
        Ok(OperationConsequenceGrant {
            id,
            destination: self.destination.clone(),
            source_offering: applied.offering.clone(),
            source_session: applied.session.clone(),
            source_operation: applied.receipt.operation.clone(),
            source_receipt_id: applied.receipt.receipt_id,
            actor: applied.actor.clone(),
            source_before: applied.before.clone(),
            source_after: applied.after.clone(),
        })
    }
}

/// A narrow, exact-source capability minted from an admitted operation consequence rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationConsequenceGrant {
    id: [u8; 32],
    destination: String,
    source_offering: String,
    source_session: SessionId,
    source_operation: String,
    source_receipt_id: [u8; 32],
    actor: DreggIdentity,
    source_before: Vec<u8>,
    source_after: Vec<u8>,
}

impl OperationConsequenceGrant {
    pub const fn id(&self) -> [u8; 32] {
        self.id
    }

    pub fn destination(&self) -> &str {
        &self.destination
    }

    pub fn actor(&self) -> &DreggIdentity {
        &self.actor
    }

    pub fn source_receipt_id(&self) -> [u8; 32] {
        self.source_receipt_id
    }

    pub fn source_offering(&self) -> &str {
        &self.source_offering
    }

    pub fn source_session(&self) -> &SessionId {
        &self.source_session
    }

    pub fn source_operation(&self) -> &str {
        &self.source_operation
    }

    pub fn source_heads(&self) -> (&[u8], &[u8]) {
        (&self.source_before, &self.source_after)
    }
}

/// A game/market organ that accepts one exact consequence grant.
///
/// Implementations still own their native executor and return their own operation receipt. This
/// interface only transports the narrow authorization; it never asks the source game to simulate
/// the destination's laws.
pub trait OperationConsequenceEndpoint {
    fn destination(&self) -> &str;

    fn apply(
        &mut self,
        grant: &OperationConsequenceGrant,
    ) -> Result<BinaryOperationReceipt, OperationConsequenceError>;
}

/// Process-local one-shot consumption book for consequence capabilities.
///
/// This is deliberately an in-memory coordination tooth. Recreating it after a process restart
/// forgets every consumed id and can re-enable a grant. A durable destination must persist/nullify
/// [`OperationConsequenceGrant::id`] in its own committed state (or restore this set from an exact
/// journal) before claiming restart-safe one-shot semantics.
#[derive(Clone, Debug, Default)]
pub struct OperationConsequenceBook {
    consumed: BTreeSet<[u8; 32]>,
}

impl OperationConsequenceBook {
    /// Apply a grant to the exact destination and actor, consuming it only after success.
    pub fn redeem<E: OperationConsequenceEndpoint>(
        &mut self,
        endpoint: &mut E,
        grant: &OperationConsequenceGrant,
        actor: &DreggIdentity,
    ) -> Result<BinaryOperationReceipt, OperationConsequenceError> {
        if &grant.actor != actor {
            return Err(OperationConsequenceError::WrongActor);
        }
        if endpoint.destination() != grant.destination {
            return Err(OperationConsequenceError::WrongDestination {
                expected: grant.destination.clone(),
                got: endpoint.destination().to_string(),
            });
        }
        if self.consumed.contains(&grant.id) {
            return Err(OperationConsequenceError::AlreadyConsumed);
        }
        let receipt = endpoint.apply(grant)?;
        if receipt.operation != grant.destination {
            return Err(OperationConsequenceError::WrongDestinationReceipt {
                expected: grant.destination.clone(),
                got: receipt.operation,
            });
        }
        self.consumed.insert(grant.id);
        Ok(receipt)
    }

    pub fn is_consumed(&self, grant: &OperationConsequenceGrant) -> bool {
        self.consumed.contains(&grant.id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationConsequenceError {
    InvalidRule(String),
    WrongSourceOperation {
        expected: String,
        got: String,
    },
    MissingPublicField(String),
    AmbiguousPublicField(String),
    WrongPublicValue {
        field: String,
        expected: String,
        got: String,
    },
    UnchangedSourceHead,
    WrongActor,
    WrongDestination {
        expected: String,
        got: String,
    },
    AlreadyConsumed,
    WrongDestinationReceipt {
        expected: String,
        got: String,
    },
    DestinationRefused(String),
}

impl std::fmt::Display for OperationConsequenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRule(reason) => write!(f, "invalid consequence rule: {reason}"),
            Self::WrongSourceOperation { expected, got } => {
                write!(f, "expected source operation {expected:?}, got {got:?}")
            }
            Self::MissingPublicField(field) => write!(f, "source receipt has no {field:?} field"),
            Self::AmbiguousPublicField(field) => {
                write!(f, "source receipt repeats public field {field:?}")
            }
            Self::WrongPublicValue {
                field,
                expected,
                got,
            } => write!(
                f,
                "source receipt field {field:?} must be {expected:?}, got {got:?}"
            ),
            Self::UnchangedSourceHead => {
                write!(
                    f,
                    "source operation did not change the hosted session commitment"
                )
            }
            Self::WrongActor => write!(f, "consequence belongs to a different actor"),
            Self::WrongDestination { expected, got } => {
                write!(f, "consequence targets {expected:?}, not {got:?}")
            }
            Self::AlreadyConsumed => write!(f, "consequence capability was already consumed"),
            Self::WrongDestinationReceipt { expected, got } => write!(
                f,
                "destination returned receipt {got:?}, expected {expected:?}"
            ),
            Self::DestinationRefused(reason) => write!(f, "destination refused: {reason}"),
        }
    }
}

impl std::error::Error for OperationConsequenceError {}

fn consequence_id(applied: &AppliedBinaryOperation, destination: &str) -> [u8; 32] {
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg.game-operation-consequence-capability.v1");
    hash_string(&mut hasher, &applied.offering);
    hash_string(&mut hasher, &applied.session.0);
    hash_string(&mut hasher, applied.actor.as_str());
    hash_string(&mut hasher, &applied.receipt.operation);
    hasher.update(&applied.receipt.receipt_id);
    hash_bytes(&mut hasher, &applied.before);
    hash_bytes(&mut hasher, &applied.after);
    hash_string(&mut hasher, destination);
    *hasher.finalize().as_bytes()
}

fn hash_string(hasher: &mut blake3::Hasher, value: &str) {
    hash_bytes(hasher, value.as_bytes());
}

fn hash_bytes(hasher: &mut blake3::Hasher, value: &[u8]) {
    hasher.update(
        &u64::try_from(value.len())
            .expect("the bounded operation value fits u64")
            .to_be_bytes(),
    );
    hasher.update(value);
}

/// Offering-selected material that is safe to place in the durable operation
/// journal and sufficient to re-verify/re-apply the operation after restart.
///
/// This is deliberately not inferred from the request body by the host. An
/// opaque upload may contain private witness material, decryption shares, or
/// credentials even when its result is public. The concrete offering must
/// explicitly opt in and name exactly what the journal retains. The bytes are
/// never returned to a frontend or included in a rendered receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryOperationReplayMaterial {
    /// Canonical offering-owned bytes used only by restart replay.
    pub bytes: Vec<u8>,
    /// Exact human-readable disclosure of what these bytes contain and omit.
    pub disclosure: String,
    /// `true` when `bytes` are the canonical original request itself. The host
    /// then requires the request and replay digests to be identical on resume.
    /// A smaller typed snapshot sets this `false` and must override the
    /// offering's replay-material validation hook.
    pub is_canonical_request: bool,
}

impl BinaryOperationReplayMaterial {
    /// Retain the canonical request after the offering has established that it
    /// contains no material forbidden from durable storage.
    pub fn new(bytes: Vec<u8>, disclosure: impl Into<String>) -> Self {
        Self {
            bytes,
            disclosure: disclosure.into(),
            is_canonical_request: true,
        }
    }

    /// Retain a smaller offering-owned snapshot instead of the original
    /// request. The offering must also override replay-material validation and
    /// restoration so this typed representation is independently checked.
    pub fn typed_snapshot(bytes: Vec<u8>, disclosure: impl Into<String>) -> Self {
        Self {
            bytes,
            disclosure: disclosure.into(),
            is_canonical_request: false,
        }
    }
}

/// A concrete offering's refusal after the host has found the addressed live
/// session.  Routing misses stay [`crate::host::HostOperationError`] variants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOperationError {
    /// This offering/session does not publish the requested operation.
    UnknownOperation(String),
    /// The owning binary payload did not decode canonically.
    Malformed(String),
    /// The payload decoded, but its proof/state/session gate refused it.
    Refused(String),
}

impl std::fmt::Display for BinaryOperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownOperation(name) => write!(f, "unknown binary operation {name:?}"),
            Self::Malformed(reason) => write!(f, "malformed operation payload: {reason}"),
            Self::Refused(reason) => write!(f, "operation refused: {reason}"),
        }
    }
}

impl std::error::Error for BinaryOperationError {}

/// Result of the one journal-aware opaque-operation transaction shared by
/// [`crate::OfferingHost`] and typed frontend session stores.
///
/// `Quarantine` is deliberately distinct from an ordinary refusal: the
/// concrete offering already returned success and may have mutated, but the
/// returned receipt cannot safely be associated with the addressed operation
/// (or could not be written through to an attached durable journal). The
/// caller must make that live session unobservable before returning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JournaledBinaryOperation {
    /// The operation landed and every applicable journal write completed.
    Applied(BinaryOperationReceipt),
    /// Nothing authoritative landed; the live session remains usable.
    Refused(BinaryOperationError),
    /// Mutation may have occurred but cannot safely remain live.
    Quarantine(BinaryOperationError),
}

/// Apply one concrete offering operation under the host's exact durable
/// journal policy.
///
/// The caller obtains `replay_material` from the live offering *before*
/// mutation, and supplies the sole decoder/mutator as `invoke`. This function
/// then owns the shared transaction law:
///
/// 1. an attached durable store requires offering-approved replay material and
///    binary-operation support;
/// 2. the ordinary-move cursor is fixed before mutation;
/// 3. a successful receipt must name exactly the addressed operation;
/// 4. the operation is appended to the in-memory timeline and written through
///    to the attached store;
/// 5. any post-mutation name confusion or write-through failure returns
///    [`JournaledBinaryOperation::Quarantine`].
///
/// Keeping this transaction outside either frontend prevents Discord,
/// Telegram, web, or the type-erased host from growing subtly different replay
/// and quarantine rules.
pub fn invoke_journaled_binary_operation(
    key: &str,
    id: &SessionId,
    name: &str,
    payload: &[u8],
    actor: DreggIdentity,
    log: &mut SessionMoveLog,
    store: Option<&dyn SessionResumeStore>,
    replay_material: Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError>,
    invoke: impl FnOnce() -> Result<BinaryOperationReceipt, BinaryOperationError>,
) -> JournaledBinaryOperation {
    let replay_material = match replay_material {
        Ok(material) => material,
        Err(error) => return JournaledBinaryOperation::Refused(error),
    };
    if let Some(store) = store {
        if replay_material.is_none() {
            return JournaledBinaryOperation::Refused(BinaryOperationError::Refused(
                "durable host refuses an operation without offering-selected safe replay material"
                    .to_string(),
            ));
        }
        if !store.supports_binary_operations() {
            return JournaledBinaryOperation::Refused(BinaryOperationError::Refused(
                "attached resume store does not support the binary-operation journal".to_string(),
            ));
        }
    }
    let after_moves = match u64::try_from(log.moves.len()) {
        Ok(cursor) => cursor,
        Err(_) => {
            return JournaledBinaryOperation::Refused(BinaryOperationError::Refused(
                "ordinary-move cursor exceeds the durable operation wire".to_string(),
            ));
        }
    };
    let receipt = match invoke() {
        Ok(receipt) => receipt,
        Err(error) => return JournaledBinaryOperation::Refused(error),
    };
    if receipt.operation != name {
        return JournaledBinaryOperation::Quarantine(BinaryOperationError::Refused(format!(
            "operation receipt named {:?}, but the host addressed {name:?}; session quarantined",
            receipt.operation
        )));
    }

    if let Some(material) = replay_material {
        let operation = LoggedBinaryOperation {
            after_moves,
            name: name.to_string(),
            actor,
            payload_digest: *blake3::hash(payload).as_bytes(),
            replay_digest: *blake3::hash(&material.bytes).as_bytes(),
            replay_material: material.bytes,
            replay_disclosure: material.disclosure,
            replay_is_canonical_request: material.is_canonical_request,
            receipt: receipt.clone(),
        };
        if let Some(store) = store {
            if !store.record_binary_operation(key, id, &operation) {
                // Keep the caller's in-memory journal at the exact pre-operation
                // image too. A quarantined session must not become resumable from
                // a ghost row merely because this process is still alive.
                return JournaledBinaryOperation::Quarantine(BinaryOperationError::Refused(
                    "durable operation journal write failed after mutation; session quarantined"
                        .to_string(),
                ));
            }
        }
        log.record_binary_operation(operation);
    }
    JournaledBinaryOperation::Applied(receipt)
}

#[cfg(test)]
mod journal_transaction_tests {
    use super::*;
    use crate::{Action, SessionConfig};

    struct RefusingOperationStore;

    impl SessionResumeStore for RefusingOperationStore {
        fn record_open(&self, _key: &str, _id: &SessionId, _cfg: &SessionConfig) {}

        fn record_landed(
            &self,
            _key: &str,
            _id: &SessionId,
            _action: &Action,
            _actor: &DreggIdentity,
        ) {
        }

        fn supports_binary_operations(&self) -> bool {
            true
        }

        fn record_binary_operation(
            &self,
            _key: &str,
            _id: &SessionId,
            _operation: &LoggedBinaryOperation,
        ) -> bool {
            false
        }

        fn forget(&self, _key: &str, _id: &SessionId) {}

        fn load(&self, _key: &str, _id: &SessionId) -> Option<SessionMoveLog> {
            None
        }

        fn all(&self) -> Vec<SessionMoveLog> {
            Vec::new()
        }
    }

    #[test]
    fn durable_write_failure_quarantines_without_ghosting_the_live_log() {
        let id = SessionId::new("write-failure");
        let mut log = SessionMoveLog::new("fixture", id.clone(), SessionConfig::default());
        let result = invoke_journaled_binary_operation(
            "fixture",
            &id,
            "apply.v1",
            &[7],
            DreggIdentity("alice".to_string()),
            &mut log,
            Some(&RefusingOperationStore),
            Ok(Some(BinaryOperationReplayMaterial::new(
                vec![7],
                "the canonical public request",
            ))),
            || {
                Ok(BinaryOperationReceipt {
                    operation: "apply.v1".to_string(),
                    receipt_id: [9; 32],
                    public_fields: Vec::new(),
                })
            },
        );

        assert!(matches!(result, JournaledBinaryOperation::Quarantine(_)));
        assert!(
            log.operations.is_empty(),
            "the in-process replay source must remain at the exact pre-operation image"
        );
    }
}
