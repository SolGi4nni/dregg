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
