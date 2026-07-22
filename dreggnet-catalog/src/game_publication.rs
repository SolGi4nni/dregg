//! A viewer-blind publication form for common-spine game receipts.
//!
//! A [`GameReceipt`](crate::GameReceipt) is an execution object.  It retains the
//! exact action or operation route, actor attribution, payload commitment, and
//! state heads needed to audit routing.  Those are useful inside the host, but
//! they are the wrong default object for a shared Discord message, public web
//! page, or cross-game activity rail: a turn may have come from a private
//! affordance and an asserted actor label is not public just because the host
//! knows it.
//!
//! [`project_public_game_receipt`] therefore publishes one deliberately small
//! grammar across Descent, Dungeon, Chutes-hosted operations, and the Bazaar:
//! the distinct game family, an opaque exact-session route commitment, the
//! bound receipt commitment, identity-free attribution provenance, and audited
//! public result fields.  It never copies actor identities, raw session names,
//! action arguments/text, operation names, payload digests, or before/after
//! state heads.  The concrete games keep their own interpreters and receipts;
//! this is only their common publication boundary.

use std::collections::{BTreeMap, BTreeSet};

use dreggnet_offerings::Attribution;

use crate::{GameKind, GameReceipt, GameSessionBinding, GameSessionRef};

/// Maximum number of fields an owning operation may present to the shared
/// publication boundary.
pub const MAX_PUBLIC_GAME_FIELDS: usize = 64;

/// Maximum UTF-8 byte length of one audited public result value.
pub const MAX_PUBLIC_GAME_FIELD_VALUE_BYTES: usize = 4 * 1024;

macro_rules! public_game_fields {
    ($( $variant:ident => $wire:literal ),+ $(,)?) => {
        /// An audited public result carrier shared by the real game operations.
        ///
        /// This is an exact allowlist. A newly named operation field remains
        /// host-local until this enum is deliberately extended.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum PublicGameField {
            $( $variant, )+
        }

        impl PublicGameField {
            /// Stable wire spelling authored by the owning operation receipt.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $( Self::$variant => $wire, )+
                }
            }

            fn from_name(name: &str) -> Option<Self> {
                match name {
                    $( $wire => Some(Self::$variant), )+
                    _ => None,
                }
            }
        }
    };
}

public_game_fields! {
    AcceptedSwaps => "acceptedSwaps",
    CommittedSequence => "committedSequence",
    DecisionBundleDigest => "decisionBundleDigest",
    DecisionClaimDigest => "decisionClaimDigest",
    DecisionTaskDigest => "decisionTaskDigest",
    Ended => "ended",
    NarrationCommit => "narrationCommit",
    NextSequence => "nextSequence",
    Phase => "phase",
    ProofDigest => "proofDigest",
    PublicHostMaterialDigest => "publicHostMaterialDigest",
    ReplaySlotsConsumed => "replaySlotsConsumed",
    RequestDigest => "requestDigest",
    SameOpeningClaimDigest => "sameOpeningClaimDigest",
    Sequence => "sequence",
    StatementDigest => "statementDigest",
}

/// One typed, audited field copied from an operation's public result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicGameFieldValue {
    pub field: PublicGameField,
    pub value: String,
}

/// Honest trust provenance without publishing the actor identity itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicGameAttribution {
    /// The ordinary turn traversed the common spine's verified signed path.
    /// This does not make any claim about post-quantum security or key custody.
    Signed,
    /// The adapter supplied an actor label without a signature at this seam.
    Asserted,
}

impl From<&Attribution> for PublicGameAttribution {
    fn from(attribution: &Attribution) -> Self {
        match attribution {
            Attribution::Signed { .. } => Self::Signed,
            Attribution::Asserted { .. } => Self::Asserted,
        }
    }
}

/// The result shape safe to share without replaying a private projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PublicGameReceiptResult {
    /// A concrete game's ordinary executor accepted one turn.  The turn route
    /// is intentionally absent because it may have been a private affordance.
    Turn { ended: bool },
    /// A proof-/attestation-bearing operation landed.  Its raw route and
    /// transport envelope remain absent; only audited public fields cross.
    Operation { fields: Vec<PublicGameFieldValue> },
}

/// A minimal common receipt card for shared/public game surfaces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicGameReceipt {
    /// The concrete ruleset family remains visible; Dungeon never becomes
    /// Bazaar merely because both use this publication grammar.
    pub kind: GameKind,
    /// Opaque commitment to offering + raw session id + host incarnation +
    /// session generation.  It links one exact session without exposing its
    /// route components.
    pub session_route_id: [u8; 32],
    /// The complete existing common-spine router receipt commitment.
    pub receipt_id: [u8; 32],
    /// Commitment to this exact safe projection.  This is a publication
    /// identity, not a replacement for the concrete game's receipt verifier.
    pub publication_id: [u8; 32],
    pub attribution: PublicGameAttribution,
    pub result: PublicGameReceiptResult,
}

impl PublicGameReceipt {
    /// Recompute the projection commitment after storage or transport.
    ///
    /// This proves only that the public card is internally unchanged. The
    /// original concrete receipt and game verifier remain the authority that
    /// the operation or turn actually landed.
    pub fn binding_verifies(&self) -> bool {
        self.publication_id
            == publication_id(
                self.kind,
                self.session_route_id,
                self.receipt_id,
                self.attribution,
                &self.result,
            )
    }

    /// Validate both the publication commitment and the canonical typed field
    /// shape expected after storage/transport.
    pub fn validate(&self) -> Result<(), GamePublicationError> {
        if !self.binding_verifies() {
            return Err(GamePublicationError::InvalidPublicationBinding);
        }
        let PublicGameReceiptResult::Operation { fields } = &self.result else {
            return Ok(());
        };
        if fields.len() > MAX_PUBLIC_GAME_FIELDS {
            return Err(GamePublicationError::TooManyFields {
                actual: fields.len(),
                maximum: MAX_PUBLIC_GAME_FIELDS,
            });
        }
        let mut previous = None;
        for field in fields {
            if previous.is_some_and(|prior| prior >= field.field) {
                return Err(GamePublicationError::NonCanonicalProjection);
            }
            if field.value.len() > MAX_PUBLIC_GAME_FIELD_VALUE_BYTES {
                return Err(GamePublicationError::FieldValueTooLarge {
                    field: field.field,
                    actual: field.value.len(),
                    maximum: MAX_PUBLIC_GAME_FIELD_VALUE_BYTES,
                });
            }
            if !field_value_is_canonical(field.field, &field.value) {
                return Err(GamePublicationError::NonCanonicalProjection);
            }
            previous = Some(field.field);
        }
        Ok(())
    }
}

/// Refusal at the common public-receipt boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GamePublicationError {
    /// Legacy two-field routes cannot distinguish host replacement or a
    /// close/reopen generation, so they are unsuitable for a durable feed.
    UnboundSession,
    /// A receipt field covered by the common router commitment was changed.
    InvalidRoutingBinding,
    /// The public card was changed without retaining its projection
    /// commitment.
    InvalidPublicationBinding,
    /// Typed public fields must be sorted and unique.
    NonCanonicalProjection,
    /// The owning operation presented an unreasonable publication surface.
    TooManyFields { actual: usize, maximum: usize },
    /// An otherwise-audited public field is too large to publish atomically.
    FieldValueTooLarge {
        field: PublicGameField,
        actual: usize,
        maximum: usize,
    },
}

impl std::fmt::Display for GamePublicationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundSession => write!(
                f,
                "public game receipts require an exact host/session authority epoch"
            ),
            Self::InvalidRoutingBinding => {
                write!(f, "game receipt no longer matches its router commitment")
            }
            Self::InvalidPublicationBinding => {
                write!(
                    f,
                    "public game receipt no longer matches its publication commitment"
                )
            }
            Self::NonCanonicalProjection => {
                write!(f, "public game receipt fields are not sorted and unique")
            }
            Self::TooManyFields { actual, maximum } => write!(
                f,
                "game receipt presents {actual} public fields; maximum is {maximum}"
            ),
            Self::FieldValueTooLarge {
                field,
                actual,
                maximum,
            } => write!(
                f,
                "public game field {:?} is {actual} bytes; maximum is {maximum}",
                field.as_str()
            ),
        }
    }
}

impl std::error::Error for GamePublicationError {}

/// Convert one landed common-spine receipt into the viewer-blind public form.
///
/// Unknown operation fields are omitted. Two occurrences of the same audited
/// name are ambiguous and both are omitted, so vector order never decides the
/// value a public viewer sees. Bounds and receipt integrity fail closed.
pub fn project_public_game_receipt(
    receipt: &GameReceipt,
) -> Result<PublicGameReceipt, GamePublicationError> {
    if !receipt.routing_binding_valid() {
        return Err(GamePublicationError::InvalidRoutingBinding);
    }
    let session_route_id = session_route_id(receipt.session())?;
    let kind = receipt.session().kind();
    let receipt_id = receipt.receipt_id();
    let attribution = PublicGameAttribution::from(receipt.attribution());

    let result = match receipt {
        GameReceipt::Turn { ended, .. } => PublicGameReceiptResult::Turn { ended: *ended },
        GameReceipt::Operation { public_fields, .. } => {
            if public_fields.len() > MAX_PUBLIC_GAME_FIELDS {
                return Err(GamePublicationError::TooManyFields {
                    actual: public_fields.len(),
                    maximum: MAX_PUBLIC_GAME_FIELDS,
                });
            }
            let mut fields = BTreeMap::<PublicGameField, String>::new();
            let mut ambiguous = BTreeSet::new();
            let operation_name = match receipt {
                GameReceipt::Operation { operation, .. } => operation.operation.as_str(),
                GameReceipt::Turn { .. } => unreachable!("operation arm selected above"),
            };
            for (name, value) in public_fields {
                let Some(field) = PublicGameField::from_name(name) else {
                    continue;
                };
                if !operation_allows_field(kind, operation_name, field) {
                    continue;
                }
                if value.len() > MAX_PUBLIC_GAME_FIELD_VALUE_BYTES {
                    return Err(GamePublicationError::FieldValueTooLarge {
                        field,
                        actual: value.len(),
                        maximum: MAX_PUBLIC_GAME_FIELD_VALUE_BYTES,
                    });
                }
                if !field_value_is_canonical(field, value) {
                    continue;
                }
                if ambiguous.contains(&field) {
                    continue;
                }
                if fields.insert(field, value.clone()).is_some() {
                    fields.remove(&field);
                    ambiguous.insert(field);
                }
            }
            PublicGameReceiptResult::Operation {
                fields: fields
                    .into_iter()
                    .map(|(field, value)| PublicGameFieldValue { field, value })
                    .collect(),
            }
        }
    };

    let publication_id = publication_id(kind, session_route_id, receipt_id, attribution, &result);
    Ok(PublicGameReceipt {
        kind,
        session_route_id,
        receipt_id,
        publication_id,
        attribution,
        result,
    })
}

/// Exact operation-context policy for the deliberately small shared default.
///
/// `BinaryOperationReceipt::public_fields` is authored by independent rule
/// engines. A global field-name allowlist is insufficient: a new private
/// operation could call a witness `winner` or even reuse a commitment-looking
/// name. Unknown routes therefore publish no fields. Known routes publish only
/// the minimal status/proof commitments needed by a public activity rail.
fn operation_allows_field(kind: GameKind, operation: &str, field: PublicGameField) -> bool {
    use PublicGameField as F;
    match (kind, operation) {
        (GameKind::Dungeon, "dungeon.chutes-narrated-turn.v1") => {
            matches!(field, F::NarrationCommit | F::Ended)
        }
        (GameKind::DarkPool, "dark-bazaar.private-amm-swap.v1") => {
            matches!(field, F::Sequence | F::RequestDigest | F::AcceptedSwaps)
        }
        (GameKind::DarkPool, "dark-bazaar.private-amm-swap.proved.v2") => matches!(
            field,
            F::Sequence | F::StatementDigest | F::ProofDigest | F::RequestDigest | F::AcceptedSwaps
        ),
        (GameKind::DarkPool, "dark-bazaar.private-amm-swap.proved.same-opening.v3") => matches!(
            field,
            F::Sequence
                | F::StatementDigest
                | F::ProofDigest
                | F::SameOpeningClaimDigest
                | F::RequestDigest
                | F::AcceptedSwaps
        ),
        (GameKind::DarkPool, "dark-amm.collective-stage.v1") => matches!(
            field,
            F::Phase
                | F::Sequence
                | F::DecisionTaskDigest
                | F::SameOpeningClaimDigest
                | F::RequestDigest
        ),
        (GameKind::DarkPool, "dark-amm.collective-commit.v1") => matches!(
            field,
            F::Phase
                | F::CommittedSequence
                | F::NextSequence
                | F::PublicHostMaterialDigest
                | F::SameOpeningClaimDigest
                | F::DecisionClaimDigest
                | F::DecisionBundleDigest
        ),
        (GameKind::DarkPool, "dark-amm.collective-abandon.v1") => matches!(
            field,
            F::Phase
                | F::Sequence
                | F::DecisionTaskDigest
                | F::SameOpeningClaimDigest
                | F::ReplaySlotsConsumed
        ),
        _ => false,
    }
}

fn field_value_is_canonical(field: PublicGameField, value: &str) -> bool {
    use PublicGameField as F;
    match field {
        F::DecisionBundleDigest
        | F::DecisionClaimDigest
        | F::DecisionTaskDigest
        | F::NarrationCommit
        | F::ProofDigest
        | F::PublicHostMaterialDigest
        | F::RequestDigest
        | F::SameOpeningClaimDigest
        | F::StatementDigest => {
            value.len() == 64
                && value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        }
        F::Phase => matches!(
            value,
            "awaiting-authority-decision" | "committed" | "abandoned"
        ),
        F::Ended => matches!(value, "true" | "false"),
        F::AcceptedSwaps
        | F::CommittedSequence
        | F::NextSequence
        | F::ReplaySlotsConsumed
        | F::Sequence => value
            .parse::<u64>()
            .is_ok_and(|number| number.to_string() == value),
    }
}

fn hash_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn session_route_id(session: &GameSessionRef) -> Result<[u8; 32], GamePublicationError> {
    let GameSessionBinding::Bound {
        host_incarnation,
        session_generation,
    } = session.binding()
    else {
        return Err(GamePublicationError::UnboundSession);
    };
    let mut hasher = blake3::Hasher::new_derive_key("dregg.public-game-session-route.v1");
    hash_field(&mut hasher, session.offering().as_bytes());
    hash_field(&mut hasher, session.session_id().0.as_bytes());
    hash_field(&mut hasher, host_incarnation.as_bytes());
    hash_field(&mut hasher, &session_generation.to_be_bytes());
    Ok(*hasher.finalize().as_bytes())
}

fn publication_id(
    kind: GameKind,
    session_route_id: [u8; 32],
    receipt_id: [u8; 32],
    attribution: PublicGameAttribution,
    result: &PublicGameReceiptResult,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg.public-game-receipt.v1");
    hash_field(&mut hasher, kind.as_str().as_bytes());
    hash_field(&mut hasher, &session_route_id);
    hash_field(&mut hasher, &receipt_id);
    hash_field(
        &mut hasher,
        &[match attribution {
            PublicGameAttribution::Signed => 1,
            PublicGameAttribution::Asserted => 0,
        }],
    );
    match result {
        PublicGameReceiptResult::Turn { ended } => {
            hash_field(&mut hasher, &[0]);
            hash_field(&mut hasher, &[u8::from(*ended)]);
        }
        PublicGameReceiptResult::Operation { fields } => {
            hash_field(&mut hasher, &[1]);
            for field in fields {
                hash_field(&mut hasher, field.field.as_str().as_bytes());
                hash_field(&mut hasher, field.value.as_bytes());
            }
        }
    }
    *hasher.finalize().as_bytes()
}
