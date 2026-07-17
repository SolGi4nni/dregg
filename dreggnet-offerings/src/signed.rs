//! # `signed` — SIGNED ATTRIBUTION: a turn's actor as a VERIFIED public key.
//!
//! On the plain [`advance`](crate::Offering::advance) path the actor is **attribution
//! metadata**: a [`DreggIdentity`] is a `String` the frontend asserts, no signature is ever
//! consumed, and any legal move can be made AS anyone who can name the string. This module adds
//! the missing consumer — the seam where an actor's key actually SIGNS the turn it is attributed
//! to — while making the trust level of every attribution visible instead of implicit:
//!
//! * [`Attribution`] — the visible trust level. [`Attribution::Signed`] means the actor identity
//!   is an Ed25519 public key that VERIFIED over this turn; [`Attribution::Asserted`] means the
//!   identity is a frontend-asserted label (every pre-existing surface). Both flow into the same
//!   [`DreggIdentity`] the core already attributes moves to, so nothing downstream changes shape.
//! * [`SignedAction`] — an [`Action`] plus the signer's public key, a replay counter, and an
//!   Ed25519 signature over the canonical [`signing_message`].
//! * [`verify_signed`] — the verifier: a forged signature is [`SignedError::BadSignature`], a
//!   replayed counter is [`SignedError::StaleCounter`], an unparseable key is
//!   [`SignedError::MalformedKey`]. On success it yields the verified [`DreggIdentity`] (the
//!   canonical lowercase public-key hex — the SAME handle the discord/telegram/wechat
//!   cipherclerks derive, so a signed actor and a custodially-attributed actor with the same key
//!   are the SAME identity).
//! * [`TurnSigner`] — the signing half, on the SAME primitive the adapters' cipherclerks use
//!   (`dregg_types::SigningKey::from_bytes` is exactly `AgentCipherclerk::from_key_bytes`'s
//!   derivation), so a key seeded the way `dreggnet-telegram`'s `seed_for` seeds one signs turns
//!   that verify against the identity that frontend already attributes.
//!
//! The host-side consumer is [`OfferingHost::advance_signed`](crate::OfferingHost::advance_signed)
//! (verify → delegate to the existing advance path → record the landed move with `Signed`
//! provenance); the session-key binding is [`crate::session::open_session_signed`] (a grant
//! minted for a signed holder refuses play driven under a different key).
//!
//! ## Honest resolution: rung 1 of 2
//!
//! This is **rung 1** of the signed-identity ladder (`docs/EXCELLENCE-BACKLOG-2026-07-16.md`
//! §G1): the core VERB exists — a turn can require a real signature by the actor it is
//! attributed to, replay-protected, and every attribution carries its trust level. What rung 1
//! does NOT change: who HOLDS the keys. Today the adapters derive custodial keys (bot secret →
//! every user's key), so a signed turn on those surfaces proves "the custodian's derivation of
//! this user signed", not "a device only the user controls signed". **Rung 2** is browser/
//! device-held keys — cipherclerk-in-wasm (the SDK's `AgentCipherclerk` + the existing
//! `SessionKey` grant envelope) or WebAuthn — feeding this SAME verifier; nothing in this module
//! needs to change for it, only where the secret lives.

use dregg_types::{PublicKey, Signature, SigningKey};

use crate::{Action, DreggIdentity, SessionId};

// ─────────────────────────────────────────────────────────────────────────────
// ATTRIBUTION — the visible trust level of an actor identity.
// ─────────────────────────────────────────────────────────────────────────────

/// **The trust level of an actor attribution** — was the actor identity VERIFIED (an Ed25519
/// public key that signed this very turn) or merely ASSERTED (a frontend-supplied label, the
/// pre-existing behavior of every surface)? Both resolve to the same [`DreggIdentity`] handle
/// the core attributes moves to; this enum is the provenance that used to be implicit (and
/// implicitly `Asserted`) made first-class and visible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Attribution {
    /// The actor is a **verified Ed25519 public key**: this exact key signed the turn it is
    /// attributed to ([`verify_signed`] passed). `pubkey_hex` is the canonical lowercase hex of
    /// the 32-byte key — identical to the [`DreggIdentity`] string the turn was attributed to.
    Signed {
        /// The verified signer's public key, lowercase hex (64 chars).
        pubkey_hex: String,
    },
    /// The actor is a **frontend-asserted label** — no signature was consumed. This is every
    /// legacy attribution (`"web:alice"`, a blake3 handle, a custodial pubkey hex used *without*
    /// signing): honest about exactly what it always was.
    Asserted {
        /// The asserted identity string, verbatim.
        label: String,
    },
}

impl Attribution {
    /// The [`DreggIdentity`] this attribution resolves to — the same opaque handle either way;
    /// the enum variant is the trust level riding beside it.
    pub fn identity(&self) -> DreggIdentity {
        match self {
            Attribution::Signed { pubkey_hex } => DreggIdentity(pubkey_hex.clone()),
            Attribution::Asserted { label } => DreggIdentity(label.clone()),
        }
    }

    /// Whether this attribution was cryptographically verified ([`Attribution::Signed`]).
    pub fn is_signed(&self) -> bool {
        matches!(self, Attribution::Signed { .. })
    }
}

/// A bare [`DreggIdentity`] converts to an **asserted** attribution — the honest default for
/// every legacy string identity. A `Signed` attribution is never minted by conversion; only a
/// successful [`verify_signed`] earns one.
impl From<DreggIdentity> for Attribution {
    fn from(id: DreggIdentity) -> Self {
        Attribution::Asserted { label: id.0 }
    }
}

/// An attribution converts back to the [`DreggIdentity`] it resolves to (dropping the trust
/// level — the lossy direction, for handing to actor-typed seams).
impl From<Attribution> for DreggIdentity {
    fn from(a: Attribution) -> Self {
        a.identity()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SIGNED ACTION + the canonical signing message.
// ─────────────────────────────────────────────────────────────────────────────

/// **A signature-carrying move** — an [`Action`] plus everything needed to verify WHO fired it:
/// the signer's public key, a strictly-increasing replay counter, and an Ed25519 signature over
/// the canonical [`signing_message`] (which binds the offering, the session, the counter, and
/// the action's executor-resolved fields). The payload
/// [`OfferingHost::advance_signed`](crate::OfferingHost::advance_signed) admits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedAction {
    /// The move being fired (the same typed [`Action`] the unsigned path resolves).
    pub action: Action,
    /// The signer's Ed25519 public key, hex (64 hex chars = 32 bytes; case-insensitive on
    /// verify, canonicalized to lowercase in the verified identity).
    pub actor_pubkey_hex: String,
    /// The replay counter — strictly increasing per `(offering, session, pubkey)`. The host
    /// tracks the last consumed value and refuses a counter at or below it
    /// ([`SignedError::StaleCounter`]), so a captured envelope cannot be replayed.
    pub counter: u64,
    /// The Ed25519 signature over [`signing_message`]`(offering_key, session, counter, action)`.
    pub signature: [u8; 64],
}

/// The domain tag every offering-turn signature is bound under — no signature over this domain
/// can be confused with a ballot, a delegation, or any other signed object in the system.
pub const TURN_SIGNING_DOMAIN: &[u8] = b"dregg-offering-turn-v1:";

/// **The canonical signing message** — the ONE byte layout both [`TurnSigner::sign`] and
/// [`verify_signed`] use (a signer/verifier fork here would be a silent wire split; the
/// pin test on this function makes drift a red test instead):
///
/// ```text
/// "dregg-offering-turn-v1:" ‖ offering_key ‖ 0x00 ‖ session_id ‖ 0x00
///   ‖ counter_le(8) ‖ 0x00 ‖ action.turn ‖ 0x00 ‖ action.arg_le(8) ‖ 0x00 ‖ action.text-or-empty
/// ```
///
/// It binds exactly the fields the executor resolves — the offering, the session, the replay
/// counter, and the action's `{turn, arg, text}`. `label` and `enabled` are deliberately NOT
/// signed: they are surface decorations (the executor never reads them), and signing them would
/// let a cosmetic re-label invalidate an otherwise-identical move.
pub fn signing_message(
    offering_key: &str,
    session: &SessionId,
    counter: u64,
    action: &Action,
) -> Vec<u8> {
    let text = action.text.as_deref().unwrap_or("");
    let mut m = Vec::with_capacity(
        TURN_SIGNING_DOMAIN.len()
            + offering_key.len()
            + session.0.len()
            + action.turn.len()
            + text.len()
            + 8
            + 8
            + 5,
    );
    m.extend_from_slice(TURN_SIGNING_DOMAIN);
    m.extend_from_slice(offering_key.as_bytes());
    m.push(0);
    m.extend_from_slice(session.0.as_bytes());
    m.push(0);
    m.extend_from_slice(&counter.to_le_bytes());
    m.push(0);
    m.extend_from_slice(action.turn.as_bytes());
    m.push(0);
    m.extend_from_slice(&action.arg.to_le_bytes());
    m.push(0);
    m.extend_from_slice(text.as_bytes());
    m
}

// ─────────────────────────────────────────────────────────────────────────────
// VERIFICATION — the fail-closed gate.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a [`SignedAction`] was REFUSED — each variant one fail-closed leg of [`verify_signed`],
/// named so an audit sees which gate bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignedError {
    /// `actor_pubkey_hex` is not 64 hex characters (32 bytes). (A well-formed 32-byte string
    /// that is not a valid curve point fails signature verification instead —
    /// [`SignedError::BadSignature`] — because no signature can verify under it.)
    MalformedKey,
    /// The replay counter is not strictly newer than the last one consumed for this
    /// `(offering, session, pubkey)` — a replayed (or reordered-stale) envelope.
    StaleCounter {
        /// The counter the envelope presented.
        presented: u64,
        /// The lowest counter the verifier would accept.
        expected: u64,
    },
    /// The Ed25519 signature did not verify over the canonical [`signing_message`] under the
    /// presented key — forged, tampered, cross-session/cross-offering spliced, or signed by a
    /// different key than claimed.
    BadSignature,
}

impl std::fmt::Display for SignedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignedError::MalformedKey => {
                write!(f, "actor public key is not 32 bytes of hex")
            }
            SignedError::StaleCounter {
                presented,
                expected,
            } => write!(
                f,
                "stale replay counter: presented {presented}, expected at least {expected}"
            ),
            SignedError::BadSignature => {
                write!(
                    f,
                    "signature did not verify over the canonical turn message"
                )
            }
        }
    }
}

impl std::error::Error for SignedError {}

/// **Verify a [`SignedAction`]** against the offering/session it claims to move and the lowest
/// acceptable replay counter. Fail-closed, cheapest gate first:
///
/// 1. the key must be 32 bytes of hex ([`SignedError::MalformedKey`]);
/// 2. `sa.counter >= expected_counter` ([`SignedError::StaleCounter`]) — the caller (the host)
///    supplies `expected_counter = last_consumed + 1` (or `0` for a first use) and consumes
///    `sa.counter` on success, making counters strictly increasing per
///    `(offering, session, pubkey)`;
/// 3. the Ed25519 signature must verify (strict — non-canonical S refused) over
///    [`signing_message`]`(offering_key, session, sa.counter, sa.action)` under the presented
///    key ([`SignedError::BadSignature`]).
///
/// On success returns the **verified** [`DreggIdentity`]: the canonical lowercase hex of the
/// key — byte-identical to the identity the adapters' cipherclerks derive for the same key, so
/// signed and custodial attributions of one actor collapse to one identity.
pub fn verify_signed(
    offering_key: &str,
    session: &SessionId,
    expected_counter: u64,
    sa: &SignedAction,
) -> Result<DreggIdentity, SignedError> {
    let key_bytes = decode_hex_32(&sa.actor_pubkey_hex).ok_or(SignedError::MalformedKey)?;
    if sa.counter < expected_counter {
        return Err(SignedError::StaleCounter {
            presented: sa.counter,
            expected: expected_counter,
        });
    }
    let msg = signing_message(offering_key, session, sa.counter, &sa.action);
    let pk = PublicKey(key_bytes);
    if !dregg_types::verify(&pk, &msg, &Signature(sa.signature)) {
        return Err(SignedError::BadSignature);
    }
    Ok(DreggIdentity(pk.hex()))
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SIGNER — the same primitive the adapters' cipherclerks hold.
// ─────────────────────────────────────────────────────────────────────────────

/// **The signing half of the seam** — holds an Ed25519 secret and produces [`SignedAction`]s
/// over the canonical [`signing_message`]. Built on `dregg_types::SigningKey::from_bytes`, which
/// is byte-for-byte the derivation inside the SDK's `AgentCipherclerk::from_key_bytes` — so a
/// `TurnSigner` seeded with an adapter's custodial seed signs turns that verify against the
/// EXACT [`DreggIdentity`] (public-key hex) that adapter already attributes moves to.
///
/// In rung 1 this lives host/test-side (custodial keys); in rung 2 the same signing runs where
/// the user's device holds the secret (cipherclerk-in-wasm / WebAuthn) and only the
/// [`SignedAction`] crosses the wire.
pub struct TurnSigner {
    key: SigningKey,
    pubkey_hex: String,
}

impl TurnSigner {
    /// A signer from a 32-byte Ed25519 secret seed — the same constructor shape as
    /// `AgentCipherclerk::from_key_bytes`, so an adapter-derived seed yields the adapter's
    /// identity.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        let key = SigningKey::from_bytes(&seed);
        let pubkey_hex = key.public_key().hex();
        TurnSigner { key, pubkey_hex }
    }

    /// The signer's public key as canonical lowercase hex — its [`DreggIdentity`] handle.
    pub fn pubkey_hex(&self) -> &str {
        &self.pubkey_hex
    }

    /// The [`DreggIdentity`] every turn this signer signs verifies to.
    pub fn identity(&self) -> DreggIdentity {
        DreggIdentity(self.pubkey_hex.clone())
    }

    /// **Sign one turn**: produce the [`SignedAction`] for `action` in `(offering_key, session)`
    /// at replay counter `counter`, over the canonical [`signing_message`] — exactly what
    /// [`verify_signed`] (and thus
    /// [`OfferingHost::advance_signed`](crate::OfferingHost::advance_signed)) admits.
    pub fn sign(
        &self,
        offering_key: &str,
        session: &SessionId,
        counter: u64,
        action: Action,
    ) -> SignedAction {
        let msg = signing_message(offering_key, session, counter, &action);
        let sig = dregg_types::sign(&self.key, &msg);
        SignedAction {
            action,
            actor_pubkey_hex: self.pubkey_hex.clone(),
            counter,
            signature: sig.0,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Hex helpers (tiny, dependency-free — `hex` is only a dev-dependency here).
// ─────────────────────────────────────────────────────────────────────────────

/// Decode exactly 64 hex chars into 32 bytes (case-insensitive). `None` on any other shape.
fn decode_hex_32(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let nib = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = [0u8; 32];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (nib(chunk[0])? << 4) | nib(chunk[1])?;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn action() -> Action {
        Action::new("press on", "choose", 3, true)
    }

    /// THE WIRE PIN — the canonical signing message for a fixed input, byte for byte,
    /// constructed here BY HAND (not via [`signing_message`]), so any drift in the layout —
    /// a reordered field, a dropped separator, an endianness flip — is a red test, never a
    /// silent signer/verifier fork.
    #[test]
    fn the_canonical_signing_message_is_pinned_byte_for_byte() {
        let msg = signing_message(
            "dungeon",
            &SessionId::new("sess-1"),
            7,
            &action(), // turn "choose", arg 3, text None
        );

        let mut expected: Vec<u8> = Vec::new();
        expected.extend_from_slice(b"dregg-offering-turn-v1:");
        expected.extend_from_slice(b"dungeon");
        expected.push(0x00);
        expected.extend_from_slice(b"sess-1");
        expected.push(0x00);
        expected.extend_from_slice(&[7, 0, 0, 0, 0, 0, 0, 0]); // 7u64 LE
        expected.push(0x00);
        expected.extend_from_slice(b"choose");
        expected.push(0x00);
        expected.extend_from_slice(&[3, 0, 0, 0, 0, 0, 0, 0]); // 3i64 LE
        expected.push(0x00);
        // text-or-empty: None → empty
        assert_eq!(msg, expected, "the canonical turn signing message drifted");

        // A text payload rides at the end; a DIFFERENT text is a DIFFERENT message.
        let with_text = signing_message(
            "dungeon",
            &SessionId::new("sess-1"),
            7,
            &action().with_text("hello"),
        );
        let mut expected_text = expected.clone();
        expected_text.extend_from_slice(b"hello");
        assert_eq!(with_text, expected_text);
        assert_ne!(msg, with_text);
    }

    /// Sign → verify round-trips to the signer's identity; every verifier gate refuses its own
    /// forgery class (wrong key / tampered action / spliced session / spliced offering / stale
    /// counter / malformed key) — both polarities of each gate.
    #[test]
    fn verify_signed_admits_the_real_signer_and_refuses_each_forgery_class() {
        let signer = TurnSigner::from_seed([7u8; 32]);
        let imposter = TurnSigner::from_seed([8u8; 32]);
        let sid = SessionId::new("s-1");

        let sa = signer.sign("dungeon", &sid, 0, action());

        // The genuine envelope verifies to the signer's identity.
        let id = verify_signed("dungeon", &sid, 0, &sa).expect("genuine signature verifies");
        assert_eq!(id, signer.identity());
        assert_eq!(id.as_str().len(), 64, "identity is the 32-byte pubkey hex");

        // WRONG KEY: the imposter signs, but claims the signer's pubkey → BadSignature.
        let mut forged = imposter.sign("dungeon", &sid, 0, action());
        forged.actor_pubkey_hex = signer.pubkey_hex().to_string();
        assert_eq!(
            verify_signed("dungeon", &sid, 0, &forged),
            Err(SignedError::BadSignature)
        );

        // TAMPERED ACTION: a genuine envelope whose action was re-pointed → BadSignature.
        let mut tampered = sa.clone();
        tampered.action.arg = 4;
        assert_eq!(
            verify_signed("dungeon", &sid, 0, &tampered),
            Err(SignedError::BadSignature)
        );

        // SPLICED into a different session or offering → BadSignature (the domain binds both).
        assert_eq!(
            verify_signed("dungeon", &SessionId::new("s-2"), 0, &sa),
            Err(SignedError::BadSignature)
        );
        assert_eq!(
            verify_signed("council", &sid, 0, &sa),
            Err(SignedError::BadSignature)
        );

        // STALE COUNTER: the same envelope presented once its counter is consumed.
        assert_eq!(
            verify_signed("dungeon", &sid, 1, &sa),
            Err(SignedError::StaleCounter {
                presented: 0,
                expected: 1
            })
        );

        // MALFORMED KEY: not 32 bytes of hex.
        let mut short = sa.clone();
        short.actor_pubkey_hex = "abcd".to_string();
        assert_eq!(
            verify_signed("dungeon", &sid, 0, &short),
            Err(SignedError::MalformedKey)
        );

        // Case-insensitive key hex canonicalizes to the same lowercase identity.
        let mut upper = sa.clone();
        upper.actor_pubkey_hex = upper.actor_pubkey_hex.to_uppercase();
        assert_eq!(
            verify_signed("dungeon", &sid, 0, &upper).expect("uppercase hex verifies"),
            signer.identity()
        );
    }

    /// The attribution conversions: a bare identity is ASSERTED (legacy honest default), a
    /// signed attribution round-trips its pubkey identity, and only `Signed` reports signed.
    #[test]
    fn attribution_conversions_keep_the_trust_level_honest() {
        let legacy: Attribution = DreggIdentity("web:alice".to_string()).into();
        assert_eq!(
            legacy,
            Attribution::Asserted {
                label: "web:alice".to_string()
            }
        );
        assert!(!legacy.is_signed());
        assert_eq!(legacy.identity(), DreggIdentity("web:alice".to_string()));

        let signer = TurnSigner::from_seed([9u8; 32]);
        let signed = Attribution::Signed {
            pubkey_hex: signer.pubkey_hex().to_string(),
        };
        assert!(signed.is_signed());
        assert_eq!(signed.identity(), signer.identity());
        assert_eq!(DreggIdentity::from(signed), signer.identity());
    }
}
