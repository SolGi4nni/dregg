//! # OCapN session handshake — `op:start-session` (SKETCH).
//!
//! This module sketches the OCapN session bootstrap against the existing
//! [`Netlayer`](crate::netlayer::Netlayer) trait. **Honest status**: the
//! message *shapes* and their [Syrup](super::syrup) encode/decode are real and
//! tested (as values); the *driven handshake* (writing/reading frames on a
//! live connection, verifying the cross-certification signature, installing
//! the [`CapSession`](crate::session::CapSession)) is described here but not
//! executed — see [§What remains](#what-remains). The [`syrup`](super::syrup)
//! codec is the finished deliverable; this is the next bounded step's blueprint
//! with its data structures already in place.
//!
//! ## The OCapN session bootstrap
//!
//! When two OCapN peers connect over a netlayer, before any object traffic
//! they exchange exactly one `op:start-session` record each (the protocol is
//! symmetric — both sides send, both sides receive):
//!
//! ```text
//! <op:start-session
//!    captp-version       ; a string, e.g. "1.0"
//!    session-pubkey      ; the public key this side will sign session
//!                        ;   assertions with (a public-key descriptor)
//!    acceptable-location ; THIS side's netlayer location (an OCapN locator —
//!                        ;   our `ocapn://<designator>.<hint>`), naming where
//!                        ;   it can be reached
//!    acceptable-location-sig> ; a signature, by session-pubkey, over the
//!                             ;   encoded acceptable-location
//! ```
//!
//! The `acceptable-location-sig` is the heart of it: it binds the session key
//! to the claimed location, so a peer cannot claim someone else's locator.
//! This is OCapN's analogue of our [`CapSession::epoch`] freshness story — the
//! signed location is what a re-dial re-certifies. (OCapN does not put an
//! epoch counter on the wire the way dregg does; reconnection freshness comes
//! from a fresh session key + fresh signed location. The netlayer's
//! [`EpochMinter`](crate::netlayer::EpochMinter) supplies our side's
//! [`CapSession::epoch`] independently.)
//!
//! Teardown is `<op:abort reason>` where `reason` is a string. Either side may
//! send it; the session and all its imports/exports are then dead.
//!
//! ## Mapping onto the Netlayer trait
//!
//! The handshake sits *between* dialing and capability traffic. Concretely,
//! given a dialed [`NetSession`](crate::netlayer::NetSession) `s`:
//!
//! 1. **Send our start frame.** Build [`StartSession`] for our own identity
//!    (our [`Netlayer::self_location`](crate::netlayer::Netlayer::self_location),
//!    our session pubkey, our signature over the encoded location), encode it
//!    with [`StartSession::to_syrup`] → [`Value::encode`](super::syrup::Value::encode),
//!    and `s.conn.send(frame)`.
//! 2. **Receive the peer's start frame.** `s.conn.recv()` → decode with
//!    [`Value::decode`](super::syrup::Value::decode) → [`StartSession::from_syrup`].
//! 3. **Verify the peer's cross-certification.** Check
//!    `acceptable-location-sig` against `session-pubkey` over the encoded
//!    `acceptable-location` ([`StartSession::location_signing_bytes`] gives the
//!    exact bytes that must be signed/verified). On failure, send `op:abort`
//!    and drop the session.
//! 4. **Bind identity.** The peer's verified locator designator is its OCapN
//!    identity; map it to a [`PeerId`](crate::netlayer::PeerId) and confirm it
//!    matches `s.captp.peer_strand` (the netlayer already minted the epoch).
//!
//! After step 4 the [`CapSession`](crate::session::CapSession) on `s.captp`
//! carries object traffic exactly as before this module existed: `op:deliver` /
//! `op:deliver-only` records carry method invocations (our
//! [`PipelinedAction`](crate::pipeline::PipelinedAction)), `desc:export` /
//! `desc:import-object` / `desc:answer` map onto
//! `s.captp.{exports,imports,promises}`, and `op:gc-export` / `op:gc-answer`
//! drive [`crate::gc`].
//!
//! ## What remains
//!
//! The codec is complete; turning this sketch into a driven handshake needs,
//! in order:
//!
//! 1. **A signature-scheme decision.** OCapN uses a public-key descriptor for
//!    `session-pubkey` and a signature descriptor for the location sig. dregg
//!    signs handoff certificates with Ed25519 ([`crate::handoff`]); the
//!    cleanest path is Ed25519 here too (Goblins' tcp-tls testing netlayer is
//!    signature-agnostic at this layer). Until that is fixed,
//!    [`StartSession::session_pubkey`] / [`StartSession::location_sig`] carry
//!    the descriptor as an opaque [`Value`](super::syrup::Value) (a record),
//!    which encodes/decodes losslessly but is not yet *verified*. This is the
//!    one genuine blocker and it is a one-function bridge once the scheme is
//!    chosen (`sign(location_signing_bytes)` / `verify(...)`).
//! 2. **The concrete shared wire** the frames travel on — an
//!    `impl Netlayer` for tcp+tls / Tor / libp2p (the OCapN netlayers Goblins
//!    actually speaks). The in-process and relay netlayers here already satisfy
//!    the trait and can exercise the handshake end-to-end in a test once (1) is
//!    decided; production interop wants the real socket netlayer (the node
//!    crate owns sockets, per [`crate::netlayer`] §3).
//! 3. **The async drive loop** that performs steps 1–4 above against a
//!    [`NetConnection`](crate::netlayer::NetConnection) (poll `recv` until the
//!    peer's frame arrives, with an `op:abort` timeout path).
//!
//! None of these touch the [`syrup`](super::syrup) codec or the
//! [`Netlayer`](crate::netlayer::Netlayer) trait.

use super::syrup::{SyrupError, Value};

/// The OCapN CapTP protocol version string this adapter targets.
///
/// (A constant so the start-session builder and any future negotiation read
/// from one place.)
pub const CAPTP_VERSION: &str = "1.0";

/// The record label for the session-start operation.
pub const OP_START_SESSION: &str = "op:start-session";

/// The record label for session teardown.
pub const OP_ABORT: &str = "op:abort";

/// Errors specific to interpreting OCapN session records (distinct from raw
/// [`SyrupError`] parse failures).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OcapnSessionError {
    /// The value was not a record, or had the wrong label.
    NotRecord {
        /// The label we expected.
        expected: &'static str,
    },
    /// A record had the wrong number of fields for its label.
    WrongArity {
        /// The record label.
        label: &'static str,
        /// How many fields we expected.
        expected: usize,
        /// How many fields were present.
        found: usize,
    },
    /// A field that had to be a string/symbol was the wrong type.
    WrongFieldType {
        /// 0-based field index.
        index: usize,
        /// What type was expected.
        expected: &'static str,
    },
    /// The underlying Syrup failed to decode.
    Syrup(SyrupError),
}

impl std::fmt::Display for OcapnSessionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OcapnSessionError::NotRecord { expected } => {
                write!(f, "expected a <{expected} …> record")
            }
            OcapnSessionError::WrongArity {
                label,
                expected,
                found,
            } => write!(
                f,
                "record <{label} …> has {found} fields, expected {expected}"
            ),
            OcapnSessionError::WrongFieldType { index, expected } => {
                write!(f, "field {index} must be a {expected}")
            }
            OcapnSessionError::Syrup(e) => write!(f, "syrup: {e}"),
        }
    }
}

impl std::error::Error for OcapnSessionError {}

impl From<SyrupError> for OcapnSessionError {
    fn from(e: SyrupError) -> Self {
        OcapnSessionError::Syrup(e)
    }
}

/// A parsed/buildable `op:start-session` record.
///
/// The `session_pubkey` and `location_sig` are carried as opaque
/// [`Value`]s (OCapN public-key / signature *descriptors* — themselves
/// records) because the signature scheme is not yet fixed (see the module's
/// [§What remains](self#what-remains)). They encode/decode losslessly; the
/// verification step that consumes them is the named remaining blocker.
#[derive(Clone, Debug, PartialEq)]
pub struct StartSession {
    /// The CapTP version string the peer offers (e.g. `"1.0"`).
    pub captp_version: String,
    /// The public key descriptor the peer signs session assertions with.
    pub session_pubkey: Value,
    /// The peer's netlayer location, as an OCapN locator string
    /// (`ocapn://<designator>.<hint>`). Stored as the string form so it
    /// round-trips through [`crate::netlayer::ocapn_uri::OcapnLocation`].
    pub acceptable_location: String,
    /// The signature (a descriptor) by `session_pubkey` over the encoded
    /// `acceptable_location` — see [`Self::location_signing_bytes`].
    pub location_sig: Value,
}

impl StartSession {
    /// Build a start-session record.
    pub fn new(
        captp_version: impl Into<String>,
        session_pubkey: Value,
        acceptable_location: impl Into<String>,
        location_sig: Value,
    ) -> Self {
        StartSession {
            captp_version: captp_version.into(),
            session_pubkey,
            acceptable_location: acceptable_location.into(),
            location_sig,
        }
    }

    /// The exact bytes that `location_sig` must sign / verify against: the
    /// canonical Syrup encoding of the `acceptable_location` **as a string
    /// value**. Pinning this here keeps signer and verifier in agreement (the
    /// one rule both sides must share once the scheme is chosen).
    pub fn location_signing_bytes(&self) -> Vec<u8> {
        Value::string(self.acceptable_location.clone()).encode()
    }

    /// Render as the Syrup record value
    /// `<op:start-session version pubkey location sig>`.
    pub fn to_syrup(&self) -> Value {
        Value::record(
            OP_START_SESSION,
            [
                Value::string(self.captp_version.clone()),
                self.session_pubkey.clone(),
                Value::string(self.acceptable_location.clone()),
                self.location_sig.clone(),
            ],
        )
    }

    /// Encode straight to canonical Syrup bytes (the wire frame payload).
    pub fn encode(&self) -> Vec<u8> {
        self.to_syrup().encode()
    }

    /// Parse from a Syrup record value.
    pub fn from_syrup(v: &Value) -> Result<Self, OcapnSessionError> {
        let fields = expect_record(v, OP_START_SESSION)?;
        if fields.len() != 4 {
            return Err(OcapnSessionError::WrongArity {
                label: OP_START_SESSION,
                expected: 4,
                found: fields.len(),
            });
        }
        let captp_version = expect_string(&fields[0], 0)?;
        let acceptable_location = expect_string(&fields[2], 2)?;
        Ok(StartSession {
            captp_version,
            session_pubkey: fields[1].clone(),
            acceptable_location,
            location_sig: fields[3].clone(),
        })
    }

    /// Decode from canonical Syrup bytes (a received wire frame).
    pub fn decode(bytes: &[u8]) -> Result<Self, OcapnSessionError> {
        let v = Value::decode(bytes)?;
        Self::from_syrup(&v)
    }
}

/// A parsed/buildable `op:abort` teardown record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbortReason {
    /// A human-readable reason string.
    pub reason: String,
}

impl AbortReason {
    /// Build an abort record with the given reason.
    pub fn new(reason: impl Into<String>) -> Self {
        AbortReason {
            reason: reason.into(),
        }
    }

    /// Render as `<op:abort reason>`.
    pub fn to_syrup(&self) -> Value {
        Value::record(OP_ABORT, [Value::string(self.reason.clone())])
    }

    /// Encode to canonical Syrup bytes.
    pub fn encode(&self) -> Vec<u8> {
        self.to_syrup().encode()
    }

    /// Parse from a Syrup record value.
    pub fn from_syrup(v: &Value) -> Result<Self, OcapnSessionError> {
        let fields = expect_record(v, OP_ABORT)?;
        if fields.len() != 1 {
            return Err(OcapnSessionError::WrongArity {
                label: OP_ABORT,
                expected: 1,
                found: fields.len(),
            });
        }
        Ok(AbortReason {
            reason: expect_string(&fields[0], 0)?,
        })
    }

    /// Decode from canonical Syrup bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, OcapnSessionError> {
        let v = Value::decode(bytes)?;
        Self::from_syrup(&v)
    }
}

/// Pull the fields out of a record with the expected symbol label.
fn expect_record<'a>(v: &'a Value, label: &'static str) -> Result<&'a [Value], OcapnSessionError> {
    match v {
        Value::Record {
            label: l,
            fields,
        } if matches!(l.as_ref(), Value::Symbol(s) if s == label) => Ok(fields),
        _ => Err(OcapnSessionError::NotRecord { expected: label }),
    }
}

/// Pull a `String` out of a `Str` (or `Symbol`) field.
fn expect_string(v: &Value, index: usize) -> Result<String, OcapnSessionError> {
    match v {
        Value::Str(s) | Value::Symbol(s) => Ok(s.clone()),
        _ => Err(OcapnSessionError::WrongFieldType {
            index,
            expected: "string",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::netlayer::ocapn_uri::OcapnLocation;

    /// A stand-in public-key / signature descriptor: OCapN models these as
    /// records (`<public-key …>` / `<sig-val …>`); until the scheme is fixed
    /// we carry them as opaque Syrup, and this builds a representative one so
    /// the round-trip tests exercise non-trivial nested payloads.
    fn fake_pubkey() -> Value {
        Value::record(
            "public-key",
            [Value::symbol("ed25519"), Value::bytes(vec![7u8; 32])],
        )
    }

    fn fake_sig() -> Value {
        Value::record(
            "sig-val",
            [Value::symbol("eddsa"), Value::bytes(vec![9u8; 64])],
        )
    }

    #[test]
    fn start_session_roundtrip() {
        let loc = OcapnLocation::new(bs58::encode([0xab; 32]).into_string(), "tcpip")
            .with_param("host", "example-node")
            .with_param("port", "30022");
        let ss = StartSession::new(CAPTP_VERSION, fake_pubkey(), loc.to_uri_string(), fake_sig());

        let bytes = ss.encode();
        let back = StartSession::decode(&bytes).unwrap();
        assert_eq!(back, ss);
        // The location field round-trips back to a parseable OCapN locator.
        assert_eq!(
            OcapnLocation::parse(&back.acceptable_location).unwrap(),
            loc
        );
    }

    #[test]
    fn start_session_is_a_record_with_the_right_label() {
        let ss = StartSession::new("1.0", fake_pubkey(), "ocapn://x.inproc", fake_sig());
        match ss.to_syrup() {
            Value::Record { label, fields } => {
                assert_eq!(*label, Value::symbol(OP_START_SESSION));
                assert_eq!(fields.len(), 4);
            }
            other => panic!("expected record, got {other:?}"),
        }
    }

    #[test]
    fn location_signing_bytes_is_stable_and_matches_string_encoding() {
        let ss = StartSession::new("1.0", fake_pubkey(), "ocapn://node.relay", fake_sig());
        // The signed bytes are exactly the Syrup string encoding of the
        // location — both sides compute this identically.
        assert_eq!(
            ss.location_signing_bytes(),
            Value::string("ocapn://node.relay").encode()
        );
        // And it is independent of the (unsigned) pubkey/sig fields.
        let ss2 = StartSession::new(
            "9.9",
            Value::int(0),
            "ocapn://node.relay",
            Value::Bool(true),
        );
        assert_eq!(ss.location_signing_bytes(), ss2.location_signing_bytes());
    }

    #[test]
    fn abort_roundtrip() {
        let a = AbortReason::new("peer misbehaved");
        let bytes = a.encode();
        assert_eq!(AbortReason::decode(&bytes).unwrap(), a);
        // Exact shape.
        assert_eq!(a.to_syrup(), Value::record(OP_ABORT, [Value::string("peer misbehaved")]));
    }

    #[test]
    fn from_syrup_rejects_wrong_label() {
        let not_start = Value::record("op:deliver", [Value::int(1)]);
        assert_eq!(
            StartSession::from_syrup(&not_start).unwrap_err(),
            OcapnSessionError::NotRecord {
                expected: OP_START_SESSION
            }
        );
    }

    #[test]
    fn from_syrup_rejects_wrong_arity() {
        // Right label, too few fields.
        let short = Value::record(OP_START_SESSION, [Value::string("1.0")]);
        assert!(matches!(
            StartSession::from_syrup(&short).unwrap_err(),
            OcapnSessionError::WrongArity {
                label: OP_START_SESSION,
                expected: 4,
                found: 1
            }
        ));
    }

    #[test]
    fn from_syrup_rejects_wrong_field_type() {
        // captp-version present but an int, not a string.
        let bad = Value::record(
            OP_START_SESSION,
            [
                Value::int(1),
                fake_pubkey(),
                Value::string("ocapn://x.inproc"),
                fake_sig(),
            ],
        );
        assert!(matches!(
            StartSession::from_syrup(&bad).unwrap_err(),
            OcapnSessionError::WrongFieldType {
                index: 0,
                expected: "string"
            }
        ));
    }

    #[test]
    fn decode_propagates_syrup_errors() {
        // Garbage bytes surface as a Syrup error, wrapped.
        assert!(matches!(
            StartSession::decode(b"not syrup at all\xff").unwrap_err(),
            OcapnSessionError::Syrup(_)
        ));
    }

    #[test]
    fn self_location_from_netlayer_is_a_valid_start_session_field() {
        // Tie the sketch to the real Netlayer surface: an InProcessNetlayer's
        // self_location() is exactly what goes in `acceptable_location`, and it
        // round-trips through the start-session record.
        use crate::netlayer::{InProcessFabric, Netlayer};
        let fabric = InProcessFabric::new();
        let me = fabric.join([0xa1; 32]);
        let loc = me.self_location();
        let ss = StartSession::new(CAPTP_VERSION, fake_pubkey(), loc.to_uri_string(), fake_sig());
        let back = StartSession::decode(&ss.encode()).unwrap();
        assert_eq!(
            OcapnLocation::parse(&back.acceptable_location).unwrap(),
            loc
        );
    }
}
