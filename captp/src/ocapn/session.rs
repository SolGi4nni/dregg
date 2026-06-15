//! # OCapN session handshake — `op:start-session`.
//!
//! This module implements the OCapN session bootstrap records against the
//! existing [`Netlayer`](crate::netlayer::Netlayer) trait. The message
//! *shapes*, their [Syrup](super::syrup) encode/decode, **and the
//! cross-certification signature** are real and tested: the
//! `acceptable-location-sig` is an Ed25519 signature (the same scheme dregg
//! signs handoff certificates with — [`crate::handoff`]), built from a
//! [`SigningKey`] by [`StartSession::new_signed`] and checked by
//! [`StartSession::verify_location_sig`] via the malleability-strict
//! [`dregg_types::verify`]. The session-pubkey and signature ride the wire as
//! the canonical OCapN gcrypt-shaped descriptors (`<public-key <ecc …>>` /
//! `<sig-val <eddsa …>>`, see [`desc`]). What is *not* yet executed is the
//! async drive loop that pumps these frames over a live socket — see
//! [§What remains](#what-remains).
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
//! 3. **Verify the peer's cross-certification.** Call
//!    [`StartSession::verify_location_sig`]: it extracts the Ed25519 public key
//!    from `session-pubkey`, the signature from `acceptable-location-sig`, and
//!    checks it against the encoded `acceptable-location`
//!    ([`StartSession::location_signing_bytes`] gives the exact signed bytes).
//!    On `Err`, send `op:abort` and drop the session.
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
//! ## Signature scheme
//!
//! `session-pubkey` and `acceptable-location-sig` are **Ed25519** — the scheme
//! dregg already signs handoff certificates with ([`crate::handoff`], via
//! [`dregg_types`]). On the wire they take OCapN's canonical gcrypt s-expression
//! descriptor shapes (the [`desc`] submodule builds and parses them):
//!
//! ```text
//! session-pubkey :  <public-key <ecc <curve Ed25519> <flags eddsa> <q  :32>>>
//! location-sig   :  <sig-val    <eddsa <r :32> <s :32>>>         ; r‖s = 64-byte sig
//! ```
//!
//! [`StartSession::new_signed`] takes a [`SigningKey`] and emits a record whose
//! sig descriptor is `sign(location_signing_bytes())`;
//! [`StartSession::verify_location_sig`] extracts the key and signature back out
//! and checks them with [`dregg_types::verify`] (which uses `verify_strict`,
//! rejecting non-canonical `S` — no signature malleability).
//!
//! ## What remains
//!
//! The records, their codec, and the cross-certification check are complete.
//! A *live driven handshake* additionally needs:
//!
//! 1. **The concrete shared wire** the frames travel on — an
//!    `impl Netlayer` for tcp+tls / Tor / libp2p (the OCapN netlayers Goblins
//!    actually speaks). The in-process and relay netlayers here already satisfy
//!    the trait and exercise the handshake end-to-end in a test; production
//!    interop wants the real socket netlayer (the node crate owns sockets, per
//!    [`crate::netlayer`] §3).
//! 2. **The async drive loop** that performs steps 1–4 above against a
//!    [`NetConnection`](crate::netlayer::NetConnection) (poll `recv` until the
//!    peer's frame arrives, with an `op:abort` timeout path).
//!
//! Neither touches the [`syrup`](super::syrup) codec or the
//! [`Netlayer`](crate::netlayer::Netlayer) trait.

use super::syrup::{SyrupError, Value};
use dregg_types::{PublicKey, Signature, SigningKey, sign, verify};

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
/// `session_pubkey` and `location_sig` are OCapN public-key / signature
/// *descriptors* (gcrypt-shaped Syrup records — see [`desc`]). They carry an
/// Ed25519 public key and an Ed25519 signature respectively;
/// [`Self::verify_location_sig`] is what consumes them, binding the key to the
/// claimed location.
#[derive(Clone, Debug, PartialEq)]
pub struct StartSession {
    /// The CapTP version string the peer offers (e.g. `"1.0"`).
    pub captp_version: String,
    /// The public key descriptor the peer signs session assertions with — an
    /// Ed25519 `<public-key <ecc …>>` (see [`desc::pubkey_from_descriptor`]).
    pub session_pubkey: Value,
    /// The peer's netlayer location, as an OCapN locator string
    /// (`ocapn://<designator>.<hint>`). Stored as the string form so it
    /// round-trips through [`crate::netlayer::ocapn_uri::OcapnLocation`].
    pub acceptable_location: String,
    /// The Ed25519 signature descriptor (`<sig-val <eddsa …>>`) by
    /// `session_pubkey` over the encoded `acceptable_location` — see
    /// [`Self::location_signing_bytes`] and [`desc::sig_from_descriptor`].
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

    /// Build a fully cross-certified start-session for our own identity:
    /// signs the encoded `acceptable_location` with `signing_key` (Ed25519) and
    /// emits the canonical OCapN descriptors for both the public key and the
    /// signature. The result is exactly what a peer's
    /// [`verify_location_sig`](Self::verify_location_sig) accepts.
    pub fn new_signed(
        captp_version: impl Into<String>,
        signing_key: &SigningKey,
        acceptable_location: impl Into<String>,
    ) -> Self {
        let acceptable_location = acceptable_location.into();
        // Pin the signed bytes the same way the verifier recomputes them.
        let signing_bytes = Value::string(acceptable_location.clone()).encode();
        let sig = sign(signing_key, &signing_bytes);
        StartSession {
            captp_version: captp_version.into(),
            session_pubkey: desc::ed25519_public_key_descriptor(&signing_key.public_key()),
            acceptable_location,
            location_sig: desc::ed25519_sig_descriptor(&sig),
        }
    }

    /// The exact bytes that `location_sig` must sign / verify against: the
    /// canonical Syrup encoding of the `acceptable_location` **as a string
    /// value**. Pinning this here keeps signer ([`Self::new_signed`]) and
    /// verifier ([`Self::verify_location_sig`]) in exact agreement — the one
    /// rule both sides share.
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

    /// Extract the Ed25519 public key carried in `session_pubkey`.
    ///
    /// This is the key the peer claims, and the key `verify_location_sig`
    /// checks the location signature against.
    pub fn session_public_key(&self) -> Result<PublicKey, LocationVerifyError> {
        desc::pubkey_from_descriptor(&self.session_pubkey)
    }

    /// Cross-certify the peer's claimed location: verify that `location_sig` is
    /// a valid Ed25519 signature, by `session_pubkey`, over
    /// [`location_signing_bytes`](Self::location_signing_bytes).
    ///
    /// This is the security heart of `op:start-session` — it binds the session
    /// key to the claimed locator, so a peer cannot present someone else's
    /// location. A failure here means the handshake MUST be aborted (the peer
    /// is forging, replaying, or corrupt). Verification uses
    /// [`dregg_types::verify`] (`verify_strict`), so non-canonical / malleable
    /// signatures are rejected.
    ///
    /// `Ok(())` admits the session; any [`LocationVerifyError`] rejects it
    /// (malformed descriptor *or* a signature that does not check out — both are
    /// grounds to abort).
    pub fn verify_location_sig(&self) -> Result<(), LocationVerifyError> {
        let pk = desc::pubkey_from_descriptor(&self.session_pubkey)?;
        let sig = desc::sig_from_descriptor(&self.location_sig)?;
        if verify(&pk, &self.location_signing_bytes(), &sig) {
            Ok(())
        } else {
            Err(LocationVerifyError::BadSignature)
        }
    }
}

/// Why a location signature failed to verify (from
/// [`StartSession::verify_location_sig`]).
///
/// The two arms are deliberately distinct: a *malformed descriptor* is a
/// well-formedness fault in the peer's frame (it sent something that is not a
/// recognizable Ed25519 public-key / signature descriptor), whereas
/// [`BadSignature`](Self::BadSignature) means the descriptors parsed but the
/// cryptographic check failed (forgery, wrong key, tampered location, or a
/// non-canonical signature). Both abort the handshake; the distinction is for
/// diagnostics and for callers that want to treat protocol errors differently
/// from authentication failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocationVerifyError {
    /// The `session-pubkey` value was not a well-formed Ed25519 `public-key`
    /// descriptor (wrong label/curve, or a `q` that is not 32 bytes / not a
    /// valid point).
    MalformedPublicKey,
    /// The `acceptable-location-sig` value was not a well-formed Ed25519
    /// `sig-val` descriptor (wrong label, or `r`/`s` not 32 bytes each).
    MalformedSignature,
    /// Both descriptors parsed, but the signature did not verify against the
    /// public key over the signed location bytes.
    BadSignature,
}

impl std::fmt::Display for LocationVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocationVerifyError::MalformedPublicKey => {
                write!(f, "session-pubkey is not a valid Ed25519 public-key descriptor")
            }
            LocationVerifyError::MalformedSignature => {
                write!(f, "acceptable-location-sig is not a valid Ed25519 sig-val descriptor")
            }
            LocationVerifyError::BadSignature => {
                write!(f, "location signature does not verify against the session public key")
            }
        }
    }
}

impl std::error::Error for LocationVerifyError {}

/// OCapN public-key / signature **descriptors** for Ed25519.
///
/// OCapN carries cryptographic material as gcrypt s-expressions serialized to
/// [Syrup](super::syrup), which surface here as nested [`Value::Record`]s. For
/// Ed25519 the canonical shapes (per the OCapN CapTP specification) are:
///
/// ```text
/// <public-key <ecc <curve Ed25519> <flags eddsa> <q  :32bytes>>>
/// <sig-val    <eddsa <r :32bytes> <s :32bytes>>>
/// ```
///
/// The inner elements are themselves single-field records keyed by a leading
/// symbol (`curve`, `flags`, `q`, `r`, `s`) — a direct transcription of the
/// gcrypt parameter list. Because gcrypt parameters are addressed *by name*,
/// the parsers here look fields up by their leading symbol rather than by
/// position, so they tolerate reordering (e.g. a `<q …>` that arrives before
/// `<curve …>`).
///
/// [`ed25519_public_key_descriptor`] / [`ed25519_sig_descriptor`] build them
/// from [`dregg_types`] primitives; [`pubkey_from_descriptor`] /
/// [`sig_from_descriptor`] extract them back out for verification.
pub mod desc {
    use super::{LocationVerifyError, PublicKey, Signature, Value};

    /// The `<public-key …>` record label.
    pub const PUBLIC_KEY: &str = "public-key";
    /// The `<sig-val …>` record label.
    pub const SIG_VAL: &str = "sig-val";
    /// The curve identifier symbol for Ed25519.
    pub const CURVE_ED25519: &str = "Ed25519";

    /// Build the canonical OCapN Ed25519 public-key descriptor for `pk`:
    /// `<public-key <ecc <curve Ed25519> <flags eddsa> <q :pk>>>`.
    pub fn ed25519_public_key_descriptor(pk: &PublicKey) -> Value {
        Value::record(
            PUBLIC_KEY,
            [Value::record(
                "ecc",
                [
                    Value::record("curve", [Value::symbol(CURVE_ED25519)]),
                    Value::record("flags", [Value::symbol("eddsa")]),
                    Value::record("q", [Value::bytes(pk.as_bytes().to_vec())]),
                ],
            )],
        )
    }

    /// Build the canonical OCapN Ed25519 signature descriptor for `sig`,
    /// splitting the 64-byte signature into its `r` and `s` halves:
    /// `<sig-val <eddsa <r :sig[0..32]> <s :sig[32..64]>>>`.
    pub fn ed25519_sig_descriptor(sig: &Signature) -> Value {
        let (r, s) = sig.0.split_at(32);
        Value::record(
            SIG_VAL,
            [Value::record(
                "eddsa",
                [
                    Value::record("r", [Value::bytes(r.to_vec())]),
                    Value::record("s", [Value::bytes(s.to_vec())]),
                ],
            )],
        )
    }

    /// Extract the 32-byte Ed25519 public key (`q`) from a `<public-key …>`
    /// descriptor.
    ///
    /// Accepts the canonical `<public-key <ecc <curve Ed25519> … <q :32>>>`,
    /// and is lenient about an `<ecc …>` wrapper being present or the bare
    /// parameter list appearing directly under `public-key` (both occur across
    /// gcrypt encodings). Requires the curve, when stated, to be Ed25519.
    pub fn pubkey_from_descriptor(v: &Value) -> Result<PublicKey, LocationVerifyError> {
        let fields = record_fields(v, PUBLIC_KEY).ok_or(LocationVerifyError::MalformedPublicKey)?;
        // The parameter list is either directly under <public-key …> or nested
        // one level inside an <ecc …> (or <ecc-flags …>) wrapper.
        let params = unwrap_single_inner(fields);
        // If a curve is named, it must be Ed25519 (reject p256/etc. early).
        if let Some(curve) = named_symbol(params, "curve") {
            if curve != CURVE_ED25519 {
                return Err(LocationVerifyError::MalformedPublicKey);
            }
        }
        let q = named_bytes(params, "q").ok_or(LocationVerifyError::MalformedPublicKey)?;
        let arr: [u8; 32] = q.try_into().map_err(|_| LocationVerifyError::MalformedPublicKey)?;
        Ok(PublicKey(arr))
    }

    /// Extract the 64-byte Ed25519 signature from a `<sig-val …>` descriptor,
    /// reassembling it from its `r` and `s` halves.
    pub fn sig_from_descriptor(v: &Value) -> Result<Signature, LocationVerifyError> {
        let fields = record_fields(v, SIG_VAL).ok_or(LocationVerifyError::MalformedSignature)?;
        // Parameters sit under an <eddsa …> wrapper (or directly, leniently).
        let params = unwrap_single_inner(fields);
        let r = named_bytes(params, "r").ok_or(LocationVerifyError::MalformedSignature)?;
        let s = named_bytes(params, "s").ok_or(LocationVerifyError::MalformedSignature)?;
        if r.len() != 32 || s.len() != 32 {
            return Err(LocationVerifyError::MalformedSignature);
        }
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(r);
        sig[32..].copy_from_slice(s);
        Ok(Signature(sig))
    }

    // ---- descriptor-walking helpers -------------------------------------

    /// If `v` is a `<label …>` record, return its fields.
    fn record_fields<'a>(v: &'a Value, label: &str) -> Option<&'a [Value]> {
        match v {
            Value::Record { label: l, fields }
                if matches!(l.as_ref(), Value::Symbol(s) if s == label) =>
            {
                Some(fields)
            }
            _ => None,
        }
    }

    /// gcrypt nests the real parameter list one level inside a wrapper record
    /// (`<ecc …>`, `<eddsa …>`). If `fields` is exactly one such record, descend
    /// into it; otherwise treat `fields` as the parameter list itself.
    fn unwrap_single_inner(fields: &[Value]) -> &[Value] {
        if let [Value::Record { fields: inner, .. }] = fields {
            inner
        } else {
            fields
        }
    }

    /// Find a `<name x …>` parameter record among `params` and return its first
    /// field. Parameters are keyed by their leading symbol (`name`).
    fn named_param<'a>(params: &'a [Value], name: &str) -> Option<&'a Value> {
        params.iter().find_map(|p| match p {
            Value::Record { label, fields }
                if matches!(label.as_ref(), Value::Symbol(s) if s == name) =>
            {
                fields.first()
            }
            _ => None,
        })
    }

    /// The bytes of a `<name :bytes>` parameter, if present and a bytestring.
    fn named_bytes<'a>(params: &'a [Value], name: &str) -> Option<&'a [u8]> {
        match named_param(params, name)? {
            Value::Bytes(b) => Some(b),
            _ => None,
        }
    }

    /// The symbol/string of a `<name 'sym>` parameter, if present.
    fn named_symbol<'a>(params: &'a [Value], name: &str) -> Option<&'a str> {
        match named_param(params, name)? {
            Value::Symbol(s) | Value::Str(s) => Some(s),
            _ => None,
        }
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
        Value::Record { label: l, fields } if matches!(l.as_ref(), Value::Symbol(s) if s == label) => {
            Ok(fields)
        }
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

    /// A representative (canonically-shaped) Ed25519 public-key descriptor —
    /// the real `<public-key <ecc …>>` form, with arbitrary key bytes. Used by
    /// the codec round-trip tests, which only care about lossless transport.
    fn fake_pubkey() -> Value {
        desc::ed25519_public_key_descriptor(&PublicKey([7u8; 32]))
    }

    fn fake_sig() -> Value {
        desc::ed25519_sig_descriptor(&Signature([9u8; 64]))
    }

    /// A deterministic Ed25519 keypair for the verification teeth.
    fn keypair(seed: u8) -> (SigningKey, PublicKey) {
        let sk = SigningKey::from_bytes(&[seed; 32]);
        let pk = sk.public_key();
        (sk, pk)
    }

    #[test]
    fn start_session_roundtrip() {
        let loc = OcapnLocation::new(bs58::encode([0xab; 32]).into_string(), "tcpip")
            .with_param("host", "example-node")
            .with_param("port", "30022");
        let ss = StartSession::new(
            CAPTP_VERSION,
            fake_pubkey(),
            loc.to_uri_string(),
            fake_sig(),
        );

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
        // And it depends ONLY on the location — never on the pubkey/sig
        // descriptor fields (so the verifier recomputes the signed bytes from
        // the location alone, exactly as the signer did).
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
        assert_eq!(
            a.to_syrup(),
            Value::record(OP_ABORT, [Value::string("peer misbehaved")])
        );
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
        // Tie this to the real Netlayer surface: an InProcessNetlayer's
        // self_location() is exactly what goes in `acceptable_location`, and it
        // round-trips through the start-session record.
        use crate::netlayer::{InProcessFabric, Netlayer};
        let fabric = InProcessFabric::new();
        let me = fabric.join([0xa1; 32]);
        let loc = me.self_location();
        let ss = StartSession::new(
            CAPTP_VERSION,
            fake_pubkey(),
            loc.to_uri_string(),
            fake_sig(),
        );
        let back = StartSession::decode(&ss.encode()).unwrap();
        assert_eq!(
            OcapnLocation::parse(&back.acceptable_location).unwrap(),
            loc
        );
    }

    // ===================================================================
    // Location-signature cross-certification: the security heart.
    // Both polarities — valid ADMITS, every forgery/tamper REJECTS.
    // ===================================================================

    const LOC: &str = "ocapn://node-a.tcpip";

    /// The Ed25519 descriptors round-trip through `dregg_types`: a built
    /// public-key/sig descriptor extracts back to the exact bytes.
    #[test]
    fn descriptor_roundtrip_through_dregg_types() {
        let (sk, pk) = keypair(1);
        let sig = sign(&sk, b"hello location");
        let pk_desc = desc::ed25519_public_key_descriptor(&pk);
        let sig_desc = desc::ed25519_sig_descriptor(&sig);
        assert_eq!(desc::pubkey_from_descriptor(&pk_desc).unwrap(), pk);
        assert_eq!(desc::sig_from_descriptor(&sig_desc).unwrap(), sig);
        // And they survive a full Syrup encode/decode (the actual wire path).
        assert_eq!(
            desc::pubkey_from_descriptor(&Value::decode(&pk_desc.encode()).unwrap()).unwrap(),
            pk
        );
        assert_eq!(
            desc::sig_from_descriptor(&Value::decode(&sig_desc.encode()).unwrap()).unwrap(),
            sig
        );
    }

    /// TOOTH (+): a correctly-signed start-session ADMITS.
    #[test]
    fn valid_location_sig_admits() {
        let (sk, _pk) = keypair(2);
        let ss = StartSession::new_signed(CAPTP_VERSION, &sk, LOC);
        assert_eq!(ss.verify_location_sig(), Ok(()));
        // And it admits after a full wire round-trip (decode then verify).
        let back = StartSession::decode(&ss.encode()).unwrap();
        assert_eq!(back.verify_location_sig(), Ok(()));
        // The recovered public key is exactly the signer's.
        assert_eq!(back.session_public_key().unwrap(), sk.public_key());
    }

    /// TOOTH (−): a signature by the WRONG key REJECTS, even though both the
    /// pubkey and sig descriptors are individually well-formed.
    #[test]
    fn wrong_key_signature_rejects() {
        let (attacker_sk, _) = keypair(3);
        let (_, victim_pk) = keypair(4);
        // Sign with the attacker's key but advertise the victim's pubkey.
        let signing_bytes = Value::string(LOC).encode();
        let forged = sign(&attacker_sk, &signing_bytes);
        let ss = StartSession::new(
            CAPTP_VERSION,
            desc::ed25519_public_key_descriptor(&victim_pk),
            LOC,
            desc::ed25519_sig_descriptor(&forged),
        );
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::BadSignature)
        );
    }

    /// TOOTH (−): a garbage signature (right shape, wrong bytes) REJECTS.
    #[test]
    fn forged_signature_bytes_reject() {
        let (sk, pk) = keypair(5);
        let ss = StartSession::new(
            CAPTP_VERSION,
            desc::ed25519_public_key_descriptor(&pk),
            LOC,
            // 64 zero bytes is not a valid signature by anyone.
            desc::ed25519_sig_descriptor(&Signature([0u8; 64])),
        );
        let _ = sk; // key is fine; the signature is the forgery
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::BadSignature)
        );
    }

    /// TOOTH (−): if the location is tampered after signing, verification
    /// REJECTS — the signature no longer covers the advertised locator (this is
    /// the whole point: you cannot claim someone else's location).
    #[test]
    fn tampered_location_rejects() {
        let (sk, _pk) = keypair(6);
        let mut ss = StartSession::new_signed(CAPTP_VERSION, &sk, LOC);
        assert_eq!(ss.verify_location_sig(), Ok(())); // valid as built
        ss.acceptable_location = "ocapn://evil-twin.tcpip".to_string();
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::BadSignature)
        );
    }

    /// TOOTH (−): a malformed public-key descriptor (not the Ed25519 shape) is
    /// reported as `MalformedPublicKey`, distinct from a bad signature.
    #[test]
    fn malformed_pubkey_descriptor_rejects() {
        let (sk, _pk) = keypair(7);
        let sig = sign(&sk, &Value::string(LOC).encode());
        // session_pubkey is the OLD opaque junk shape, not <public-key <ecc …>>.
        let ss = StartSession::new(
            CAPTP_VERSION,
            Value::record("public-key", [Value::symbol("eddsa"), Value::bytes(vec![0u8; 32])]),
            LOC,
            desc::ed25519_sig_descriptor(&sig),
        );
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::MalformedPublicKey)
        );
        // session_public_key() surfaces the same fault directly.
        assert_eq!(
            ss.session_public_key(),
            Err(LocationVerifyError::MalformedPublicKey)
        );
    }

    /// TOOTH (−): a malformed signature descriptor (wrong-length r/s) is
    /// reported as `MalformedSignature`, distinct from a bad signature.
    #[test]
    fn malformed_sig_descriptor_rejects() {
        let (sk, pk) = keypair(8);
        let _ = sk;
        // r is only 16 bytes — not a valid Ed25519 sig half.
        let bad_sig = Value::record(
            desc::SIG_VAL,
            [Value::record(
                "eddsa",
                [
                    Value::record("r", [Value::bytes(vec![1u8; 16])]),
                    Value::record("s", [Value::bytes(vec![2u8; 32])]),
                ],
            )],
        );
        let ss = StartSession::new(
            CAPTP_VERSION,
            desc::ed25519_public_key_descriptor(&pk),
            LOC,
            bad_sig,
        );
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::MalformedSignature)
        );
    }

    /// TOOTH (−): a non-canonical / wrong public key point that is not a valid
    /// curve point REJECTS at extraction (`verify_strict` would also catch a
    /// non-canonical key, but extraction reports the malformed key first only if
    /// it fails `try_into`; an all-0xff `q` is a non-point and fails verify).
    #[test]
    fn non_point_pubkey_rejects() {
        // q is 32 bytes (well-sized) but not a valid Ed25519 point: verify
        // returns false -> BadSignature (the descriptor parsed; the key just
        // can't validate anything).
        let (sk, _pk) = keypair(9);
        let sig = sign(&sk, &Value::string(LOC).encode());
        let bogus_pk = Value::record(
            desc::PUBLIC_KEY,
            [Value::record(
                "ecc",
                [
                    Value::record("curve", [Value::symbol(desc::CURVE_ED25519)]),
                    Value::record("q", [Value::bytes(vec![0xffu8; 32])]),
                ],
            )],
        );
        let ss = StartSession::new(
            CAPTP_VERSION,
            bogus_pk,
            LOC,
            desc::ed25519_sig_descriptor(&sig),
        );
        // PublicKey([0xff;32]) -> to_verifying_key() is None -> verify() false.
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::BadSignature)
        );
    }

    /// The verifier tolerates descriptor field REORDERING (gcrypt params are
    /// addressed by name): a pubkey with `<q …>` before `<curve …>` still
    /// admits a valid signature.
    #[test]
    fn pubkey_descriptor_field_order_is_tolerated() {
        let (sk, pk) = keypair(10);
        let ss_sig = sign(&sk, &Value::string(LOC).encode());
        let reordered_pk = Value::record(
            desc::PUBLIC_KEY,
            [Value::record(
                "ecc",
                [
                    Value::record("q", [Value::bytes(pk.as_bytes().to_vec())]),
                    Value::record("flags", [Value::symbol("eddsa")]),
                    Value::record("curve", [Value::symbol(desc::CURVE_ED25519)]),
                ],
            )],
        );
        let ss = StartSession::new(
            CAPTP_VERSION,
            reordered_pk,
            LOC,
            desc::ed25519_sig_descriptor(&ss_sig),
        );
        assert_eq!(ss.verify_location_sig(), Ok(()));
    }

    /// A wrong CURVE in the descriptor is rejected as malformed (we sign only
    /// Ed25519 here; a p256 descriptor must not be silently accepted).
    #[test]
    fn wrong_curve_rejects() {
        let (sk, pk) = keypair(11);
        let sig = sign(&sk, &Value::string(LOC).encode());
        let p256_pk = Value::record(
            desc::PUBLIC_KEY,
            [Value::record(
                "ecc",
                [
                    Value::record("curve", [Value::symbol("NIST-P256")]),
                    Value::record("q", [Value::bytes(pk.as_bytes().to_vec())]),
                ],
            )],
        );
        let ss = StartSession::new(
            CAPTP_VERSION,
            p256_pk,
            LOC,
            desc::ed25519_sig_descriptor(&sig),
        );
        assert_eq!(
            ss.verify_location_sig(),
            Err(LocationVerifyError::MalformedPublicKey)
        );
    }
}
