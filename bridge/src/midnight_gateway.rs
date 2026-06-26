//! End-to-end wire path for the proof-carrying dregg → Midnight envelope.
//!
//! This module closes step 1 of the Level-1.5 lane
//! (`plans/midnight-bridge-production.md`): it carries a
//! [`VerifiedDreggToMidnight`] envelope *over the wire* and gives the two
//! parties that handle it on the dregg side a single place to **verify the
//! embedded circuit proof**:
//!
//! - [`BridgeGateway`] — the *relay* side. It accepts an envelope arriving as
//!   wire bytes, runs the full Level-1.5 verification (attestation leg +
//!   cross-binding + STARK proof), records the nonce so a replay cannot be
//!   re-queued, and enqueues the accepted claim in a store-and-forward buffer.
//!   Draining that buffer is what a relay posts to Midnight.
//!
//! - [`Watchtower`] — the *challenger* side. It is permissionless: **anyone**
//!   can run it against a relayed envelope with no trust in the relay or the
//!   federation. [`Watchtower::examine`] returns [`Verdict::Fraud`] iff the
//!   envelope's embedded proof does not verify against the attested burn — the
//!   fraud-proof material a single honest watcher uses to challenge.
//!
//! # Why this is the load-bearing safety component
//!
//! Midnight's contract circuits are Halo2/KZG over BLS12-381 with no in-circuit
//! verification of foreign proofs (see `bridge/src/midnight_contract.compact`
//! and the production plan). A dregg STARK therefore cannot be verified *on
//! Midnight*. The Midnight contract checks only the federation attestation
//! (Level 1). The circuit proof's safety value is realized **entirely on the
//! dregg side**, by watchtowers: the proof is the objective, deterministic
//! fraud evidence that turns "trust the federation threshold" (2/3) into "trust
//! any single honest watcher" (1-of-N).
//!
//! # The claim hash
//!
//! Both parties key a claim by its canonical attestation hash
//! ([`claim_hash`]) — the same domain-separated BLAKE3 hash the Midnight
//! contract keys its replay set on. A watchtower watching a relayed Midnight
//! claim (which carries only the Level-1 attestation) correlates it to the
//! proof-carrying wire envelope by this hash, then [`Watchtower::examine`]s it.

use crate::midnight::{
    DreggToMidnightMessage, FederationAttestation, MidnightBridgeConfig, NonceTracker,
};
use crate::midnight_verified::{VerifiedBridgeError, VerifiedDreggToMidnight};

/// The canonical claim identifier for an envelope: the domain-separated BLAKE3
/// hash of the Level-1 message payload.
///
/// This is exactly the value [`FederationAttestation::compute_message_hash`]
/// produces over [`DreggToMidnightMessage::canonical_payload`], i.e. the value
/// the Midnight contract uses to deduplicate unlock claims. It is therefore the
/// natural key for correlating a Midnight-side attestation claim back to the
/// proof-carrying envelope that should justify it.
pub fn claim_hash(message: &DreggToMidnightMessage) -> [u8; 32] {
    FederationAttestation::compute_message_hash(&message.canonical_payload())
}

// ============================================================================
// Gateway (relay side)
// ============================================================================

/// Errors from accepting an envelope at the gateway.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GatewayError {
    /// The wire bytes did not deserialize as a [`VerifiedDreggToMidnight`].
    Decode { reason: String },
    /// The envelope failed Level-1.5 verification (attestation, cross-binding,
    /// or the embedded STARK proof). This is the same check a watchtower runs.
    Rejected(VerifiedBridgeError),
}

impl core::fmt::Display for GatewayError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Decode { reason } => write!(f, "envelope wire-decode failed: {reason}"),
            Self::Rejected(e) => write!(f, "envelope rejected at gateway: {e}"),
        }
    }
}

impl std::error::Error for GatewayError {}

/// An envelope the gateway has fully verified and queued for Midnight submission.
#[derive(Clone, Debug)]
pub struct AcceptedEnvelope {
    /// The canonical claim hash (what a relay posts / a watchtower correlates).
    pub claim_hash: [u8; 32],
    /// The full proof-carrying envelope. A relay forwards the attestation leg to
    /// Midnight and keeps the proof available on the dregg wire for watchtowers.
    pub envelope: VerifiedDreggToMidnight,
}

/// The relay-side bridge gateway.
///
/// Accepts proof-carrying envelopes off the wire, verifies them (the embedded
/// proof included), tracks nonces to reject replays, and buffers accepted
/// claims for submission to Midnight (store-and-forward across Midnight's
/// ~20s block time).
pub struct BridgeGateway {
    config: MidnightBridgeConfig,
    midnight_federation_id: [u8; 32],
    nonce_tracker: NonceTracker,
    outbound: Vec<AcceptedEnvelope>,
}

impl BridgeGateway {
    /// Create a gateway for a given bridge config and Midnight destination id.
    pub fn new(config: MidnightBridgeConfig, midnight_federation_id: [u8; 32]) -> Self {
        Self {
            config,
            midnight_federation_id,
            nonce_tracker: NonceTracker::new(),
            outbound: Vec::new(),
        }
    }

    /// Accept an envelope arriving as postcard wire bytes.
    ///
    /// Decodes, then defers to [`Self::accept`].
    pub fn accept_wire(&mut self, bytes: &[u8]) -> Result<[u8; 32], GatewayError> {
        let envelope: VerifiedDreggToMidnight =
            postcard::from_bytes(bytes).map_err(|e| GatewayError::Decode {
                reason: e.to_string(),
            })?;
        self.accept(envelope)
    }

    /// Accept a decoded envelope.
    ///
    /// Runs the full [`VerifiedDreggToMidnight::verify`] (attestation +
    /// cross-binding + STARK proof, with replay checked against this gateway's
    /// nonce tracker). On success, records the nonce so the same `(epoch, nonce)`
    /// cannot be re-queued, buffers the accepted claim, and returns its
    /// [`claim_hash`].
    pub fn accept(&mut self, envelope: VerifiedDreggToMidnight) -> Result<[u8; 32], GatewayError> {
        envelope
            .verify(
                &self.config,
                &self.nonce_tracker,
                &self.midnight_federation_id,
            )
            .map_err(GatewayError::Rejected)?;

        // Verification passed and proved the nonce fresh; burn it now so a
        // re-submission of the same claim is rejected as a replay.
        self.nonce_tracker
            .record(envelope.message.attestation.epoch, envelope.message.nonce);

        let claim_hash = claim_hash(&envelope.message);
        self.outbound.push(AcceptedEnvelope {
            claim_hash,
            envelope,
        });
        Ok(claim_hash)
    }

    /// Number of accepted claims awaiting Midnight submission.
    pub fn pending(&self) -> usize {
        self.outbound.len()
    }

    /// Drain the store-and-forward buffer of accepted claims.
    ///
    /// A relay calls this to batch claims for posting to Midnight (the
    /// attestation leg is what the contract verifies; the proof stays on the
    /// dregg wire as fraud-proof material).
    pub fn drain_outbound(&mut self) -> Vec<AcceptedEnvelope> {
        std::mem::take(&mut self.outbound)
    }
}

// ============================================================================
// Watchtower (challenger side)
// ============================================================================

/// A watchtower's verdict on a relayed envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The envelope's embedded proof verifies against the attested burn. The
    /// claim is sound; no challenge is warranted.
    Valid {
        /// The canonical claim hash this verdict pertains to.
        claim_hash: [u8; 32],
    },
    /// The envelope failed verification. This is fraud: the carried
    /// `reason` is the objective, deterministic challenge evidence.
    Fraud {
        /// The canonical claim hash this verdict pertains to.
        claim_hash: [u8; 32],
        /// Why the claim is invalid.
        reason: VerifiedBridgeError,
    },
}

impl Verdict {
    /// Whether this verdict warrants challenging the relay.
    pub fn is_fraud(&self) -> bool {
        matches!(self, Verdict::Fraud { .. })
    }
}

/// A permissionless watchtower.
///
/// Holds only public configuration: the bridge config (federation epoch keys,
/// amount limits) and the expected Midnight destination id. Anyone can stand
/// one up and challenge fraudulent relays.
pub struct Watchtower {
    config: MidnightBridgeConfig,
    midnight_federation_id: [u8; 32],
}

impl Watchtower {
    /// Create a watchtower from public bridge configuration.
    pub fn new(config: MidnightBridgeConfig, midnight_federation_id: [u8; 32]) -> Self {
        Self {
            config,
            midnight_federation_id,
        }
    }

    /// Independently verify a relayed envelope.
    ///
    /// Runs the same Level-1.5 verification as the gateway, but with a *fresh*
    /// nonce tracker: a watchtower judges whether the claim is *cryptographically
    /// sound* (valid attestation + matching, verifying proof), not whether it is
    /// a replay — replay is the gateway's / Midnight contract's bookkeeping.
    ///
    /// A [`Verdict::Fraud`] is the 1-of-N safety guarantee in action: a single
    /// honest watcher detects a relay or federation that attests to a burn the
    /// circuit never witnessed.
    pub fn examine(&self, envelope: &VerifiedDreggToMidnight) -> Verdict {
        let ch = claim_hash(&envelope.message);
        match envelope.verify(
            &self.config,
            &NonceTracker::new(),
            &self.midnight_federation_id,
        ) {
            Ok(()) => Verdict::Valid { claim_hash: ch },
            Err(reason) => Verdict::Fraud {
                claim_hash: ch,
                reason,
            },
        }
    }

    /// Examine a Midnight-side attestation claim against the wire envelope that
    /// should justify it.
    ///
    /// The relay posts only the Level-1 attestation to Midnight; a watchtower
    /// learns the `claim_hash` from that posting and looks up the proof-carrying
    /// envelope on the dregg wire. This returns [`Verdict::Fraud`] when:
    ///
    /// - no envelope is presented for the claim (`envelope == None`) — the relay
    ///   posted an attestation with no proof behind it; or
    /// - the presented envelope does not hash to `expected_claim_hash` — it does
    ///   not justify this Midnight claim; or
    /// - the envelope fails verification (delegates to [`Self::examine`]).
    ///
    /// The fraud reason is reported as a [`ClaimFraud`], which distinguishes a
    /// missing proof and a mismatched claim from an invalid envelope.
    pub fn challenge_attestation_claim(
        &self,
        expected_claim_hash: [u8; 32],
        envelope: Option<&VerifiedDreggToMidnight>,
    ) -> ClaimVerdict {
        let Some(envelope) = envelope else {
            return ClaimVerdict::Fraud {
                claim_hash: expected_claim_hash,
                reason: ClaimFraud::MissingProof,
            };
        };
        let ch = claim_hash(&envelope.message);
        if ch != expected_claim_hash {
            return ClaimVerdict::Fraud {
                claim_hash: expected_claim_hash,
                reason: ClaimFraud::WrongClaim { presented: ch },
            };
        }
        match self.examine(envelope) {
            Verdict::Valid { claim_hash } => ClaimVerdict::Valid { claim_hash },
            Verdict::Fraud { claim_hash, reason } => ClaimVerdict::Fraud {
                claim_hash,
                reason: ClaimFraud::InvalidEnvelope(reason),
            },
        }
    }
}

/// Why a Midnight-side attestation claim is fraudulent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimFraud {
    /// No proof-carrying envelope was presented for the claim.
    MissingProof,
    /// The presented envelope hashes to a different claim than was posted.
    WrongClaim {
        /// The claim hash of the presented envelope.
        presented: [u8; 32],
    },
    /// The presented envelope failed Level-1.5 verification.
    InvalidEnvelope(VerifiedBridgeError),
}

impl core::fmt::Display for ClaimFraud {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MissingProof => write!(f, "no proof-carrying envelope presented for claim"),
            Self::WrongClaim { presented } => write!(
                f,
                "presented envelope hashes to a different claim ({:02x}{:02x}{:02x}{:02x}...)",
                presented[0], presented[1], presented[2], presented[3]
            ),
            Self::InvalidEnvelope(e) => write!(f, "presented envelope invalid: {e}"),
        }
    }
}

/// A watchtower's verdict on a Midnight-side attestation claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimVerdict {
    /// The claim is backed by a valid, matching proof-carrying envelope.
    Valid {
        /// The canonical claim hash.
        claim_hash: [u8; 32],
    },
    /// The claim is fraudulent.
    Fraud {
        /// The canonical claim hash.
        claim_hash: [u8; 32],
        /// Why it is fraudulent.
        reason: ClaimFraud,
    },
}

impl ClaimVerdict {
    /// Whether this verdict warrants challenging the relay.
    pub fn is_fraud(&self) -> bool {
        matches!(self, ClaimVerdict::Fraud { .. })
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::midnight::EpochKey;
    use crate::midnight_verified::commit_midnight_recipient;

    const MIDNIGHT_FED_ID: [u8; 32] = [0x6D; 32]; // 'm'

    fn signing_key() -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[0x42u8; 32])
    }

    fn config() -> MidnightBridgeConfig {
        let vk = signing_key().verifying_key();
        MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![EpochKey {
                from_epoch: 0,
                to_epoch: Some(10),
                pubkey: vk.to_bytes(),
            }],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        }
    }

    fn envelope(nonce: u64) -> VerifiedDreggToMidnight {
        VerifiedDreggToMidnight::create(
            [0xAA; 32],
            5_000_000,
            vec![0xBB; 32],
            nonce,
            MIDNIGHT_FED_ID,
            &signing_key(),
            0,
        )
    }

    #[test]
    fn claim_hash_matches_attestation_message_hash() {
        // The claim hash a watchtower correlates on must equal the hash the
        // federation actually signed over (so the Midnight contract and the
        // watchtower agree on claim identity).
        let env = envelope(1);
        assert_eq!(
            claim_hash(&env.message),
            env.message.attestation.message_hash
        );
    }

    #[test]
    fn gateway_accepts_valid_wire_envelope_and_queues_it() {
        let mut gw = BridgeGateway::new(config(), MIDNIGHT_FED_ID);
        let env = envelope(1);
        let bytes = postcard::to_stdvec(&env).unwrap();

        let ch = gw
            .accept_wire(&bytes)
            .expect("valid envelope must be accepted");
        assert_eq!(ch, claim_hash(&env.message));
        assert_eq!(gw.pending(), 1);

        let drained = gw.drain_outbound();
        assert_eq!(drained.len(), 1);
        assert_eq!(drained[0].claim_hash, ch);
        assert_eq!(gw.pending(), 0);
    }

    #[test]
    fn gateway_rejects_replayed_nonce() {
        let mut gw = BridgeGateway::new(config(), MIDNIGHT_FED_ID);
        let env = envelope(7);
        assert!(gw.accept(env.clone()).is_ok());
        // Same (epoch, nonce) again → rejected as a replay via the attestation leg.
        let r = gw.accept(env);
        assert!(
            matches!(
                r,
                Err(GatewayError::Rejected(VerifiedBridgeError::Attestation(
                    crate::midnight::MidnightBridgeError::NonceReplay { .. }
                )))
            ),
            "got {r:?}"
        );
        assert_eq!(gw.pending(), 1, "replay must not be queued");
    }

    #[test]
    fn gateway_rejects_garbage_wire_bytes() {
        let mut gw = BridgeGateway::new(config(), MIDNIGHT_FED_ID);
        let r = gw.accept_wire(&[0xFF, 0x00, 0x13, 0x37]);
        assert!(matches!(r, Err(GatewayError::Decode { .. })), "got {r:?}");
    }

    #[test]
    fn gateway_rejects_envelope_for_wrong_destination() {
        // Gateway configured for a different Midnight destination than the proof binds.
        let mut gw = BridgeGateway::new(config(), [0x99; 32]);
        let r = gw.accept(envelope(1));
        assert!(
            matches!(
                r,
                Err(GatewayError::Rejected(
                    VerifiedBridgeError::DestinationMismatch { .. }
                ))
            ),
            "got {r:?}"
        );
    }

    #[test]
    fn watchtower_accepts_valid_envelope() {
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let env = envelope(1);
        let v = wt.examine(&env);
        assert!(!v.is_fraud(), "honest envelope must pass: {v:?}");
        assert_eq!(
            v,
            Verdict::Valid {
                claim_hash: claim_hash(&env.message)
            }
        );
    }

    #[test]
    fn watchtower_detects_proof_attestation_divergence() {
        // The federation attests to a 5_000_000 burn, but the embedded proof
        // binds a 4_000_000 burn. The Midnight contract (checking only the
        // attestation) would accept; a single watchtower catches the fraud.
        let nullifier = [0xAA; 32];
        let recipient = vec![0xBB; 32];
        let fraudulent = VerifiedDreggToMidnight {
            message: VerifiedDreggToMidnight::create(
                nullifier,
                5_000_000,
                recipient.clone(),
                1,
                MIDNIGHT_FED_ID,
                &signing_key(),
                0,
            )
            .message,
            binding: crate::action_binding::create_action_binding(
                nullifier,
                commit_midnight_recipient(&recipient),
                MIDNIGHT_FED_ID,
                4_000_000, // proof disagrees with the attestation
            ),
        };

        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let v = wt.examine(&fraudulent);
        assert!(v.is_fraud(), "divergence must be caught: {v:?}");
        assert!(matches!(
            v,
            Verdict::Fraud {
                reason: VerifiedBridgeError::AmountMismatch,
                ..
            }
        ));
    }

    #[test]
    fn watchtower_detects_tampered_proof_bytes() {
        let mut env = envelope(1);
        env.binding.proof_bytes[20] ^= 0xFF;
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let v = wt.examine(&env);
        assert!(v.is_fraud(), "tampered proof must be caught: {v:?}");
        assert!(matches!(
            v,
            Verdict::Fraud {
                reason: VerifiedBridgeError::Binding(_),
                ..
            }
        ));
    }

    #[test]
    fn challenge_attestation_claim_missing_proof_is_fraud() {
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let env = envelope(1);
        let ch = claim_hash(&env.message);
        // Relay posted an attestation claim, but no envelope is presented.
        let v = wt.challenge_attestation_claim(ch, None);
        assert!(matches!(
            v,
            ClaimVerdict::Fraud {
                reason: ClaimFraud::MissingProof,
                ..
            }
        ));
    }

    #[test]
    fn challenge_attestation_claim_mismatched_envelope_is_fraud() {
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let posted = envelope(1);
        let other = envelope(2); // different nonce → different claim hash
        let v = wt.challenge_attestation_claim(claim_hash(&posted.message), Some(&other));
        assert!(matches!(
            v,
            ClaimVerdict::Fraud {
                reason: ClaimFraud::WrongClaim { .. },
                ..
            }
        ));
    }

    #[test]
    fn challenge_attestation_claim_valid_envelope_passes() {
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let env = envelope(1);
        let ch = claim_hash(&env.message);
        let v = wt.challenge_attestation_claim(ch, Some(&env));
        assert!(!v.is_fraud(), "valid backing envelope must pass: {v:?}");
        assert_eq!(v, ClaimVerdict::Valid { claim_hash: ch });
    }

    #[test]
    fn end_to_end_relay_then_watch() {
        // 1. Relay builds an envelope and ships it over the wire.
        let env = envelope(42);
        let wire = postcard::to_stdvec(&env).unwrap();

        // 2. Gateway accepts off the wire, verifies the embedded proof, queues it.
        let mut gw = BridgeGateway::new(config(), MIDNIGHT_FED_ID);
        let ch = gw.accept_wire(&wire).expect("gateway accepts");
        let accepted = gw.drain_outbound();
        assert_eq!(accepted.len(), 1);

        // 3. An independent watchtower re-verifies the same claim with no trust
        //    in the relay — the 1-of-N safety check.
        let wt = Watchtower::new(config(), MIDNIGHT_FED_ID);
        let v = wt.challenge_attestation_claim(ch, Some(&accepted[0].envelope));
        assert_eq!(v, ClaimVerdict::Valid { claim_hash: ch });
    }
}
