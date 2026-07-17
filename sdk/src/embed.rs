//! # dregg-embed: No-I/O integration layer
//!
//! This module provides a zero-I/O facade over dregg's core capabilities,
//! suitable for embedding in any existing service without dragging in dregg's
//! networking, consensus, or storage infrastructure.
//!
//! The pattern follows the "sans-io" approach: all methods are synchronous,
//! take bytes in, and produce bytes/state-transitions out. The **caller**
//! handles transport, persistence, and scheduling.
//!
//! # What's no-IO here
//!
//! - `TurnExecutor::execute()` — pure state machine, no I/O
//! - `prove_presentation` / `verify_presentation` — pure computation
//! - Token mint/attenuate — pure HMAC/hash operations
//! - `WireCodec::encode` / `decode` — pure serialization
//!
//! # Integration examples
//!
//! ## Axum HTTP handler (verify proof from a header)
//!
//! ```ignore
//! async fn verify_handler(headers: HeaderMap, State(engine): State<Arc<DreggEngine>>) -> StatusCode {
//!     let proof_b64 = headers.get("x-dregg-proof").unwrap();
//!     let proof_bytes = base64::decode(proof_b64).unwrap();
//!     let root = engine.federation_root();
//!     if engine.verify_presentation(&proof_bytes, &root) {
//!         StatusCode::OK
//!     } else {
//!         StatusCode::FORBIDDEN
//!     }
//! }
//! ```
//!
//! ## gRPC interceptor (attenuate token per-request)
//!
//! ```ignore
//! fn intercept(engine: &DreggEngine, parent_token: &[u8], caveats: &[Caveat]) -> Vec<u8> {
//!     engine.attenuate(parent_token, caveats).unwrap()
//! }
//! ```
//!
//! ## CLI tool (generate proof, output bytes)
//!
//! ```ignore
//! let engine = DreggEngine::new(EngineConfig::for_testing());
//! let token = engine.mint_token(b"my-root-key-32-bytes-exactly!!!!", "my-service").unwrap();
//! let proof = engine.prove_presentation(&token, "read", "my-service").unwrap();
//! std::fs::write("proof.bin", &proof).unwrap();
//! ```

use dregg_bridge::present::{self, BridgePresentationBuilder, WirePresentationProof};
use dregg_cell::Ledger;
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use dregg_turn::turn::TurnResult;
use dregg_turn::{Turn, TurnReceipt};

use crate::error::SdkError;

// Re-export the executor so embedders can configure costs without extra imports.
pub use dregg_turn::executor::{ComputronCosts, TurnExecutor};

// =============================================================================
// Error types
// =============================================================================

/// Errors from the embed layer.
#[derive(Debug)]
pub enum EmbedError {
    /// Turn deserialization failed.
    TurnDecode(String),
    /// Turn execution was rejected by the executor.
    TurnRejected {
        reason: String,
        at_action: Vec<usize>,
    },
    /// State snapshot serialization/deserialization failed.
    StateSerde(String),
    /// State snapshot integrity check failed (BLAKE3 hash mismatch).
    ///
    /// This indicates the snapshot was tampered with or corrupted in storage/transit.
    IntegrityCheckFailed,
    /// Token operation failed.
    Token(String),
    /// Proof generation failed.
    ProofGen(String),
    /// Proof verification failed (malformed input, not "invalid proof").
    ProofDecode(String),
}

impl std::fmt::Display for EmbedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TurnDecode(e) => write!(f, "turn decode: {e}"),
            Self::TurnRejected { reason, at_action } => {
                write!(f, "turn rejected at {at_action:?}: {reason}")
            }
            Self::StateSerde(e) => write!(f, "state serde: {e}"),
            Self::IntegrityCheckFailed => write!(
                f,
                "state integrity check failed: BLAKE3 hash mismatch (snapshot may be tampered)"
            ),
            Self::Token(e) => write!(f, "token: {e}"),
            Self::ProofGen(e) => write!(f, "proof gen: {e}"),
            Self::ProofDecode(e) => write!(f, "proof decode: {e}"),
        }
    }
}

impl std::error::Error for EmbedError {}

impl From<SdkError> for EmbedError {
    fn from(e: SdkError) -> Self {
        Self::Token(e.to_string())
    }
}

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the no-I/O engine.
///
/// This struct intentionally does NOT implement `Default`. The `timestamp` field
/// is critical for proof verification: a zero timestamp causes cipherclerk-generated
/// proofs to appear "from the future" and engine-generated proofs to be rejected
/// as expired. Callers MUST provide a real wall-clock timestamp.
///
/// Use [`EngineConfig::new()`] for production (requires explicit timestamp) or
/// [`EngineConfig::for_testing()`] for test contexts where timestamp doesn't matter.
#[derive(Clone, Debug)]
pub struct EngineConfig {
    /// Computron cost table for turn metering.
    pub costs: ComputronCosts,
    /// This federation's identity (32-byte hash). Used for cross-federation
    /// replay prevention in turn signatures.
    pub federation_id: [u8; 32],
    /// Initial block height.
    pub block_height: u64,
    /// Initial timestamp (unix seconds).
    ///
    /// **IMPORTANT**: This must be set to the current wall-clock time for proof
    /// freshness checks to work correctly. A timestamp of 0 will cause all
    /// verification to fail silently.
    pub timestamp: i64,
    /// Maximum age of a presentation proof in seconds for freshness checks.
    ///
    /// When non-zero, `verify_presentation_bytes()` rejects proofs whose embedded
    /// timestamp is older than this many seconds from the engine's current timestamp.
    /// Defaults to 300 seconds (5 minutes).
    pub max_proof_age_secs: i64,
}

impl EngineConfig {
    /// Create a new engine configuration with an explicit timestamp.
    ///
    /// This is the recommended constructor for production use. The timestamp
    /// should be the current wall-clock time (unix seconds).
    ///
    /// # Example
    ///
    /// ```
    /// use dregg_sdk::embed::EngineConfig;
    /// use std::time::SystemTime;
    ///
    /// let now = SystemTime::now()
    ///     .duration_since(SystemTime::UNIX_EPOCH)
    ///     .unwrap()
    ///     .as_secs() as i64;
    /// let config = EngineConfig::new(now);
    /// ```
    pub fn new(timestamp: i64) -> Self {
        Self {
            costs: ComputronCosts::default_costs(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp,
            max_proof_age_secs: present::DEFAULT_MAX_PROOF_AGE_SECS,
        }
    }

    /// Create a configuration suitable for testing only.
    ///
    /// Uses timestamp 0 and default values. Proofs generated or verified with
    /// this config will NOT pass freshness checks against real-world timestamps.
    ///
    /// **Do not use in production.** Use [`EngineConfig::new()`] with a real
    /// wall-clock timestamp instead.
    pub fn for_testing() -> Self {
        Self {
            costs: ComputronCosts::default_costs(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp: 0,
            max_proof_age_secs: present::DEFAULT_MAX_PROOF_AGE_SECS,
        }
    }
}

// =============================================================================
// DreggEngine — the no-IO core
// =============================================================================

/// The no-I/O dregg engine.
///
/// Wraps the turn executor and ledger in a single struct with a bytes-oriented
/// API. Does **no** networking, filesystem access, or async operations.
///
/// Thread safety: NOT `Sync` by default (contains `Ledger` which is a BTreeMap).
/// Wrap in `Mutex` or `RwLock` if sharing across threads.
pub struct DreggEngine {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The current federation root (caller updates this from their own sync).
    federation_root: [u8; 32],
    /// Maximum proof age in seconds (0 = no freshness check).
    max_proof_age_secs: i64,
}

impl DreggEngine {
    /// Create a new engine with the given configuration and an empty ledger.
    pub fn new(config: EngineConfig) -> Self {
        let mut executor = TurnExecutor::new(config.costs);
        executor.set_block_height(config.block_height);
        executor.set_timestamp(config.timestamp);
        executor.set_local_federation_id(config.federation_id);
        Self {
            ledger: Ledger::new(),
            executor,
            federation_root: [0u8; 32],
            max_proof_age_secs: config.max_proof_age_secs,
        }
    }

    /// Create an engine from an existing ledger (e.g. loaded from your own DB).
    pub fn with_ledger(config: EngineConfig, ledger: Ledger) -> Self {
        let mut executor = TurnExecutor::new(config.costs);
        executor.set_block_height(config.block_height);
        executor.set_timestamp(config.timestamp);
        executor.set_local_federation_id(config.federation_id);
        Self {
            ledger,
            executor,
            federation_root: [0u8; 32],
            max_proof_age_secs: config.max_proof_age_secs,
        }
    }

    // =========================================================================
    // Turn execution
    // =========================================================================

    /// Execute a turn provided as postcard-encoded bytes.
    ///
    /// On success, the ledger is mutated and a `TurnReceipt` is returned.
    /// On rejection, the ledger is unchanged and the reason is in the error.
    pub fn execute_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<TurnReceipt, EmbedError> {
        let turn: Turn =
            postcard::from_bytes(turn_bytes).map_err(|e| EmbedError::TurnDecode(e.to_string()))?;
        self.execute_turn(&turn)
    }

    /// Execute a pre-deserialized turn.
    pub fn execute_turn(&mut self, turn: &Turn) -> Result<TurnReceipt, EmbedError> {
        match self.executor.execute(turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => Ok(receipt),
            TurnResult::Rejected { reason, at_action } => Err(EmbedError::TurnRejected {
                reason: format!("{reason:?}"),
                at_action,
            }),
            TurnResult::Expired => Err(EmbedError::TurnRejected {
                reason: "conditional turn expired".into(),
                at_action: vec![],
            }),
            TurnResult::Pending => Err(EmbedError::TurnRejected {
                reason: "conditional turn pending".into(),
                at_action: vec![],
            }),
        }
    }

    /// Validate a turn without applying it (dry-run).
    pub fn validate_turn(&self, turn: &Turn) -> Result<(), EmbedError> {
        self.executor
            .validate_without_apply(turn, &self.ledger)
            .map_err(|e| EmbedError::TurnRejected {
                reason: format!("{e:?}"),
                at_action: vec![],
            })
    }

    /// Estimate computron cost of a turn without executing.
    pub fn estimate_cost(&self, turn: &Turn) -> u64 {
        self.executor.estimate_cost(turn)
    }

    // =========================================================================
    // Proof generation and verification
    // =========================================================================

    /// Generate a presentation proof from a token chain.
    ///
    /// `encoded_token` is the `em2_`-encoded root token string.
    /// `root_key` is the 32-byte root key used to mint the token.
    /// `attenuations` is the chain of attenuations applied after minting.
    /// `action` and `resource` define the authorization request.
    ///
    /// Returns the wire-safe proof bytes (postcard-encoded `WirePresentationProof`).
    pub fn prove_presentation(
        &self,
        encoded_token: &str,
        root_key: &[u8; 32],
        attenuations: &[Attenuation],
        action: &str,
        resource: &str,
    ) -> Result<Vec<u8>, EmbedError> {
        let token = MacaroonToken::from_encoded(encoded_token, *root_key)
            .map_err(|e| EmbedError::ProofGen(format!("token decode: {e}")))?;

        // Derive the proof key from root_key using the same KDF as the cipherclerk.
        // Federation tree leaves are hash(derived_proof_key), so both engine and
        // cipherclerk proofs must target the same leaf.
        let proof_key = blake3::derive_key("dregg-proof-key-v1", root_key);

        let mut builder = BridgePresentationBuilder::new(proof_key, self.federation_root);
        builder.set_root_token(token);

        for att in attenuations {
            if !builder.add_attenuation(att) {
                return Err(EmbedError::ProofGen("attenuation failed".into()));
            }
        }

        // Refuse to generate proofs with timestamp 0 — they'll be rejected by any
        // verifier with real time. Fail loudly at generation rather than silently at verification.
        let now = if self.executor.current_timestamp > 0 {
            self.executor.current_timestamp
        } else {
            return Err(EmbedError::ProofGen(
                "engine timestamp is 0; call set_timestamp() before generating proofs".into(),
            ));
        };

        let request = AuthRequest {
            action: Some(action.to_string()),
            service: Some(resource.to_string()),
            app_id: None,
            features: vec![],
            user_id: None,
            now: Some(now),
            ..Default::default()
        };

        let proof = builder
            .prove(&request)
            .map_err(|e| EmbedError::ProofGen(format!("{e:?}")))?;

        let wire_proof = proof.into_wire_proof();
        postcard::to_stdvec(&wire_proof).map_err(|e| EmbedError::ProofGen(e.to_string()))
    }

    /// Verify a wire presentation proof against the current federation root.
    ///
    /// Performs the SAME checks as `verify_presentation_full`:
    /// 1. STARK proof validity (issuer membership)
    /// 2. Federation root binding
    /// 3. Action binding — the proof must be bound to `(expected_action, expected_resource)`
    /// 4. Timestamp freshness — the proof must not be older than `max_proof_age_secs`
    ///
    /// Returns `Ok(true)` on success, `Ok(false)` if the proof is cryptographically
    /// invalid or fails any check, or `Err` if the input cannot be decoded.
    ///
    /// Returns `Ok(false)` immediately if no federation root has been set (rejects
    /// proofs forged against the zero root). Configure via `set_federation_root`.
    pub fn verify_presentation_bytes(
        &self,
        proof_bytes: &[u8],
        expected_action: &str,
        expected_resource: &str,
    ) -> Result<bool, EmbedError> {
        if self.federation_root == [0u8; 32] {
            return Ok(false);
        }
        self.verify_presentation_against(
            proof_bytes,
            &self.federation_root,
            expected_action,
            expected_resource,
        )
    }

    /// Verify a wire presentation proof against a specific federation root.
    ///
    /// Delegates to the canonical [`present::verify_proof_complete`] which checks ALL of:
    /// 1. Reject zero federation root
    /// 2. Real STARK proof presence
    /// 3. STARK validity (issuer membership)
    /// 4. Federation root binding
    /// 5. Action binding (proof bound to expected_action + expected_resource)
    /// 6. Timestamp freshness (proof not older than max_proof_age_secs)
    /// 7. Composition commitment (non-zero AND correctly recomputed)
    /// 8. Proof tier (Production only)
    ///
    /// Use this when the caller supplies their own root (e.g., from a trusted
    /// external source or a specific block height).
    pub fn verify_presentation_against(
        &self,
        proof_bytes: &[u8],
        federation_root: &[u8; 32],
        expected_action: &str,
        expected_resource: &str,
    ) -> Result<bool, EmbedError> {
        let wire_proof: WirePresentationProof = match postcard::from_bytes(proof_bytes) {
            Ok(p) => p,
            Err(e) => return Err(EmbedError::ProofDecode(e.to_string())),
        };

        let now = self.executor.current_timestamp;
        match present::verify_proof_complete(
            &wire_proof,
            expected_action,
            expected_resource,
            federation_root,
            now,
            self.max_proof_age_secs,
        ) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    /// Verify ONLY federation membership (STARK proof + root binding).
    ///
    /// This checks that the proof is a valid STARK proof with the expected
    /// federation root, but does NOT check action binding or freshness.
    ///
    /// **WARNING**: Use this ONLY for federation membership verification where
    /// action binding is not applicable (e.g., qualifying a node as a federation
    /// member). For action-authorized requests, use [`verify_presentation_bytes`]
    /// which enforces full security checks via [`present::verify_proof_complete`].
    // AUDIT[P2]: returns `bool` and swallows the underlying error category.
    // Callers cannot distinguish "decode failure" from "STARK rejected" from
    // "wrong root". Consider returning `Result<(), MembershipError>` to surface
    // failures into telemetry and prevent silent acceptance windows during
    // partial federation rotations.
    pub fn verify_membership_proof(&self, proof_bytes: &[u8], federation_root: &[u8; 32]) -> bool {
        self.verify_membership_proof_outcome(proof_bytes, federation_root)
            .is_ok()
    }

    /// P2-3: categorised outcome version of [`verify_membership_proof`].
    ///
    /// Surfaces the specific failure category (decode error, STARK rejected,
    /// root mismatch, etc.) so callers can log or alert appropriately.
    pub fn verify_membership_proof_outcome(
        &self,
        proof_bytes: &[u8],
        federation_root: &[u8; 32],
    ) -> crate::verify::VerifyOutcome {
        use crate::verify::VerifyOutcome;
        let wire_proof: WirePresentationProof = match postcard::from_bytes(proof_bytes) {
            Ok(p) => p,
            Err(e) => return VerifyOutcome::DecodeError(format!("postcard: {e}")),
        };

        // For membership-only verification, we call verify_proof_complete with
        // relaxed parameters: empty action/resource (matching what the prover used
        // for membership-only proofs) and no freshness check.
        // If the proof was generated with action binding, this will correctly
        // reject (action mismatch) — membership-only proofs use empty bindings.
        match present::verify_proof_complete(
            &wire_proof,
            "",
            "",
            federation_root,
            0,
            0, // no freshness check for membership-only
        ) {
            Ok(_) => VerifyOutcome::Ok,
            Err(e) => {
                // verify_proof_complete returns a single error type without a
                // category discriminator we can pattern-match on; surface the
                // message under StarkInvalid (the most common cause). Decode /
                // root-mismatch cases short-circuit above.
                let msg = format!("{e:?}");
                if msg.contains("root") {
                    VerifyOutcome::RootMismatch
                } else if msg.contains("freshness") || msg.contains("expired") {
                    VerifyOutcome::FreshnessExpired
                } else {
                    VerifyOutcome::StarkInvalid
                }
            }
        }
    }

    // =========================================================================
    // Token operations (pure crypto, no IO)
    // =========================================================================

    /// Mint a new root token for a service.
    ///
    /// Returns the `em2_`-encoded token string and the root key needed for
    /// future operations (verification, attenuation). The caller stores both.
    pub fn mint_token(&self, root_key: &[u8; 32], service: &str) -> Result<String, EmbedError> {
        let kid = format!("{}:{}", service, self.executor.block_height);
        let token = MacaroonToken::mint(*root_key, kid.as_bytes(), service);
        token
            .to_encoded()
            .map_err(|e| EmbedError::Token(e.to_string()))
    }

    /// Attenuate (restrict) an existing token.
    ///
    /// Takes the `em2_`-encoded token string and the root key, returns the
    /// attenuated token as a new encoded string.
    pub fn attenuate_token(
        &self,
        encoded_token: &str,
        root_key: &[u8; 32],
        restrictions: &Attenuation,
    ) -> Result<String, EmbedError> {
        let token = MacaroonToken::from_encoded(encoded_token, *root_key)
            .map_err(|e| EmbedError::Token(format!("decode: {e}")))?;
        let attenuated = token
            .attenuate(restrictions)
            .map_err(|e| EmbedError::Token(format!("attenuate: {e}")))?;
        attenuated
            .to_encoded()
            .map_err(|e| EmbedError::Token(e.to_string()))
    }

    // =========================================================================
    // State management (caller persists however they want)
    // =========================================================================

    /// Serialize the current ledger state to bytes with BLAKE3 integrity hash.
    ///
    /// The caller can persist this to their own storage (postgres, rocksdb, S3, etc).
    /// The format is postcard-encoded `Vec<Cell>` followed by a 32-byte BLAKE3 hash.
    ///
    /// The trailing 32-byte hash ensures that tampered snapshots are detected on load.
    pub fn state_snapshot(&self) -> Result<Vec<u8>, EmbedError> {
        let cells: Vec<&dregg_cell::Cell> = self.ledger.iter().map(|(_, cell)| cell).collect();
        let serialized =
            postcard::to_stdvec(&cells).map_err(|e| EmbedError::StateSerde(e.to_string()))?;
        let hash = blake3::hash(&serialized);
        let mut result = serialized;
        result.extend_from_slice(hash.as_bytes());
        Ok(result)
    }

    /// Load ledger state from a previous snapshot, verifying BLAKE3 integrity.
    ///
    /// Replaces the current ledger with the cells from the snapshot. Returns an error
    /// if the snapshot is too short to contain a hash, or if the integrity check fails
    /// (indicating the snapshot was tampered with or corrupted).
    pub fn load_state(&mut self, snapshot: &[u8]) -> Result<(), EmbedError> {
        // SECURITY: The snapshot must contain at least 32 bytes for the trailing BLAKE3 hash.
        if snapshot.len() < 32 {
            return Err(EmbedError::StateSerde(
                "snapshot too short: missing integrity hash (expected at least 32 trailing bytes)"
                    .into(),
            ));
        }

        let (data, expected_hash_bytes) = snapshot.split_at(snapshot.len() - 32);

        // Recompute the BLAKE3 hash over the data portion and compare.
        let computed_hash = blake3::hash(data);
        if computed_hash.as_bytes() != expected_hash_bytes {
            return Err(EmbedError::IntegrityCheckFailed);
        }

        let cells: Vec<dregg_cell::Cell> =
            postcard::from_bytes(data).map_err(|e| EmbedError::StateSerde(e.to_string()))?;
        let mut ledger = Ledger::new();
        for cell in cells {
            ledger
                .insert_cell(cell)
                .map_err(|e| EmbedError::StateSerde(format!("insert: {e:?}")))?;
        }
        self.ledger = ledger;
        Ok(())
    }

    /// Get a reference to the current ledger (for read-only inspection).
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    // AUDIT[P2]: `ledger_mut()` exposes a raw `&mut Ledger` that lets callers
    // mutate cell balances, replace state roots, and erase nonce gaps in ways
    // that bypass every turn-execution invariant the executor enforces. This
    // is "one-time-checked-then-discarded" in spirit: the executor verifies
    // each turn but the ledger it operates on is unconditionally writable by
    // any external caller holding `&mut DreggEngine`. Recommended fix: gate
    // `ledger_mut` behind a feature flag, or remove and replace with a
    // narrower set of authenticated mutation methods (e.g., load_snapshot
    // already exists). Severity P2 because callers with `&mut DreggEngine`
    // already have full process trust; documenting so the reviewer can decide.
    /// Get a mutable reference to the ledger (for direct manipulation).
    pub fn ledger_mut(&mut self) -> &mut Ledger {
        &mut self.ledger
    }

    // =========================================================================
    // Federation root management
    // =========================================================================

    /// Get the current federation root.
    pub fn federation_root(&self) -> [u8; 32] {
        self.federation_root
    }

    // AUDIT[P2]: `set_federation_root` and `set_max_proof_age_secs` are
    // "implicit trust based on type, not on a stored proof": the engine
    // trusts whatever the caller sets, even though the federation root is
    // the public input that every membership STARK is verified against.
    // A caller that sets `federation_root = [0u8;32]` and toggles
    // `max_proof_age_secs = 0` effectively disables freshness + binds
    // verification to a sentinel root. The current code handles
    // `[0u8; 32]` by failing closed in verify_presentation_bytes (good)
    // but nothing prevents the operator from accidentally rolling back
    // the root to a stale value. Recommended: track an internal
    // monotonic `root_version` and refuse to roll back without an
    // explicit downgrade method. Severity P2 — operator-level concern,
    // not exploitable from untrusted input.
    /// Update the federation root.
    ///
    /// The caller is responsible for fetching/verifying the root from their own
    /// sync mechanism (pull from a peer, read from a shared DB, etc).
    pub fn set_federation_root(&mut self, root: [u8; 32]) {
        self.federation_root = root;
    }

    // =========================================================================
    // Executor configuration pass-through
    // =========================================================================

    /// Update the current block height (for precondition evaluation).
    pub fn set_block_height(&mut self, height: u64) {
        self.executor.set_block_height(height);
    }

    /// Update the current timestamp (for expiration checks).
    pub fn set_timestamp(&mut self, ts: i64) {
        self.executor.set_timestamp(ts);
    }

    /// Get the maximum proof age in seconds.
    pub fn max_proof_age_secs(&self) -> i64 {
        self.max_proof_age_secs
    }

    /// Set the maximum proof age in seconds.
    ///
    /// When non-zero, `verify_presentation_bytes()` rejects proofs whose embedded
    /// timestamp is older than this many seconds from the engine's current timestamp.
    /// Set to 0 to disable freshness checks (not recommended for production).
    pub fn set_max_proof_age_secs(&mut self, secs: i64) {
        self.max_proof_age_secs = secs;
    }

    /// Get a reference to the underlying executor for advanced configuration.
    pub fn executor(&self) -> &TurnExecutor {
        &self.executor
    }

    /// Get a mutable reference to the executor for advanced configuration
    /// (e.g., setting proof verifiers, budget gates, trusted roots).
    pub fn executor_mut(&mut self) -> &mut TurnExecutor {
        &mut self.executor
    }
}

// =============================================================================
// WireCodec — protocol message parsing without transport
//
// The wire codec (encode/decode/process_message) is the networked face and
// lives in `dregg-sdk-net` (`dregg_sdk_net::WireCodec`), built over the
// wire-free `DreggEngine` core above. The core crate stays net-free so it is
// wasm-buildable.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engine_default_creation() {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        assert_eq!(engine.federation_root(), [0u8; 32]);
        assert!(engine.ledger().is_empty());
    }

    #[test]
    fn mint_and_attenuate_roundtrip() {
        let engine = DreggEngine::new(EngineConfig::for_testing());

        let root_key = b"test-root-key-32-bytes-exactly!!";
        let encoded = engine.mint_token(root_key, "my-service").unwrap();
        assert!(encoded.starts_with("em2_") || !encoded.is_empty());

        // Attenuate it.
        let restrictions = Attenuation {
            services: vec![("dns".into(), "r".into())],
            ..Default::default()
        };
        let attenuated = engine
            .attenuate_token(&encoded, root_key, &restrictions)
            .unwrap();
        assert!(!attenuated.is_empty());
        // Attenuated token should be different from root.
        assert_ne!(encoded, attenuated);
    }

    #[test]
    fn state_snapshot_roundtrip() {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        // Insert a cell into the ledger for a non-trivial state.
        let cell = dregg_cell::Cell::with_balance([1u8; 32], [0u8; 32], 1000);
        engine.ledger_mut().insert_cell(cell).unwrap();

        let snapshot = engine.state_snapshot().unwrap();
        assert!(!snapshot.is_empty());

        // Create a fresh engine and load the snapshot.
        let mut engine2 = DreggEngine::new(EngineConfig::for_testing());
        engine2.load_state(&snapshot).unwrap();
        assert!(!engine2.ledger().is_empty());
    }

    #[test]
    fn federation_root_management() {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        assert_eq!(engine.federation_root(), [0u8; 32]);

        let new_root = [0x42u8; 32];
        engine.set_federation_root(new_root);
        assert_eq!(engine.federation_root(), new_root);
    }

    #[test]
    fn verify_rejects_garbage() {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        // Garbage bytes should fail to decode or not verify.
        let result = engine.verify_presentation_bytes(&[0u8; 100], "read", "api/v1/users");
        // Either returns Err (decode failure) or Ok(false) (verification failure).
        assert!(result.is_err() || matches!(result, Ok(false)));
    }

    #[test]
    fn load_state_rejects_tampered_snapshot() {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        let cell = dregg_cell::Cell::with_balance([1u8; 32], [0u8; 32], 1000);
        engine.ledger_mut().insert_cell(cell).unwrap();

        let mut snapshot = engine.state_snapshot().unwrap();
        assert!(!snapshot.is_empty());

        // Tamper with a byte in the data portion (not the hash).
        snapshot[0] ^= 0xFF;

        // Loading the tampered snapshot must fail with IntegrityCheckFailed.
        let mut engine2 = DreggEngine::new(EngineConfig::for_testing());
        let result = engine2.load_state(&snapshot);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, EmbedError::IntegrityCheckFailed),
            "expected IntegrityCheckFailed, got: {err:?}"
        );
    }

    #[test]
    fn load_state_rejects_truncated_snapshot() {
        // A snapshot shorter than 32 bytes cannot contain a valid hash.
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        let result = engine.load_state(&[0u8; 16]);
        assert!(result.is_err());
    }

    #[test]
    fn load_state_rejects_hash_only_snapshot() {
        // A snapshot of exactly 32 bytes = an empty data portion followed by the
        // BLAKE3 of that empty data. This is the adversarial case the integrity
        // hash CANNOT catch: the trailing hash genuinely matches `blake3([])`, so
        // the integrity check PASSES. The rejection must therefore come from the
        // deserializer: `[]` is not a valid postcard `Vec<Cell>` (a real empty
        // ledger serializes to the one-byte length prefix `0x00`, never to zero
        // bytes). A snapshot whose data survives integrity but cannot be decoded
        // into a ledger must be REFUSED, not silently accepted as some default
        // (empty) ledger — otherwise an attacker who strips the payload but keeps
        // a matching hash rolls the engine to a blank ledger.
        let mut engine = DreggEngine::new(EngineConfig::for_testing());

        // Seed a non-empty ledger so a silent "accept as empty" would be a visible
        // state change we can catch.
        let cell = dregg_cell::Cell::with_balance([9u8; 32], [0u8; 32], 4242);
        engine.ledger_mut().insert_cell(cell).unwrap();
        let cells_before = engine.ledger().iter().count();
        assert_eq!(cells_before, 1, "setup: the ledger holds one cell");

        let empty_data: &[u8] = &[];
        let hash = blake3::hash(empty_data);
        let snapshot: Vec<u8> = hash.as_bytes().to_vec();
        assert_eq!(
            snapshot.len(),
            32,
            "fixture: hash-only snapshot is 32 bytes"
        );

        // The integrity check must PASS on this snapshot (the hash matches the
        // empty data) — proving the rejection below is a *deserialization*
        // refusal, not an integrity one.
        {
            let (data, expected) = snapshot.split_at(snapshot.len() - 32);
            assert!(data.is_empty(), "the data portion is empty");
            assert_eq!(
                blake3::hash(data).as_bytes(),
                expected,
                "the trailing hash genuinely matches — integrity alone cannot reject this"
            );
        }

        let result = engine.load_state(&snapshot);
        assert!(
            result.is_err(),
            "a hash-only snapshot (empty, undeserializable payload) must be rejected, \
             got Ok — the engine accepted a payload it could not decode"
        );

        // And the refused load must leave the existing ledger untouched (no
        // silent rollback to a blank ledger).
        assert_eq!(
            engine.ledger().iter().count(),
            cells_before,
            "a refused load_state must not mutate the ledger"
        );
    }
}
