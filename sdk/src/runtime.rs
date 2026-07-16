//! Agent runtime: high-level orchestration of cipherclerk, ledger, and execution.
//!
//! The [`AgentRuntime`] ties together:
//! - An agent cipherclerk (identity + tokens)
//! - A local ledger (cell state)
//! - A turn executor (atomic execution)
//!
//! It provides the highest-level API for agent operations: execute effects,
//! spawn sub-agents with attenuated capabilities, and manage the local cell.

use std::sync::{Arc, Mutex, RwLock};

use dregg_cell::{Cell, CellId, Ledger, VerificationKey};
use dregg_token::{Attenuation, AuthToken, BiscuitToken, biscuit_auth};
use dregg_turn::{
    Action, Authorization, BudgetGate, BudgetSlice, CallForest, ComputronCosts, DelegationMode,
    Effect, TokenKeyRef, Turn, TurnExecutor, TurnReceipt, TurnResult, action::symbol,
};
use dregg_types::PublicKey;
use zeroize::Zeroizing;

use crate::cipherclerk::{AgentCipherclerk, HeldToken};
use crate::error::SdkError;
use crate::raw;
use crate::turns::TurnBuilder;

/// THE SWAP (FLIPPED DEFAULT) — the VERIFIED Lean executor is the authoritative state producer on
/// this runtime's execute paths BY DEFAULT (for the swap-safe covered set), with the Rust
/// `TurnExecutor` demoted to a parallel differential cross-check. Reads an opt-OUT:
/// `DREGG_LEAN_PRODUCER=0` (or `false`/`off`/`no`) falls back to the legacy Rust-producer path; any
/// other value (or unset) keeps the verified producer ON.
///
/// Mirrors `dregg_node::state::lean_producer_env_enabled` so the node and the SDK read the SAME
/// switch. Under the `no-lean-link` platform gate (wasm32/zkvm) this always returns `false`
/// (the producer path is not compiled in), so wasm/default consumers never link the Lean archive.
pub fn lean_producer_env_enabled() -> bool {
    #[cfg(not(feature = "no-lean-link"))]
    {
        !matches!(
            std::env::var("DREGG_LEAN_PRODUCER").ok().as_deref(),
            Some("0")
                | Some("false")
                | Some("FALSE")
                | Some("off")
                | Some("OFF")
                | Some("no")
                | Some("NO")
        )
    }
    #[cfg(feature = "no-lean-link")]
    {
        false
    }
}

/// Install the Lean-verified REAL ML-DSA verify core as `dregg_pq::ml_dsa_verify`'s accept/reject AUTHORITY
/// for THIS process — taking the `fips204` crate out of the SDK-hosted process's verify TCB.
///
/// `dregg_pq::ml_dsa_verify` is the process-global ML-DSA-65 verify behind the SDK-hosted surfaces the
/// crate-TCB audit flagged: the wire `SiloServer`'s token/revocation verify (`wire/src/server.rs` sites
/// V2/V3) and the SDK's own turn/captp receipt verifies. It routes through an install-time function pointer;
/// with the REAL core installed it takes its verdict from the extracted, full-byte `MlDsaVerifyReal.verifyCore`
/// (BRICK 8) and NEVER consults the `fips204` crate. Only the node installed it before — so an SDK-hosted
/// process (or starbridge-v2) was falling through to the crate at every verify. This is the SAME shared
/// install the node performs (`dregg_pq::install_verified_mldsa_verify_core`), injecting the two
/// `dregg-lean-ffi` archive symbols; it is idempotent and once-per-process.
///
/// Gated on `fips204_verify_real_core_available()`: install ONLY when the linked archive EXPORTS the real
/// core. A build without it (or a `no-lean-link` wasm/zkvm target) keeps the `fips204`-crate fallback (a
/// valid FIPS-204 verify) rather than bricking verify. Returns the outcome so callers / the running-binary
/// gate can assert routing.
pub fn install_verified_mldsa_verify_core() -> dregg_pq::MlDsaVerifyCoreInstall {
    dregg_pq::install_verified_mldsa_verify_core(
        dregg_lean_ffi::fips204_verify_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
    )
}

/// Perform the once-per-process verify-core install at SDK agent-runtime startup, logging the outcome once.
/// Called from every [`AgentRuntime`] constructor so ANY SDK-hosted process routes its wire-silo +
/// turn/captp verifies through the Lean-verified core without the host having to remember to install.
fn ensure_verified_mldsa_verify_core_installed() {
    use dregg_pq::MlDsaVerifyCoreInstall as I;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mldsa_verify_core();
    LOGGED.call_once(|| match outcome {
        I::Installed => tracing::info!(
            "ML-DSA verify: verified Lean core installed at SDK agent-runtime startup — the extracted \
             full-byte `MlDsaVerifyReal.verifyCore` is now `dregg_pq::ml_dsa_verify`'s accept/reject \
             authority for this process (wire silo + turn/captp verifies); the `fips204` crate is out of \
             the SDK-hosted verify TCB"
        ),
        I::AlreadyInstalled => tracing::debug!(
            "ML-DSA verify: a verified Lean core was already installed this process (install is \
             once-per-process) — the `fips204` crate remains out of the SDK-hosted verify TCB"
        ),
        I::ExportAbsent => tracing::warn!(
            "ML-DSA verify: the linked Lean archive does NOT export the real verify core \
             (`fips204_verify_real_core_available()` is false) — the SDK-hosted process's ML-DSA verify \
             falls back to the `fips204` crate (a valid FIPS-204 verify, but NOT the Lean-verified \
             authority). Rebuild against a HEAD-matching archive to route verify through Lean."
        ),
    });
}

/// Build the `TurnExecutor` every [`AgentRuntime`] runs on, with the **real**
/// witnessed-predicate verifiers installed (not the fail-closed defaults).
///
/// This is the one behavioral default that makes `SenderAuthorized { PublicRoot }`
/// (and the other STARK-backed witnessed predicates whose backend lives in
/// `dregg-cell`/`dregg-circuit`) ENFORCE FOR REAL on the honest fire path: a
/// turn whose sender carries a genuine Poseidon2 Merkle-membership proof against
/// the authorized-set root is ACCEPTED, and a non-member's turn is rejected at
/// the STARK level — rather than every `SenderAuthorized` turn failing closed
/// because the default registry's `MerkleMembership` slot is a reject-everything
/// stub.
///
/// `registry_with_real_verifiers` rides `dregg-turn`'s existing `dregg-circuit`
/// dependency (the verifier links it), so this adds no new heavy dep to the SDK.
/// A host that needs fail-closed `SenderAuthorized` (e.g. a negative regression)
/// can opt out via `AgentRuntime::set_witnessed_registry(empty())`.
///
/// As of the executor-default change, `TurnExecutor::new()` ALREADY installs
/// `registry_with_real_verifiers()` (the bare executor is no longer a
/// reject-everything stub), so this helper is now just the plain constructor —
/// kept as a named seam so the SDK's intent stays explicit and so a host that
/// wants the host-context-full registry can find the upgrade path
/// (`registry_with_real_verifiers_full`) from here.
fn executor_with_real_verifiers(executor_signing_seed: Option<[u8; 32]>) -> TurnExecutor {
    let mut executor = TurnExecutor::new(ComputronCosts::default_costs());
    // ROUTE (ii): when the HOST supplies an executor signing seed, install it so
    // every committed `TurnReceipt` carries an Ed25519 `executor_signature` over
    // `canonical_executor_signed_message` (the exact bytes
    // `turn::verify_receipt_signature_with_keys` — and the forge check
    // `RequiredCheck::CommittedReceipt` — verify). `None` = today's UNSIGNED
    // behavior, byte-unchanged.
    if let Some(seed) = executor_signing_seed {
        executor.set_executor_signing_key(seed);
    }
    executor
}

/// Derive the Ed25519 executor PUBLIC key from a 32-byte signing seed — the key a
/// forge / auditor pins in `trusted_executor_keys` to admit receipts this runtime's
/// executor signed (`turn::verify_receipt_signature_with_keys`). This is exactly the
/// verifying key `TurnExecutor::maybe_sign_receipt` signs under, so a receipt this
/// runtime committed under `seed` verifies against `executor_pubkey_from_seed(&seed)`.
pub fn executor_pubkey_from_seed(seed: &[u8; 32]) -> [u8; 32] {
    ed25519_dalek::SigningKey::from_bytes(seed)
        .verifying_key()
        .to_bytes()
}

/// The default method a [`SubAgent`] is scoped to when no explicit set is
/// given: the `execute` verb its `execute()` path submits.
pub const DEFAULT_SUBAGENT_METHOD: &str = "execute";

/// Map a worker method NAME to the action string the executor's token verifier
/// matches against.
///
/// The executor binds `request.action = hex(action.method)` where
/// `action.method = symbol(name) = blake3(name)`. The biscuit authorizer fires
/// `allow if service($svc, $actions), request_service($svc), request_action($act),
/// $actions.contains($act)` — a RAW-STRING match — so the grant's action for a
/// method must be exactly `hex(symbol(name))`. Then a worker turn invoking a
/// method OUTSIDE its granted set has a `request_action` no grant `.contains`,
/// the default-deny fires, and the EXECUTOR rejects the turn.
fn method_scope_fragment(method_name: &str) -> String {
    hex::encode(symbol(method_name))
}

/// Whether an [`Attenuation`] would produce no caveats (an empty attenuation,
/// which the token backends reject). Mirrors the dimensions the macaroon /
/// biscuit caveat builders actually emit.
fn restrictions_are_empty(att: &Attenuation) -> bool {
    att.apps.is_empty()
        && att.services.is_empty()
        && att.features.is_empty()
        && att.not_after.is_none()
        && att.not_before.is_none()
        && att.confine_user.is_none()
        && att.oauth_providers.is_empty()
        && att.oauth_scopes.is_empty()
        && att.feature_globs.is_none()
        && att.budget.is_none()
}

/// Mint the ENFORCED capability credential a sub-agent carries on every turn it
/// submits: a public-key biscuit, granting `service(sub_cell, method)` for
/// EXACTLY the set of `methods` the worker may invoke.
///
/// This is the heart of internalizing the guarantee. The biscuit is minted under
/// a fresh issuer keypair; the sub-agent's cell records that issuer's public key
/// as its `verification_key` — the trust anchor the executor's
/// `verify_token_authorization` (`TokenKeyRef::BiscuitIssuer`) checks. The worker
/// presents the credential as `Authorization::Token` on its turn, so the EXECUTOR
/// — not an out-of-band `cap.verify()` — admits or rejects: a turn whose method
/// is outside the granted set has no covering `service(...)` grant, the biscuit's
/// default-deny fires, and the executor rejects with
/// `TokenInsufficientCapability`.
///
/// The service name is the sub-agent's cell id (hex) and each granted action is
/// `hex(symbol(method))`, mirroring exactly what the executor binds from
/// `(action.target, action.method)`.
///
/// Returns `(encoded_biscuit, issuer_pubkey)`.
fn mint_subagent_cap_token(
    sub_cell: CellId,
    methods: &[&str],
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    mint_subagent_cap_token_with_keypair(sub_cell, methods, biscuit_auth::KeyPair::new())
}

/// DETERMINISTIC twin of [`mint_subagent_cap_token`]: mint the worker's
/// capability biscuit under an issuer keypair rebuilt from `issuer_seed`
/// instead of a fresh random one. Same credential shape, same executor trust
/// anchor — the ONLY difference is that the same seed reproduces the same
/// issuer across process restarts, so a credential minted in an earlier epoch
/// still verifies against the recreated cell's `verification_key`.
///
/// # Security contract
///
/// `issuer_seed` IS the issuer's ed25519 private key. The caller must derive it
/// from an already-custodied secret with strict domain separation (e.g.
/// `blake3::derive_key("app.component.biscuit-issuer.vN", root_secret)`), must
/// never reuse it for any other key role, and must never persist the derived
/// seed or the issuer private key — only the custodied root secret.
fn mint_subagent_cap_token_seeded(
    sub_cell: CellId,
    methods: &[&str],
    issuer_seed: &[u8; 32],
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    let private =
        biscuit_auth::PrivateKey::from_bytes(issuer_seed, biscuit_auth::Algorithm::Ed25519)
            .map_err(|e| {
                SdkError::MissingKey(format!(
                    "issuer seed is not a valid biscuit ed25519 private key: {e}"
                ))
            })?;
    mint_subagent_cap_token_with_keypair(sub_cell, methods, biscuit_auth::KeyPair::from(&private))
}

/// Shared body for [`mint_subagent_cap_token`] / [`mint_subagent_cap_token_seeded`]:
/// mint the worker's `service(sub_cell, method)` biscuit under `kp`.
fn mint_subagent_cap_token_with_keypair(
    sub_cell: CellId,
    methods: &[&str],
    kp: biscuit_auth::KeyPair,
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    let issuer: [u8; 32] = kp
        .public()
        .to_bytes()
        .try_into()
        .expect("ed25519 public key is 32 bytes");
    let svc = hex::encode(sub_cell.as_bytes());
    // One service grant per allowed method: `service(cell_hex, hex(symbol(m)))`.
    // The authorizer's `$actions.contains($act)` then matches exactly the
    // request action `hex(action.method)` for an in-scope verb and nothing else.
    let services: Vec<(String, String)> = methods
        .iter()
        .map(|m| (svc.clone(), method_scope_fragment(m)))
        .collect();
    let token = BiscuitToken::mint_dregg(&kp, &[], &services, &[], &[], &[], None)
        .map_err(SdkError::Token)?;
    let encoded = token.to_encoded().map_err(SdkError::Token)?.into_bytes();
    Ok((encoded, issuer))
}

/// The agent runtime: orchestrates cipherclerk, ledger, and execution.
///
/// This is the top-level coordination layer for an agent. It manages:
/// - The agent's cell in the local ledger
/// - Turn construction and execution
/// - Sub-agent spawning with attenuated capabilities
///
/// The cipherclerk is held behind an `Arc<RwLock<...>>` so that the runtime can
/// append receipts after successful turn execution (mutating the receipt chain
/// and IVC state), while still allowing shared read access for signing and
/// token operations.
///
/// # Example
///
/// ```no_run
/// use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};
/// use dregg_types::CellId;
/// use std::sync::{Arc, RwLock};
///
/// let cipherclerk = Arc::new(RwLock::new(AgentCipherclerk::new()));
/// let runtime = AgentRuntime::new(cipherclerk, "my-domain");
///
/// // Execute effects against the local ledger
/// let receipt = runtime.execute(vec![
///     Effect::IncrementNonce { cell: runtime.cell_id() },
/// ]).unwrap();
/// ```
pub struct AgentRuntime {
    /// The agent's cipherclerk (read-write lock for receipt chain mutation).
    cipherclerk: Arc<RwLock<AgentCipherclerk>>,
    /// The agent's cell ID in the local domain.
    cell_id: CellId,
    /// The domain this runtime operates in.
    domain: String,
    /// The local ledger (shared, thread-safe).
    ledger: Arc<Mutex<Ledger>>,
    /// The turn executor.
    executor: TurnExecutor,
    /// Current nonce for the agent's cell (tracks submitted turns).
    nonce: Mutex<u64>,
    /// THE SWAP — producer mode (authority inversion). When `true`, [`Self::execute`] and
    /// [`Self::execute_turn`] make the VERIFIED Lean executor the authoritative state PRODUCER
    /// (`dregg_turn::lean_apply::produce_via_lean`): the committed ledger is reconstituted from the
    /// Lean FFI's post-state, and the Rust [`TurnExecutor`] is demoted to a parallel runtime
    /// DIFFERENTIAL cross-check (a divergence is logged loudly as a real soundness finding). The
    /// verified producer installs its state only for the swap-safe covered set; a root-gap or
    /// unmappable effect falls back to Rust for that turn. Default mirrors `DREGG_LEAN_PRODUCER`
    /// (ON unless `DREGG_LEAN_PRODUCER=0`); `false` is the legacy Rust-producer path. Only ever
    /// `true` on every native build (Lean unconditional; gated OUT only by `no-lean-link`); an unlinked archive
    /// self-falls-back per turn.
    lean_producer_enabled: bool,
    /// ROUTE (ii) — the HOST executor signing seed, or `None` for today's UNSIGNED
    /// default. When `Some`, this runtime's own executor AND every worker
    /// [`SubAgent`] it spawns (the grain drive path) sign every committed
    /// `TurnReceipt`'s `executor_signature` (Ed25519 over
    /// `canonical_executor_signed_message`), so a grain turn is forge-admissible
    /// (`turn::verify_receipt_signature_with_keys` against [`Self::executor_pubkey`]
    /// passes). Additive: `None` leaves the pre-existing behavior byte-unchanged.
    executor_signing_seed: Option<[u8; 32]>,
}

impl AgentRuntime {
    /// Create a new agent runtime with simplified ownership.
    ///
    /// This is a convenience constructor that wraps the cipherclerk in `Arc<RwLock<...>>`
    /// internally, so callers don't need to manage the synchronization primitives
    /// themselves.
    ///
    /// # Arguments
    ///
    /// * `cipherclerk` - The agent's cipherclerk (moved into the runtime).
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    ///
    /// # Example
    ///
    /// ```no_run
    /// use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    ///
    /// let cipherclerk = AgentCipherclerk::new();
    /// let runtime = AgentRuntime::new_simple(cipherclerk, "my-domain");
    /// ```
    pub fn new_simple(cipherclerk: AgentCipherclerk, domain: &str) -> Self {
        Self::new(Arc::new(RwLock::new(cipherclerk)), domain)
    }

    /// Create a new agent runtime.
    ///
    /// Initializes the local ledger with the agent's cell (funded with a default
    /// balance for local execution). The domain determines the agent's cell ID.
    ///
    /// # Arguments
    ///
    /// * `cipherclerk` - Shared read-write reference to the agent's cipherclerk.
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    pub fn new(cipherclerk: Arc<RwLock<AgentCipherclerk>>, domain: &str) -> Self {
        // Route this SDK-hosted process's ML-DSA verify (wire silo + turn/captp) through the
        // Lean-verified core (idempotent, once-per-process) — see
        // [`ensure_verified_mldsa_verify_core_installed`].
        ensure_verified_mldsa_verify_core_installed();
        let cell_id;
        let public_key;
        {
            // Recover from poisoned lock rather than cascading panics.
            // A poisoned RwLock means a writer panicked while holding the lock;
            // we accept the potentially-inconsistent state as preferable to
            // bringing down the entire runtime.
            let w = cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            cell_id = w.cell_id(domain);
            public_key = w.public_key();
        }
        let mut ledger = Ledger::new();

        // Create the agent's cell with a generous initial balance for local use.
        let agent_cell = Cell::with_balance(
            public_key.0,
            *blake3::hash(domain.as_bytes()).as_bytes(),
            1_000_000, // 1M computrons initial balance
        );
        ledger
            .insert_cell(agent_cell)
            .expect("fresh ledger, no conflict");

        let executor = executor_with_real_verifiers(None);
        {
            let w = cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            if let Some(head) = w.receipt_head() {
                executor.set_last_receipt_hash(cell_id, head.receipt_hash());
            }
        }

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger: Arc::new(Mutex::new(ledger)),
            executor,
            nonce: Mutex::new(0),
            lean_producer_enabled: lean_producer_env_enabled(),
            executor_signing_seed: None,
        }
    }

    /// Create a runtime with a pre-existing ledger.
    ///
    /// Use this when the ledger is shared with other components or has been
    /// restored from persistent storage.
    pub fn with_ledger(
        cipherclerk: Arc<RwLock<AgentCipherclerk>>,
        domain: &str,
        ledger: Arc<Mutex<Ledger>>,
    ) -> Self {
        // Same once-per-process verify-core install as `new` (this is an independent construction path).
        ensure_verified_mldsa_verify_core_installed();
        let cell_id = cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .cell_id(domain);
        let executor = executor_with_real_verifiers(None);

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger,
            executor,
            nonce: Mutex::new(0),
            lean_producer_enabled: lean_producer_env_enabled(),
            executor_signing_seed: None,
        }
    }

    /// ROUTE (ii) — install a HOST executor signing seed on this runtime (builder
    /// form), so every committed receipt — this runtime's own AND every worker
    /// [`SubAgent`] it spawns (the grain drive path) — is Ed25519-signed over
    /// `canonical_executor_signed_message`. This is what makes a grain turn's
    /// receipt FORGE-ADMISSIBLE: `turn::verify_receipt_signature_with_keys` against
    /// [`Self::executor_pubkey`] passes, exactly the check
    /// `RequiredCheck::CommittedReceipt` runs. Without it the runtime keeps today's
    /// UNSIGNED behavior (`executor_signature == None`) — additive, opt-in.
    pub fn with_executor_signing_key(mut self, seed: [u8; 32]) -> Self {
        self.executor_signing_seed = Some(seed);
        self.executor.set_executor_signing_key(seed);
        self
    }

    /// Install the HOST executor signing seed after construction (see
    /// [`Self::with_executor_signing_key`]). The signed path is opt-in; the seed
    /// threads into every worker [`SubAgent`] this runtime spawns AFTERWARD.
    pub fn set_executor_signing_key(&mut self, seed: [u8; 32]) {
        self.executor_signing_seed = Some(seed);
        self.executor.set_executor_signing_key(seed);
    }

    /// The HOST executor signing seed installed on this runtime, if any.
    pub fn executor_signing_seed(&self) -> Option<[u8; 32]> {
        self.executor_signing_seed
    }

    /// The Ed25519 executor PUBLIC key this runtime signs receipts under (derived
    /// from the installed seed via [`executor_pubkey_from_seed`]), or `None` if no
    /// seed is installed. A forge / auditor pins this in `trusted_executor_keys` to
    /// admit the runtime's — and its grains' — signed receipts.
    pub fn executor_pubkey(&self) -> Option<[u8; 32]> {
        self.executor_signing_seed
            .as_ref()
            .map(executor_pubkey_from_seed)
    }

    /// Get the agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get the domain this runtime operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get a reference to the ledger.
    pub fn ledger(&self) -> &Arc<Mutex<Ledger>> {
        &self.ledger
    }

    /// Get the agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }

    /// Get a reference to the cipherclerk (behind RwLock).
    ///
    /// Callers should use `.read().unwrap_or_else(|e| e.into_inner())` for read
    /// access or `.write().unwrap_or_else(|e| e.into_inner())` for mutation
    /// (e.g., enabling IVC, minting tokens).
    pub fn cipherclerk(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn cclerk(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        self.cipherclerk()
    }

    /// Attach a budget gate (Stingray bounded counter) to this runtime's executor.
    ///
    /// When set, each turn execution will check the silo's local budget slice
    /// before proceeding. If the slice cannot cover the turn fee, the turn is
    /// rejected with `TurnError::BudgetExhausted`.
    ///
    /// Call this when the agent's current silo has provided a budget slice via
    /// the StingrayCounter (dregg_coord::StingrayCounter).
    pub fn set_budget_gate(&mut self, silo_id: u32, slice: BudgetSlice) {
        self.executor
            .set_budget_gate(BudgetGate::new(silo_id, slice));
    }

    /// Set the federation id used by the embedded executor for signature
    /// verification. Must match the federation id used to sign actions.
    pub fn set_local_federation_id(&mut self, id: [u8; 32]) {
        self.executor.set_local_federation_id(id);
    }

    /// The federation id the embedded executor verifies action signatures
    /// against (see [`Self::set_local_federation_id`]).
    pub fn local_federation_id(&self) -> [u8; 32] {
        self.executor.local_federation_id
    }

    /// Set the block height the embedded executor evaluates time-gated
    /// program constraints against (`TemporalGate` and friends, via
    /// `EvalContext.block_height`).
    ///
    /// A node-driven executor gets this from consensus; a local runtime
    /// defaults to 0. The settlement-cell timeout/deadline gates built by
    /// [`crate::factories`] read this height.
    pub fn set_block_height(&mut self, height: u64) {
        self.executor.set_block_height(height);
    }

    /// The block height the embedded executor currently evaluates
    /// time-gated program constraints against. Turn builders that must
    /// stamp the execution height (the identity pre-rotation rotate verb,
    /// [`crate::identity`]) read it here.
    pub fn block_height(&self) -> u64 {
        self.executor.block_height
    }

    /// The executor's recorded receipt-chain head for `agent` (the hash a
    /// directly-built [`Turn::previous_receipt_hash`] must carry to satisfy the
    /// executor's `check_previous_receipt_hash`), or `None` if `agent` has
    /// committed no turn yet.
    ///
    /// Callers who hand-assemble a [`Turn`] for an agent that has already acted
    /// (e.g. a governed identity cell that adopted itself, then is driven by a
    /// custom-authorized rotation) read the chain head here rather than passing
    /// `None` and tripping `ReceiptChainMismatch`.
    pub fn agent_receipt_head(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.executor.get_last_receipt_hash(agent)
    }

    /// Replace this runtime's executor's witnessed-predicate registry.
    ///
    /// `AgentRuntime` defaults (via [`executor_with_real_verifiers`]) to the
    /// REAL STARK-backed registry, so `SenderAuthorized { PublicRoot }` and the
    /// other `dregg-circuit`-backed witnessed predicates enforce for real. Call
    /// this to install a different registry — e.g.
    /// `dregg_cell::WitnessedPredicateRegistry::empty()` for a negative test that
    /// wants fail-closed `SenderAuthorized`, or
    /// `dregg_turn::executor::registry_with_real_verifiers_full(..)` to add the
    /// host-context-dependent kinds (Dfa / Temporal / BlindedSet issuer-root).
    pub fn set_witnessed_registry(&mut self, registry: dregg_cell::WitnessedPredicateRegistry) {
        self.executor.set_witnessed_registry(registry);
    }

    /// Deploy a [`FactoryDescriptor`] into this runtime's executor.
    ///
    /// Once deployed, an `Effect::CreateCellFromFactory` referencing the
    /// descriptor's `factory_vk` is admitted (the executor validates the
    /// creation params against the descriptor and births the child cell with
    /// the descriptor's `state_constraints` installed as its `CellProgram`,
    /// so the factory's slot caveats bite on every subsequent turn). Returns
    /// the deployed `factory_vk`.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        self.executor.deploy_factory(descriptor)
    }

    /// THE SWAP — toggle producer mode on this runtime (authority inversion).
    ///
    /// When enabled, [`Self::execute`] / [`Self::execute_turn`] route the committed state through
    /// the VERIFIED Lean executor (`dregg_turn::lean_apply::produce_via_lean`) and demote the Rust
    /// `TurnExecutor` to a logged differential. The constructors default this to
    /// [`lean_producer_env_enabled`] (ON unless `DREGG_LEAN_PRODUCER=0`); use this to set it
    /// explicitly (e.g. an app that wires the producer path from its own config field rather than
    /// the env var).
    ///
    /// Has NO effect under the `no-lean-link` platform gate — there the
    /// producer path is not compiled in and execution always uses the legacy Rust producer.
    pub fn set_lean_producer(&mut self, enabled: bool) {
        self.lean_producer_enabled = enabled;
    }

    /// Whether producer mode (the verified Lean executor as the authoritative state producer) is
    /// active on this runtime. See [`Self::set_lean_producer`].
    pub fn lean_producer_enabled(&self) -> bool {
        self.lean_producer_enabled
    }

    /// Run one fully-built turn against `ledger`, choosing the PRODUCER per [`Self::lean_producer_enabled`].
    ///
    /// THE SWAP authority inversion (Stage 0) lives here: when producer mode is on (and the crate
    /// was built by default on native), on the COVERED set the VERIFIED Lean executor is
    /// AUTHORITATIVE via `dregg_turn::lean_apply::produce_via_lean` — its post-state AND its commit
    /// verdict are committed unconditionally — and the Rust `TurnExecutor` is demoted to a checked
    /// reference. A Lean↔Rust disagreement on a covered turn is a surfaced RUST BUG (`error!`), NOT a
    /// fallback to Rust: the verified verdict is what was committed. The returned [`TurnResult`]
    /// follows the AUTHORITATIVE (Lean) verdict, with the receipt's `post_state_hash` pinned to the
    /// installed Lean root.
    ///
    /// When producer mode is off — or the turn is outside the covered set (an uncovered/root-gap
    /// effect) — this is the legacy `self.executor.execute(turn, ledger)` path, explicitly FENCED
    /// (the uncovered partition is named + surfaced, not a silent Rust default).
    fn run_turn(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        produce(&self.executor, turn, ledger, self.lean_producer_enabled)
    }

    /// Open the typed turn builder — the SDK's one public turn shape:
    /// `runtime.turn().transfer(..).write(..).sign()?.submit()` →
    /// [`crate::Receipt`].
    ///
    /// See [`crate::turns`] for the verbs. The legacy `execute*` methods
    /// below are the same authorized flow without the staging surface.
    pub fn turn(&self) -> TurnBuilder<'_> {
        TurnBuilder::new(self)
    }

    /// Sign `unsigned` with this runtime's cipherclerk key over the
    /// canonical federation-bound signing message. The authorization field
    /// of the input is ignored (zeroed for the message) and replaced with a
    /// real `Authorization::HybridSignature` — this is the ONLY way an action
    /// leaves the runtime.
    ///
    /// HYBRID (ed25519 + ML-DSA-65): the runtime signer routes through the
    /// cipherclerk's [`AgentCipherclerk::sign_action_hybrid`] path — the SAME
    /// seed-derived keys (the ML-DSA half from the ed25519 secret seed via
    /// `MlDsaTurnKey::from_ed25519_seed`) and the SAME canonical signing
    /// message (`TurnExecutor::compute_signing_message`, authorization zeroed
    /// to `Unchecked`) the SDK cipherclerk uses. This makes every AgentRuntime
    /// turn carry the post-quantum half, so the runtime path is `require_pq`-
    /// acceptable rather than a live classical-only producer.
    ///
    /// `turn_nonce` must be the nonce the submitted turn will carry
    /// (`dregg-action-sig-v3` binds it into the signing message): the
    /// runtime's own counter for agent turns
    /// ([`Self::next_agent_turn_nonce`]), or the CELL's on-ledger replay
    /// counter for cell-agent turns (`execute_as`).
    pub(crate) fn sign_action_for_runtime(&self, unsigned: Action, turn_nonce: u64) -> Action {
        self.cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .sign_action_hybrid(unsigned, &self.executor.local_federation_id, turn_nonce)
    }

    /// The nonce the next AGENT turn will be submitted under — the value
    /// `submit_signed_action_as_agent` draws from the runtime counter.
    pub(crate) fn next_agent_turn_nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }

    /// Submit a SIGNED root action as an ordinary agent turn: this agent
    /// pays `fee`, the turn rides the runtime nonce, and the committed
    /// receipt is appended to the identity's receipt chain.
    ///
    /// This is the shared core under [`Self::execute`], [`Self::execute_on`]
    /// and [`crate::turns::AuthorizedTurn::submit`].
    pub(crate) fn submit_signed_action_as_agent(
        &self,
        action: Action,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        let mut forest = CallForest::new();
        forest.add_root(action);

        // LOCK ORDER: ledger → nonce → cipherclerk (canonical order to prevent deadlock).
        let mut ledger = self.ledger.lock().unwrap();

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Bind this turn to the receipt chain: read the latest receipt hash from the cipherclerk.
        let previous_receipt_hash = self
            .cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .receipt_head()
            .map(|r| r.receipt_hash());

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // Execute against the local ledger (producer mode routes through the verified Lean executor
        // when enabled; otherwise the legacy Rust producer). See [`Self::run_turn`].
        let result = self.run_turn(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Release ledger lock before taking cipherclerk write lock.
                drop(ledger);
                // Append the receipt to the cipherclerk's chain (write lock).
                // Strict mode: surface fork detection as an SdkError instead of
                // silently rewriting the receipt's `previous_receipt_hash`.
                self.cipherclerk
                    .write()
                    .unwrap_or_else(|e| e.into_inner())
                    .append_receipt(receipt.clone())?;
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Submit a SIGNED root action as a cell-agent turn: `cell` is the turn
    /// agent and pays `fee` from its own balance; the receipt belongs to the
    /// cell's history (NOT appended to this identity's chain).
    pub(crate) fn submit_signed_action_as_cell(
        &self,
        cell: CellId,
        action: Action,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        let mut forest = CallForest::new();
        forest.add_root(action);
        let mut ledger = self.ledger.lock().unwrap();
        // The turn nonce must equal the agent CELL's on-ledger replay counter.
        let nonce = ledger
            .get(&cell)
            .ok_or(SdkError::Turn(dregg_turn::TurnError::CellNotFound {
                id: cell,
            }))?
            .state
            .nonce();
        let turn = Turn {
            agent: cell,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        match self.run_turn(&turn, &mut ledger) {
            TurnResult::Committed { receipt, .. } => Ok(receipt),
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Execute a list of effects against the local ledger.
    ///
    /// Wraps the effects into a turn, signs it, and executes it atomically.
    /// On success, the ledger is updated and a receipt is returned.
    ///
    /// Equivalent to `self.turn().effects(effects).sign()?.submit()` minus
    /// the [`crate::Receipt`] wrapper — the typed builder is the preferred
    /// public shape.
    ///
    /// # Arguments
    ///
    /// * `effects` - The effects to execute (state changes, transfers, etc.)
    ///
    /// # Returns
    ///
    /// A [`TurnReceipt`] proving the turn was committed, or an error if
    /// execution was rejected.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        // Sign before acquiring the ledger lock since signing is pure.
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(self.cell_id, "execute", effects),
            self.next_agent_turn_nonce(),
        );
        self.submit_signed_action_as_agent(action, 10_000)
    }

    /// Execute effects in a turn whose agent (and action target) is `cell`
    /// rather than this runtime's own agent cell — `cell` PAYS `fee` from its
    /// own balance, and `fee` is the turn's computron budget.
    ///
    /// The action is signed with this runtime's cipherclerk key, so this only
    /// commits for cells whose `owner_pubkey` IS this runtime's public key
    /// (the executor verifies the Ed25519 signature against the target cell's
    /// key). The canonical use is the one-time capability bootstrap of a
    /// factory-born cell (see [`crate::factories`]): the cell self-grants its
    /// creator a c-list capability, after which the creator drives it with
    /// ordinary agent-paid turns via [`Self::execute_on`].
    ///
    /// Differences from [`Self::execute`]:
    /// * `turn.agent = cell` — the turn nonce is the CELL's on-ledger replay
    ///   counter (read fresh under the ledger lock), not the runtime's;
    /// * `fee` is debited from the CELL (budget for the turn's computrons);
    /// * the receipt is returned but NOT appended to the runtime's receipt
    ///   chain (it belongs to `cell`'s history, not the agent's).
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_as(
        &self,
        cell: CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        // The signature binds the turn nonce (`dregg-action-sig-v3`), and a
        // cell-agent turn rides the CELL's on-ledger replay counter — read it
        // fresh, sign over it, then submit (which re-reads the same counter).
        let turn_nonce = {
            let ledger = self.ledger.lock().unwrap();
            ledger
                .get(&cell)
                .ok_or(SdkError::Turn(dregg_turn::TurnError::CellNotFound {
                    id: cell,
                }))?
                .state
                .nonce()
        };
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(cell, "execute", effects),
            turn_nonce,
        );
        self.submit_signed_action_as_cell(cell, action, fee)
    }

    /// Execute effects in an ordinary agent turn (this runtime's agent pays
    /// the fee) whose ACTION TARGETS `target` instead of the agent cell.
    ///
    /// This is the production shape for driving a cell the agent administers
    /// (the node's app-cell ingress uses it for factory-born cells): the
    /// action is signed with this runtime's key and the executor verifies it
    /// against `target`'s `owner_pubkey`, per-effect checks ride on
    /// `effect.cell == action.target`, and the parent gate requires the agent
    /// to hold a c-list capability on `target` (bootstrap one via the cell's
    /// self-grant — see [`crate::factories`] `adopt_effects`). The target
    /// cell's installed `CellProgram` decides whether the transition commits.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_on(
        &self,
        target: CellId,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, SdkError> {
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(target, "execute", effects),
            self.next_agent_turn_nonce(),
        );
        self.submit_signed_action_as_agent(action, 10_000)
    }

    /// Execute a pre-built turn against the local ledger.
    ///
    /// Use this when you need full control over the turn structure (multiple
    /// root actions, child actions, custom authorization, etc.)
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_turn(&self, turn: &Turn) -> Result<TurnReceipt, SdkError> {
        // LOCK ORDER: ledger → nonce → cipherclerk (canonical order to prevent deadlock).
        let mut ledger = self.ledger.lock().unwrap();
        // The cipherclerk's make_turn paths default fee to 0 and nonce to 0;
        // if the caller hasn't set them, fill in sensible defaults so budget
        // and replay checks pass.
        let mut turn = turn.clone();
        if turn.fee == 0 {
            turn.fee = 10_000;
        }
        {
            let mut n = self.nonce.lock().unwrap();
            if turn.nonce == 0 && *n > 0 {
                turn.nonce = *n;
            }
            // Ensure the runtime nonce tracker stays ahead of this turn.
            if turn.nonce >= *n {
                *n = turn.nonce + 1;
            }
        }
        // Producer mode routes through the verified Lean executor when enabled (see `run_turn`).
        let result = self.run_turn(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Release ledger lock before taking cipherclerk write lock.
                drop(ledger);
                // The cipherclerk holds THIS runtime agent's (`self.cell_id`)
                // receipt chain — a single linear history. A turn whose agent IS
                // this runtime's agent extends that chain. A turn that DRIVES a
                // DIFFERENT cell (e.g. a governed identity cell rotated by a
                // custom-auth attestation, `turn.agent != self.cell_id`) belongs
                // to THAT cell's own per-agent history; the executor already
                // tracks it under its own authority head (`last_receipt_hash`),
                // and the turn's `previous_receipt_hash` links to THAT head, not
                // this agent's. Appending it here would splice a foreign-agent
                // receipt onto this agent's linear chain (its `prev` points at the
                // driven cell's head, never this chain's head) — a spurious
                // `ReceiptChainMismatch`. This mirrors `submit_signed_action_as_cell`,
                // which deliberately does NOT append a cell-agent turn to this
                // identity's chain.
                if receipt.agent == self.cell_id {
                    // Strict mode: surface fork detection as an SdkError.
                    self.cipherclerk
                        .write()
                        .unwrap_or_else(|e| e.into_inner())
                        .append_receipt(receipt.clone())?;
                }
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Spawn a sub-agent with attenuated capabilities.
    ///
    /// Creates a new agent (fresh cipherclerk + cell) with capabilities derived from
    /// this agent's tokens, narrowed by the given restrictions. The sub-agent
    /// operates on the same ledger but with reduced authority.
    ///
    /// The sub-agent is scoped to the single [`DEFAULT_SUBAGENT_METHOD`] verb its
    /// [`SubAgent::execute`] path uses. Use [`Self::spawn_sub_agent_scoped`] to
    /// grant a worker an explicit set of method verbs.
    ///
    /// # Arguments
    ///
    /// * `restrictions` - Restrictions to apply to the delegated token.
    /// * `token` - The parent token to delegate from.
    ///
    /// # Returns
    ///
    /// A [`SubAgent`] with its own cipherclerk and attenuated token.
    pub fn spawn_sub_agent(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
    ) -> Result<SubAgent, SdkError> {
        self.spawn_sub_agent_scoped(restrictions, token, &[DEFAULT_SUBAGENT_METHOD])
    }

    /// Spawn a sub-agent scoped to an explicit set of method verbs.
    ///
    /// Identical to [`Self::spawn_sub_agent`], but the worker's ENFORCED
    /// capability credential (the public-key biscuit it presents as
    /// `Authorization::Token` on every turn) grants exactly `allowed_methods`.
    /// The EXECUTOR — not an out-of-band `cap.verify()` — rejects a worker turn
    /// whose method is outside this set (`TokenInsufficientCapability`). This is
    /// the in-runtime admission gate: the credential the worker carries IS the
    /// boundary.
    pub fn spawn_sub_agent_scoped(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
    ) -> Result<SubAgent, SdkError> {
        // Fresh random identity + fresh random biscuit issuer (the pre-existing
        // behavior, byte-for-byte).
        self.spawn_sub_agent_scoped_with(
            restrictions,
            token,
            allowed_methods,
            AgentCipherclerk::new(),
            None,
        )
    }

    /// DETERMINISTIC twin of [`Self::spawn_sub_agent_scoped`]: rebuild the
    /// worker's committed identity from seeds instead of fresh randomness.
    ///
    /// `worker_seed` is the worker cipherclerk's ed25519 signing key
    /// ([`AgentCipherclerk::from_key_bytes`]) — it fixes the worker's public key
    /// and therefore its [`CellId`] in this runtime's domain. `issuer_seed` is
    /// the biscuit issuer's ed25519 private key — it fixes the issuer public key
    /// recorded as the worker cell's `verification_key` (the executor's trust
    /// anchor for the worker's capability credential). Calling this again with
    /// the same seeds — even on a FRESH runtime and ledger after a process
    /// restart — reproduces the same worker cell id and the same
    /// `verification_key`, so a capability credential minted in an earlier
    /// epoch still verifies against the recreated cell.
    ///
    /// # Security contract
    ///
    /// Both seeds are PRIVATE KEYS. The caller must derive them from an
    /// already-custodied secret with strict domain separation (e.g.
    /// `blake3::derive_key("app.component.worker-key.vN", root_secret)` /
    /// `".biscuit-issuer.vN"`), must use distinct domains for the two seeds,
    /// and must never persist the derived seeds or the issuer private key —
    /// only the custodied root secret. The seeds are zeroized here after use.
    ///
    /// Pair the seeds one-to-one: the worker cell insert is idempotent, so
    /// spawning the same `worker_seed` into the same ledger again keeps the
    /// FIRST recorded `verification_key` — a second spawn under a different
    /// `issuer_seed` would mint a credential the executor then refuses.
    pub fn spawn_sub_agent_scoped_seeded(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
        worker_seed: [u8; 32],
        issuer_seed: [u8; 32],
    ) -> Result<SubAgent, SdkError> {
        let sub_cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(worker_seed));
        let issuer_seed = Zeroizing::new(issuer_seed);
        self.spawn_sub_agent_scoped_with(
            restrictions,
            token,
            allowed_methods,
            sub_cclerk,
            Some(&issuer_seed),
        )
    }

    /// Shared spawn body: everything after worker-identity/issuer selection is
    /// identical between the random ([`Self::spawn_sub_agent_scoped`]) and
    /// seeded ([`Self::spawn_sub_agent_scoped_seeded`]) paths.
    fn spawn_sub_agent_scoped_with(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
        mut sub_cclerk: AgentCipherclerk,
        issuer_seed: Option<&[u8; 32]>,
    ) -> Result<SubAgent, SdkError> {
        let sub_pk = sub_cclerk.public_key();

        // The delegated (narration) HeldToken must carry at least one caveat —
        // an empty attenuation is rejected. When the caller relies purely on
        // `allowed_methods` and passes empty `restrictions`, narrow the
        // delegated token to those method verbs as a service grant so the
        // narration token is itself scoped and the attenuation is non-empty.
        let effective_restrictions = if restrictions_are_empty(restrictions) {
            // A `feature` caveat naming the worker's scope keeps the (legacy,
            // out-of-band) delegation token itself narrowed and the attenuation
            // non-empty. The ENFORCED gate is the biscuit `cap_token` minted
            // below; this token is the redundant defense-in-depth presentation.
            Attenuation {
                features: allowed_methods
                    .iter()
                    .map(|m| format!("subagent-method:{m}"))
                    .collect(),
                ..Default::default()
            }
        } else {
            restrictions.clone()
        };

        // Attenuate the token for the sub-agent.
        let decoded = token.decode()?;
        let attenuated_boxed = decoded.attenuate(&effective_restrictions)?;
        let encoded = attenuated_boxed.to_encoded()?;

        let token_id = format!("sub:{}:{}", token.id(), sub_pk.short_hex());
        let delegated_label = format!("delegated:{}", token.service());

        // SECURITY: The sub-agent receives an attenuated token with zeroed root_key.
        // It cannot mint new root tokens or bypass the attenuation chain.
        // However, it carries the derived issuer_key for ZK proof generation.
        // The issuer_key is always the derived proof key (never the raw root key).
        let issuer_key = *token.issuer_key();
        // Carry the parent's effect-mask authority projection forward (monotone — the
        // sub-agent's `granted` can never exceed the parent's `held`).
        let delegated_token = HeldToken::new_attenuated(
            delegated_label.clone(),
            token.service().to_string(),
            encoded.clone(),
            token_id.clone(),
            issuer_key,
            token.narrowed_authority(),
        );

        // Pass through the issuer_key as the proof_key for the sub-agent's delegation.
        // Since issuer_key is already a one-way derivation (never the raw root key),
        // it's safe to transmit to the sub-agent.
        let proof_key = if issuer_key != [0u8; 32] {
            Some(issuer_key)
        } else {
            None
        };

        // Local (in-process) sub-agent spawning. We use the typed `LocalDelegation`
        // path so this code can never accidentally normalize an externally-sourced
        // unsigned token. The local envelope is still signature-bound (under a
        // distinct domain tag), and the receiver verifies it against the parent
        // cipherclerk's public key.
        let parent_pubkey = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.public_key()
        };
        let local = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.make_local_delegation(
                encoded,
                token.service().to_string(),
                delegated_label,
                token_id,
                sub_pk,
                effective_restrictions.clone(),
                proof_key,
                None, // no pre-generated membership proof in this path
                None, // no caveat_chain_hash; sub-agent operates on local state
            )
        };
        sub_cclerk.receive_local_delegation(local, &parent_pubkey)?;

        let sub_cell_id = sub_cclerk.cell_id(&self.domain);

        // Mint the ENFORCED capability credential the worker carries on every
        // turn: a public-key biscuit granting `service(sub_cell, method)` for
        // exactly `allowed_methods`. The worker presents this as
        // `Authorization::Token`, so the EXECUTOR's `verify_token_authorization`
        // — not an out-of-band `cap.verify()` — is the real admission gate.
        let federation_id = self.executor.local_federation_id;
        let (cap_token, cap_issuer) = match issuer_seed {
            None => mint_subagent_cap_token(sub_cell_id, allowed_methods)?,
            Some(seed) => mint_subagent_cap_token_seeded(sub_cell_id, allowed_methods, seed)?,
        };
        let cap_methods: Vec<String> = allowed_methods.iter().map(|m| m.to_string()).collect();

        // Create the sub-agent's cell in the ledger, recording the biscuit
        // issuer's public key as the cell's `verification_key` — the trust anchor
        // the executor checks (`TokenKeyRef::BiscuitIssuer` requires the issuer to
        // equal the target cell's pk or its verification key). This binds the
        // worker's credential to ITS OWN cell: a credential issued by any other
        // key is rejected by the executor.
        {
            let mut ledger = self.ledger.lock().unwrap();
            let mut sub_cell = Cell::with_balance(
                sub_pk.0,
                *blake3::hash(self.domain.as_bytes()).as_bytes(),
                100_000, // 100k computrons for sub-agent
            );
            sub_cell.verification_key = Some(VerificationKey {
                hash: *blake3::hash(&cap_issuer).as_bytes(),
                data: cap_issuer.to_vec(),
            });
            // Ignore error if cell already exists (idempotent).
            let _ = ledger.insert_cell(sub_cell);
        }

        Ok(SubAgent {
            cipherclerk: Arc::new(sub_cclerk),
            cell_id: sub_cell_id,
            token: delegated_token,
            cap_token,
            cap_issuer,
            cap_methods,
            parent: self
                .cipherclerk
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .public_key(),
            domain: self.domain.clone(),
            federation_id,
            ledger: self.ledger.clone(),
            nonce: Mutex::new(0),
            last_receipt_hash: Mutex::new(None),
            // Inherit producer mode from the parent runtime so worker turns route
            // through the SAME producer-selection seam a runtime turn does.
            lean_producer_enabled: self.lean_producer_enabled,
            // ROUTE (ii) — inherit the host executor signing seed, so the FRESH
            // executor this worker builds per `execute_method` signs the committed
            // grain-turn receipt (forge-admissible). `None` = unsigned worker turns.
            executor_signing_seed: self.executor_signing_seed,
            // WAVE A / WELD — a freshly spawned worker is NOT enveloped until the
            // gateway pins the owner key (`admit_enveloped_owned`); default `None`.
            owner_envelope_pubkey: None,
        })
    }
}

/// Run one fully-built turn against `ledger`, choosing the PRODUCER per `lean_producer_enabled`.
///
/// This is the single producer-selection seam shared by [`AgentRuntime::run_turn`] and every
/// worker turn ([`SubAgent::execute_method`]). When producer mode is on (and the crate was built
/// with `exec-lean`), on the COVERED set the VERIFIED Lean executor is AUTHORITATIVE via
/// `dregg_exec_lean::produce_via_lean` — its post-state AND commit verdict are committed
/// unconditionally, and the Rust `TurnExecutor` is demoted to a checked reference. A covered
/// Lean↔Rust disagreement is a surfaced RUST BUG (`error!`), NOT a fallback to Rust. Off the
/// covered set (or with producer mode off, or under the `no-lean-link` platform gate) this is the
/// legacy `executor.execute(turn, ledger)` path — byte-identical to the pre-weld behavior.
#[cfg_attr(not(feature = "exec-lean"), allow(unused_variables))]
fn produce(
    executor: &TurnExecutor,
    turn: &Turn,
    ledger: &mut Ledger,
    lean_producer_enabled: bool,
) -> TurnResult {
    #[cfg(feature = "exec-lean")]
    {
        if lean_producer_enabled {
            use dregg_exec_lean::{self as lean_apply, ProducerOutcome};
            let (result, outcome) = lean_apply::produce_via_lean(executor, turn, ledger);
            match &outcome {
                ProducerOutcome::LeanAuthoritative {
                    committed,
                    rust_agreed,
                    lean_root,
                    rust_root,
                    rust_committed,
                } => {
                    if *rust_agreed {
                        tracing::info!(
                            target: "dregg::sdk::lean_producer",
                            agent = ?turn.agent,
                            committed = *committed,
                            "THE SWAP producer mode (SDK): verified Lean executor is \
                             AUTHORITATIVE for this covered turn; Rust reference AGREES"
                        );
                    } else {
                        // THE AUTHORITY INVERSION's tooth: a covered Lean↔Rust disagreement is
                        // the Rust path being WRONG. The verified Lean verdict was committed;
                        // this surfaces the Rust bug — it is NOT a fallback to Rust.
                        tracing::error!(
                            target: "dregg::sdk::lean_producer",
                            agent = ?turn.agent,
                            lean_committed = *committed,
                            rust_committed = *rust_committed,
                            lean_root = ?lean_root,
                            rust_root = ?rust_root,
                            "THE SWAP authority inversion (SDK): verified Lean executor \
                             (AUTHORITATIVE) and the demoted Rust reference DISAGREE on a \
                             covered turn — the Rust path is BUGGY (REAL finding). The verified \
                             Lean verdict was committed; Rust was NOT allowed to override it"
                        );
                    }
                }
                ProducerOutcome::Fallback { reason } => {
                    tracing::warn!(
                        target: "dregg::sdk::lean_producer",
                        agent = ?turn.agent,
                        reason = %reason,
                        "THE SWAP producer mode (SDK): turn outside the swap-safe covered set \
                         — FENCED onto the legacy Rust path for this turn (explicit, surfaced; \
                         the named burning-down partition, not a silent Rust default)"
                    );
                }
            }
            return result;
        }
    }
    // Legacy Rust-producer path (also the only path under the `no-lean-link` platform gate).
    executor.execute(turn, ledger)
}

impl std::fmt::Debug for AgentRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentRuntime")
            .field("cell_id", &self.cell_id)
            .field("domain", &self.domain)
            .field("nonce", &self.nonce())
            .finish()
    }
}

/// A sub-agent spawned by a parent runtime with attenuated capabilities.
///
/// Sub-agents have their own identity and cipherclerk but operate on the same ledger
/// as their parent. Their token is strictly less powerful than the parent's.
///
/// Each sub-agent maintains its own receipt chain binding: every turn it executes
/// includes `previous_receipt_hash` linking to its last committed receipt. This
/// prevents reordering and replay of sub-agent turns.
// AUDIT[P2]: `SubAgent` exposes `pub cipherclerk: Arc<AgentCipherclerk>` and `pub token:
// HeldToken`. The `HeldToken` itself is now sealed-value (P0 fix), so its
// authority-affecting fields cannot be tampered with. But `pub federation_id:
// [u8; 32]` IS writable by an external caller holding a `&mut SubAgent`. This
// federation_id is used as the signing-message domain separator for turn
// signatures (see `SubAgent::execute`). An attacker who can mutate
// `federation_id` post-construct could cause the sub-agent to sign turns
// against the wrong federation, leading to cross-federation replay vectors.
// Severity P2: requires existing `&mut SubAgent` access, which is itself a
// privileged hold. Recommended fix: make all SubAgent fields private with
// read-only accessors (`pub fn federation_id(&self) -> [u8; 32]`).
#[derive(Debug)]
pub struct SubAgent {
    // P1-1, P1-2 (AUDIT-cipherclerk.md / AUDIT-sdk-rest.md): every field is now
    // `pub(crate)` so external callers can no longer rewrite `federation_id`
    // (the signing-message domain separator) or swap `cipherclerk` / `token`
    // post-construct. Access from outside the crate is via the read-only
    // accessor methods below.
    /// The sub-agent's cipherclerk.
    pub(crate) cipherclerk: Arc<AgentCipherclerk>,
    /// The sub-agent's cell ID.
    pub(crate) cell_id: CellId,
    /// The attenuated token this sub-agent holds.
    pub(crate) token: HeldToken,
    /// The ENFORCED capability credential: a public-key biscuit (encoded
    /// `eb2_…`) granting `service(sub_cell, method)` for exactly the method verbs
    /// the worker may invoke. Presented as [`Authorization::Token`] on every turn
    /// so the EXECUTOR's `verify_token_authorization` is the admission gate — an
    /// over-broad worker turn (a method outside `cap_methods`) is rejected by the
    /// executor itself, not by an out-of-band `cap.verify()`.
    pub(crate) cap_token: Vec<u8>,
    /// The biscuit issuer public key the worker's `cap_token` is signed under.
    /// Carried in the [`Authorization::Token`] as the
    /// [`TokenKeyRef::BiscuitIssuer`] anchor; the executor checks it against the
    /// sub-agent cell's `verification_key`.
    pub(crate) cap_issuer: [u8; 32],
    /// The method verbs the worker's `cap_token` grants (for diagnostics; the
    /// authoritative scope lives in the biscuit's `service(...)` grants).
    pub(crate) cap_methods: Vec<String>,
    /// The parent agent's public key.
    pub(crate) parent: PublicKey,
    /// The domain this sub-agent operates in.
    pub(crate) domain: String,
    /// The federation/group ID inherited from the parent runtime.
    ///
    /// In the unified lace model, this is equivalent to a `GroupId` (the
    /// reference group this agent belongs to). Used for signing messages
    /// with the correct group context. The field name is preserved for
    /// backward compatibility; semantically it is a group identifier.
    pub(crate) federation_id: [u8; 32],
    /// Shared ledger with the parent.
    ledger: Arc<Mutex<Ledger>>,
    /// Nonce counter for turn submission (incremented on each execute call).
    nonce: Mutex<u64>,
    /// The hash of the last committed receipt for this sub-agent.
    /// Used to bind each new turn to its predecessor, preventing reordering
    /// and replay of sub-agent turns.
    last_receipt_hash: Mutex<Option<[u8; 32]>>,
    /// Whether producer mode is active for this worker's turns — inherited from
    /// the parent runtime at spawn. When on (and built with `exec-lean`), a
    /// worker turn on the covered set is produced by the VERIFIED Lean executor
    /// via [`produce`], exactly like a runtime turn through
    /// [`AgentRuntime::run_turn`]. This is what routes served/minted grain
    /// turns through the same producer-selection seam instead of the legacy
    /// direct Rust producer.
    lean_producer_enabled: bool,
    /// ROUTE (ii) — the HOST executor signing seed inherited from the parent
    /// runtime at spawn. When `Some`, the FRESH executor this worker builds per
    /// [`Self::execute_method`] signs the committed grain-turn receipt's
    /// `executor_signature` (Ed25519 over `canonical_executor_signed_message`), so a
    /// served / minted grain turn is forge-admissible. `None` = today's UNSIGNED
    /// worker receipts.
    executor_signing_seed: Option<[u8; 32]>,
    /// WAVE A / WELD — OWNER LIVENESS. When this worker was admitted ENVELOPED
    /// (`ToolGateway::admit_enveloped_owned`), the renter/owner ed25519 public key
    /// (`agent_platform::RenterAnchor.pubkey`) whose signature gates the worker's
    /// authority-widening turns. The FRESH executor this worker builds per
    /// [`Self::execute_method`] registers an owner-envelope verifier for this key
    /// (`dregg_turn::TurnExecutor::register_owner_envelope`), so a VALID
    /// owner-signed `Authorization::Custom` on a `Delegate`/`SetPermissions` turn
    /// RESOLVES and is accepted (liveness) — while the host, lacking the owner
    /// key, still cannot forge it (safety). `None` for a non-enveloped worker
    /// (byte-unchanged).
    owner_envelope_pubkey: Option<[u8; 32]>,
}

impl SubAgent {
    /// Get the sub-agent's public key.
    pub fn public_key(&self) -> PublicKey {
        self.cipherclerk.public_key()
    }

    /// Read-only access to the sub-agent's cipherclerk.
    pub fn cipherclerk(&self) -> &Arc<AgentCipherclerk> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn cclerk(&self) -> &Arc<AgentCipherclerk> {
        self.cipherclerk()
    }

    /// Get the sub-agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get a reference to the sub-agent's held token.
    pub fn token(&self) -> &HeldToken {
        &self.token
    }

    /// Get the parent agent's public key.
    pub fn parent(&self) -> PublicKey {
        self.parent
    }

    /// Get the domain this sub-agent operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get the federation (group) id this sub-agent inherited.
    pub fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    /// Check whether the sub-agent's token authorizes a request.
    ///
    /// P1-4: previously delegated to [`AgentCipherclerk::verify_token`], which
    /// requires the token's `root_key` to be set (HMAC verification). Sub-agent
    /// tokens are delegated and carry a zeroed `root_key`, so `verify_token`
    /// always returned `false` — the method had no useful semantics.
    ///
    /// This implementation runs the Datalog evaluator on the structural
    /// caveat set (the same evaluator used by trusted-mode authorization),
    /// returning `true` if the request is `Allow`ed by the token's caveats and
    /// `false` for `Deny` / `Inconclusive` / parse failure. The durable
    /// binding is re-verified first so a post-receive tampering returns
    /// `false`.
    pub fn can_authorize(&self, request: &dregg_token::AuthRequest) -> bool {
        if self.token.reverify_delegation_binding().is_err() {
            return false;
        }
        match self
            .cipherclerk
            .authorize(&self.token, request, crate::VerificationMode::Trusted)
        {
            Ok(crate::AuthorizationPresentation::Trusted { trace, .. }) => {
                matches!(trace.conclusion, dregg_trace::Conclusion::Allow { .. })
            }
            // Any other presentation kind shouldn't occur from Trusted mode;
            // be conservative.
            Ok(_) => false,
            Err(_) => false,
        }
    }

    /// Read-only access to the worker's ENFORCED capability credential (the
    /// encoded biscuit presented as [`Authorization::Token`]).
    pub fn cap_token(&self) -> &[u8] {
        &self.cap_token
    }

    /// The biscuit issuer public key the worker's `cap_token` is signed under —
    /// the same key recorded (blake3-hashed) as the worker cell's
    /// `verification_key`, the executor's trust anchor for this credential.
    pub fn cap_issuer(&self) -> [u8; 32] {
        self.cap_issuer
    }

    /// The method verbs the worker's capability credential grants (diagnostic;
    /// the authoritative scope is the biscuit's `service(...)` grants, enforced
    /// by the executor).
    pub fn cap_methods(&self) -> &[String] {
        &self.cap_methods
    }

    /// Build the [`Authorization::Token`] the worker presents on its turns.
    ///
    /// The credential is the public-key biscuit minted at spawn; the executor
    /// verifies it against the issuer anchored in the sub-agent cell's
    /// `verification_key` via [`TokenKeyRef::BiscuitIssuer`] and runs the
    /// biscuit's `service(cell, action)` cover against THIS call. An over-scope
    /// call is rejected by the executor itself.
    fn cap_authorization(&self) -> Authorization {
        Authorization::Token {
            encoded: self.cap_token.clone(),
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: self.cap_issuer,
            },
            discharges: Vec::new(),
        }
    }

    /// Execute effects on the shared ledger using this sub-agent's cell, under
    /// the worker's default [`DEFAULT_SUBAGENT_METHOD`] scope.
    ///
    /// The worker presents its capability credential as [`Authorization::Token`],
    /// so the EXECUTOR's `verify_token_authorization` is the admission gate.
    /// Each turn is bound to this sub-agent's receipt chain via
    /// `previous_receipt_hash`, which prevents reordering and replay of
    /// sub-agent turns. The binding is updated after each successful commit.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        self.execute_method(DEFAULT_SUBAGENT_METHOD, effects)
    }

    /// WAVE A / WELD — pin the renter/owner ed25519 public key this worker's
    /// fresh executor registers as the owner-envelope verifier (see
    /// [`Self::owner_envelope_pubkey`]). Called by
    /// [`crate::ToolGateway::admit_enveloped_owned`] right after spawn, with the
    /// key that is ALSO stamped (hashed) into the worker cell's authority-widening
    /// permission slots — so the executor gate and the verifier answer for the
    /// SAME owner. Installs LIVENESS only; the fail-closed safety is unaffected.
    pub(crate) fn set_owner_envelope_pubkey(&mut self, owner_pubkey: [u8; 32]) {
        self.owner_envelope_pubkey = Some(owner_pubkey);
    }

    /// Execute effects under an explicit `method` verb.
    ///
    /// The worker presents its biscuit capability credential as
    /// [`Authorization::Token`]. If `method` is OUTSIDE the worker's granted
    /// scope (the biscuit's `service(cell, action)` grants fixed at spawn), the
    /// EXECUTOR rejects the turn with `TokenInsufficientCapability` — the
    /// credential is the boundary, not an out-of-band check.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_method(
        &self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, SdkError> {
        let executor = {
            // ROUTE (ii): the fresh executor carries the host signing seed inherited
            // at spawn, so the committed grain-turn receipt is signed (forge-admissible).
            let mut e = executor_with_real_verifiers(self.executor_signing_seed);
            // Run under the runtime's federation id so the token verifier's
            // AuthRequest (which binds `app_id = hex(federation_id)`) and the
            // receipt-chain domain separation match the parent runtime. The
            // biscuit cover is keyed on `service(cell, action)` and the issuer
            // anchored in the cell's verification_key, so it verifies regardless
            // of federation — but keeping the executor on the same federation
            // keeps signing/domain context consistent.
            e.set_local_federation_id(self.federation_id);
            // WAVE A / WELD — OWNER LIVENESS: an ENVELOPED worker's fresh executor
            // registers the owner-envelope verifier for the renter/owner key pinned
            // at rent, so a VALID owner-signed `Authorization::Custom` on a
            // `Delegate`/`SetPermissions` turn RESOLVES and is accepted (instead of
            // `AuthModeNotRegistered`). The host, lacking the owner key, still cannot
            // forge the signature (safety unchanged). `None` = non-enveloped worker.
            if let Some(owner_pubkey) = self.owner_envelope_pubkey {
                e.register_owner_envelope(owner_pubkey);
            }
            e
        };

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Read the current receipt chain head for binding.
        let previous_receipt_hash = *self.last_receipt_hash.lock().unwrap();

        // Seed the FRESH executor's per-agent receipt-chain head from this
        // worker's last committed receipt. The executor stores the chain head
        // in-instance (`TurnExecutor::check_previous_receipt_hash` validates the
        // turn's `previous_receipt_hash` against `self`'s stored head), but we
        // build a fresh `TurnExecutor` per call, so without seeding the stored
        // head is always `None` and a worker's SECOND chained turn (which
        // presents `Some(prev)`) is rejected with `ReceiptChainMismatch`. Seeding
        // makes the per-worker provenance chain actually hold across turns — a
        // worker can submit a sequence of chained, tamper-evident turns, which is
        // exactly what an audit of a sub-agent's work trail needs.
        if let Some(prev) = previous_receipt_hash {
            executor.set_last_receipt_hash(self.cell_id, prev);
        }

        // The worker authorizes by PRESENTING its capability credential. No
        // signature is needed: a verified `Authorization::Token` is the complete
        // authorization (the executor's token path returns on success).
        let action = Action {
            target: self.cell_id,
            method: symbol(method),
            args: Vec::new(),
            authorization: self.cap_authorization(),
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mut forest = CallForest::new();
        forest.add_root(action);

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee: 5_000,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let mut ledger = self.ledger.lock().unwrap();
        // Route the worker turn through the SAME producer-selection seam a runtime
        // turn owns (see [`produce`] / [`AgentRuntime::run_turn`]): under producer
        // mode, a covered worker turn (e.g. the served/minted grain turn) is
        // produced by the VERIFIED Lean executor, not the direct Rust producer.
        let result = produce(&executor, &turn, &mut ledger, self.lean_producer_enabled);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // SECURITY: Update the receipt chain binding so the next turn
                // is linked to this one, preventing reordering and replay.
                *self.last_receipt_hash.lock().unwrap() = Some(receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Get the sub-agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }
}

#[cfg(test)]
mod runtime_signer_hybrid_tests {
    //! The runtime signer (`sign_action_for_runtime`) is the ONLY way an action
    //! leaves an [`AgentRuntime`]. These tests pin that it now emits a HYBRID
    //! authorization (ed25519 + ML-DSA-65) — the same seed-derived key and
    //! canonical signing message the SDK cipherclerk uses — so an AgentRuntime
    //! turn carries the post-quantum half and is `require_pq`-acceptable. This
    //! closes the runtime's live CLASSICAL producer that blocked global
    //! `require_pq`.
    use super::*;
    use crate::cipherclerk::AgentCipherclerk;
    use dregg_turn::Effect;

    fn runtime(domain: &str) -> AgentRuntime {
        AgentRuntime::new_simple(AgentCipherclerk::new(), domain)
    }

    /// The runtime signer emits `Authorization::HybridSignature` with a NON-empty
    /// ML-DSA half, over the SAME canonical `compute_signing_message` (both halves
    /// verify), and the derived PQ pubkey is carried for a self-contained verifier.
    #[test]
    fn runtime_signer_emits_verifiable_hybrid_authorization() {
        let rt = runtime("runtime-hybrid-emit");
        let unsigned = raw::unsigned_action_named(
            rt.cell_id(),
            "execute",
            vec![Effect::IncrementNonce { cell: rt.cell_id() }],
        );
        let turn_nonce = rt.next_agent_turn_nonce();
        let signed = rt.sign_action_for_runtime(unsigned, turn_nonce);

        let (ed25519, ml_dsa, ml_dsa_pk) = match &signed.authorization {
            Authorization::HybridSignature {
                ed25519,
                ml_dsa,
                ml_dsa_pk,
            } => (*ed25519, ml_dsa.clone(), ml_dsa_pk.clone()),
            other => panic!("runtime signer must emit HybridSignature, got {other:?}"),
        };

        // Both halves cover the SAME canonical message the runtime signs over.
        let zeroed = Action {
            authorization: Authorization::Unchecked,
            ..signed.clone()
        };
        let msg = TurnExecutor::compute_signing_message(
            &zeroed,
            &rt.executor.local_federation_id,
            turn_nonce,
        );
        let pk = rt
            .cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key();
        assert!(
            pk.verify(&msg, &crate::Signature(ed25519)),
            "ed25519 half must verify against the runtime identity"
        );
        assert!(!ml_dsa.is_empty(), "the runtime always signs the PQ half");
        assert_eq!(ml_dsa_pk.len(), dregg_turn::pq::ML_DSA_PK_LEN);
        assert!(
            dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &ml_dsa),
            "ML-DSA half must verify against the carried pubkey"
        );
    }

    /// An AgentRuntime turn commits with `require_pq` OFF (the rollout default) —
    /// the hybrid change preserves existing runtime semantics.
    #[test]
    fn runtime_turn_commits_with_require_pq_off() {
        let rt = runtime("runtime-hybrid-off");
        assert!(!rt.executor.require_pq());
        let receipt = rt
            .execute(vec![Effect::IncrementNonce { cell: rt.cell_id() }])
            .expect("runtime turn must commit at require_pq=off");
        assert_eq!(receipt.action_count, 1);
    }

    /// KEY require_pq gate: with `require_pq` FORCED ON on the runtime's executor,
    /// an AgentRuntime turn is now ACCEPTED (it carries the ML-DSA half). Before
    /// the hybrid flip the runtime emitted a classical-only `Signature`, which the
    /// executor REJECTS under `require_pq=on` — so this is the blocker being lifted.
    #[test]
    fn runtime_turn_accepted_under_require_pq_on() {
        let rt = runtime("runtime-hybrid-on");
        rt.executor.set_require_pq(true);
        assert!(rt.executor.require_pq());
        let receipt = rt
            .execute(vec![Effect::IncrementNonce { cell: rt.cell_id() }])
            .expect("hybrid runtime turn MUST be accepted under require_pq=on");
        assert_eq!(receipt.action_count, 1);
    }
}
