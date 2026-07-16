//! Action types: the building blocks of a call forest.
//!
//! An Action is a single operation in the call forest, analogous to Mina's AccountUpdate.
//! Each action targets a cell, specifies a method, carries authorization, declares
//! preconditions, and produces effects.

use dregg_cell::lifecycle::{ArchivalAttestation, DeathCertificate};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::predicate::WitnessedPredicate;
use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CellId, NoteCommitment, Nullifier, Preconditions};
use dregg_cell_crypto::note_bridge::PortableNoteProof;
#[allow(unused_imports)]
use dregg_cell_crypto::{ValueCommitment, ValueCommitmentBytes};
use serde::{Deserialize, Serialize};

/// Serde helper for `[u8; 64]` (Ed25519 signatures — serde doesn't support arrays > 32).
/// Moved here verbatim from the dissolved `escrow` module (the wire encoding is unchanged).
pub mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CommitmentMode {
    /// Sign over the entire turn hash (current behavior — maximum binding).
    Full,
    /// Sign over only this action's hash + its position in the forest.
    /// Allows composability: signer doesn't need to see other actions.
    Partial,
}

impl Default for CommitmentMode {
    fn default() -> Self {
        CommitmentMode::Full
    }
}

/// A Symbol is a BLAKE3-hashed method or topic name, stored as a field element.
pub type Symbol = FieldElement;

/// Compute a symbol from a string name.
pub fn symbol(name: &str) -> Symbol {
    *blake3::hash(name.as_bytes()).as_bytes()
}

fn hash_auth_required(hasher: &mut blake3::Hasher, auth: &AuthRequired) {
    match auth {
        AuthRequired::None => hasher.update(&[0u8]),
        AuthRequired::Signature => hasher.update(&[1u8]),
        AuthRequired::Proof => hasher.update(&[2u8]),
        AuthRequired::Either => hasher.update(&[3u8]),
        AuthRequired::Impossible => hasher.update(&[4u8]),
        AuthRequired::Custom { vk_hash } => {
            hasher.update(&[5u8]);
            hasher.update(vk_hash)
        }
    };
}

/// A single operation in the call forest.
///
/// Analogous to Mina's AccountUpdate: targets a cell, performs a method,
/// requires authorization, checks preconditions, and produces effects.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Action {
    /// Which cell is being acted upon.
    pub target: CellId,
    /// What operation (method name hashed to symbol).
    pub method: Symbol,
    /// Arguments to the operation.
    pub args: Vec<FieldElement>,
    /// How this action is authorized.
    pub authorization: Authorization,
    /// What must be true before this action can execute.
    pub preconditions: Preconditions,
    /// What changes result from this action.
    pub effects: Vec<Effect>,
    /// Can children use parent's capabilities?
    pub may_delegate: DelegationMode,
    /// How much of the turn this action's signer commits to.
    /// Full = signs over entire turn hash (default, maximum binding).
    /// Partial = signs over only this action + position (enables multi-party composition).
    #[serde(default)]
    pub commitment_mode: CommitmentMode,
    /// Signed balance modification (Mina-style).
    ///
    /// When set, this applies a signed delta to the target cell's balance:
    /// - Negative values withdraw (produce excess available to other actions)
    /// - Positive values deposit (consume excess from other actions)
    ///
    /// At turn end, the sum of all balance_change deltas must be zero (conservation law).
    /// This enables composable patterns like DEX fills without explicit Transfer pairing.
    #[serde(default)]
    pub balance_change: Option<i64>,
    /// Canonical witness carrier for witness-attached predicates.
    ///
    /// Each blob is an opaque bytestring identified by its index in this vec.
    /// `WitnessedPredicate` clauses (in [`Preconditions::witnessed`] or in
    /// [`dregg_cell::StateConstraint::Witnessed`]) reference a blob by index
    /// via `WitnessedPredicate::proof_witness_index`. Variant-specific
    /// witnesses (Merkle paths for `SenderAuthorized`, preimage bytes for
    /// `PreimageGate`, per-(cell,sender) epoch counters for `RateLimit`,
    /// `Custom` predicate STARK proofs, etc.) are encoded as
    /// [`WitnessBlob`] entries here.
    ///
    /// Turn::hash v3 covers this field (see [`Action::hash`]). Signatures are
    /// computed over `Action::hash`, not over the postcard bytes, so always
    /// serializing this field does not change any signature. It MUST always be
    /// serialized: `Action` rides inside `Turn` over postcard (a positional
    /// format) — an omitted field desyncs the byte stream on deserialize
    /// ("Found an Option discriminant that wasn't 0 or 1" / "expected more
    /// data"). An empty `Vec` is one length byte; postcard does NOT skip it.
    #[serde(default)]
    pub witness_blobs: Vec<WitnessBlob>,
}

/// A single witness blob carried alongside an [`Action`].
///
/// Witness blobs are the canonical carrier for the inputs that
/// witness-attached predicates (`WitnessedPredicate`) and slot-caveat
/// enforcement need. The encoding is **typed-tag + bytes** so the
/// executor can dispatch without parsing the variant; the bytes are
/// then interpreted per-tag.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessBlob {
    /// What kind of witness this is. Determines how `bytes` is parsed.
    pub kind: WitnessKind,
    /// The opaque witness payload. Encoding is determined by `kind`.
    pub bytes: Vec<u8>,
}

impl WitnessBlob {
    /// Construct a `WitnessBlob` with the given kind and raw bytes.
    pub fn new(kind: WitnessKind, bytes: Vec<u8>) -> Self {
        Self { kind, bytes }
    }
    /// Convenience: a Merkle-membership-proof blob (for `SenderAuthorized`).
    pub fn merkle_path(path_bytes: Vec<u8>) -> Self {
        Self {
            kind: WitnessKind::MerklePath,
            bytes: path_bytes,
        }
    }
    /// Convenience: a 32-byte preimage blob (for `PreimageGate`).
    pub fn preimage(preimage: [u8; 32]) -> Self {
        Self {
            kind: WitnessKind::Preimage32,
            bytes: preimage.to_vec(),
        }
    }
    /// Convenience: a STARK / custom proof bytes blob.
    pub fn proof(proof_bytes: Vec<u8>) -> Self {
        Self {
            kind: WitnessKind::ProofBytes,
            bytes: proof_bytes,
        }
    }
    /// Convenience: a u32 rate-limit count blob (for `RateLimit`).
    pub fn rate_limit_count(count: u32) -> Self {
        Self {
            kind: WitnessKind::RateLimitCount,
            bytes: count.to_le_bytes().to_vec(),
        }
    }
    /// Decode `RateLimitCount` payload to its u32 value.
    pub fn as_rate_limit_count(&self) -> Option<u32> {
        if self.kind != WitnessKind::RateLimitCount || self.bytes.len() != 4 {
            return None;
        }
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&self.bytes);
        Some(u32::from_le_bytes(buf))
    }
    /// Decode `Preimage32` payload to its 32-byte value.
    pub fn as_preimage32(&self) -> Option<[u8; 32]> {
        if self.kind != WitnessKind::Preimage32 || self.bytes.len() != 32 {
            return None;
        }
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&self.bytes);
        Some(buf)
    }
}

/// Kinds of witness payloads carried in `Action::witness_blobs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessKind {
    /// 32-byte preimage payload (for `PreimageGate`).
    Preimage32,
    /// Merkle-membership-proof bytes (for `SenderAuthorized` /
    /// `MerkleMembership` witnessed predicates).
    MerklePath,
    /// u32 little-endian rate-limit counter snapshot (for `RateLimit`).
    RateLimitCount,
    /// STARK / Plonk / Bulletproof proof bytes (for `WitnessedPredicate`
    /// dispatch, custom-AIR proofs, etc.).
    ProofBytes,
    /// Cleartext bytes — interpreted by the receiving verifier.
    Cleartext,
}

/// How an action is authorized.
///
/// Maps to the authorization models in Mina: signature, proof, or none.
/// Adds `Breadstuff` for capability token authorization.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Authorization {
    /// Ed25519 signature over the action hash (stored as two 32-byte halves).
    Signature([u8; 32], [u8; 32]),
    /// Zero-knowledge proof bytes with the bound (action, resource) pair.
    ///
    /// The `bound_action` and `bound_resource` fields record what the prover
    /// committed to at proving time (from `AuthRequest.action` and
    /// `app_id.or(service)`). The verifier recomputes the binding from these
    /// strings and checks it against the proof's public inputs.
    Proof {
        proof_bytes: Vec<u8>,
        bound_action: String,
        bound_resource: String,
    },
    /// Capability token hash (breadstuff authorization).
    Breadstuff([u8; 32]),
    /// Bearer capability: proof-carrying authorization that exercises a capability
    /// WITHOUT requiring it to be in the actor's c-list. The proof demonstrates
    /// delegated authority from a root holder through a delegation chain.
    ///
    /// This enables E-language alignment: a capability can be exercised immediately
    /// in the same turn it is delegated, with no persistence in any cell's state.
    Bearer(BearerCapProof),
    /// No authorization provided (only valid if the cell's permissions allow it).
    ///
    /// Named `Unchecked` rather than `None` to make it grep-able and ensure
    /// code review flags its usage. Previously called `None`.
    #[serde(alias = "None")]
    Unchecked,
    /// Authorization derived from a verified CapTP delivery (Seam 3, Stage 7 / P1.B).
    ///
    /// When a CapTP wire message (EnlivenSturdyRef, DropRemoteRef, PresentHandoff,
    /// CapHello-driven export) is received, the wire layer constructs a Turn that
    /// mirrors the CapTP-side state mutation on-chain. The cryptographic legitimacy
    /// of that delivery is captured here:
    ///
    /// - `handoff_cert` is the introducer-signed certificate naming the recipient,
    ///   target cell, swiss number, permissions, allowed_effects, and nonce. Its
    ///   `introducer_signature` binds the certificate to the introducer's identity.
    /// - `sender_pk` is the recipient public key named in the certificate (the
    ///   entity that delivered the CapTP wire message).
    /// - `sender_signature` is a 64-byte ed25519 signature by `sender_pk` over
    ///   the canonical CapTP-delivery signing message (see
    ///   `Authorization::captp_delivered_signing_message`). This binds the
    ///   specific Turn (agent, target, effects, nonce) to this certificate's
    ///   nonce — defeating replay against unrelated turns.
    ///
    /// The executor verifies (a) the introducer signature on the cert against
    /// `introducer_pk`, (b) the sender signature over the canonical message
    /// against `sender_pk`, (c) that `sender_pk == handoff_cert.recipient_pk`,
    /// and (d) that the cert's `allowed_effects` (when present) covers every
    /// effect in the action.
    CapTpDelivered {
        /// The introducer-signed handoff certificate that authorized this delivery.
        handoff_cert: dregg_captp::HandoffCertificate,
        /// The introducer's public key (used to verify `handoff_cert.introducer_signature`).
        /// The certificate's `introducer` field is the federation identity; this is the
        /// concrete committee/signer key that issued the certificate.
        introducer_pk: [u8; 32],
        /// The recipient/sender public key. Must equal `handoff_cert.recipient_pk`.
        sender_pk: [u8; 32],
        /// Ed25519 signature by `sender_pk` over `captp_delivered_signing_message`.
        #[serde(with = "serde_sig64")]
        sender_signature: [u8; 64],
    },
    /// App-defined authorization: a [`WitnessedPredicate`] proves the
    /// authorization condition holds for THIS turn at THIS federation
    /// at THIS nonce position (per `AUTHORIZATION-CUSTOM-DESIGN.md`).
    ///
    /// The predicate's `input_ref` SHOULD be
    /// [`InputRef::SigningMessage`](dregg_cell::InputRef::SigningMessage),
    /// which the executor binds to the bytes
    /// `compute_partial_signing_message(action, position, federation_id,
    /// turn_nonce)` produces. The same federation/nonce binding the
    /// `Signature` path enjoys carries to `Custom`.
    ///
    /// `predicate.proof_witness_index` names the entry in
    /// [`Action::witness_blobs`] that carries the proof bytes; the
    /// verifier is resolved via the executor's
    /// `WitnessedPredicateRegistry` keyed on `predicate.kind`. Unknown
    /// kinds reject with [`TurnError::AuthModeNotRegistered`].
    ///
    /// When the target cell's [`AuthRequired::Custom { vk_hash }`] is
    /// set, the executor additionally requires that
    /// `predicate.kind == WitnessedPredicateKind::Custom { vk_hash }`
    /// — the cell declares which mode it accepts (design §10.4).
    Custom {
        /// The witnessed predicate that proves the authorization
        /// condition. Its commitment names the auth-mode-specific
        /// audience root (e.g., multisig signer set, time-lock DSL
        /// hash, credential ring root); its proof witnesses the
        /// authorization condition over the canonical signing message.
        predicate: WitnessedPredicate,
    },
    /// **Disjunctive multi-mode authorization: any one of `candidates`
    /// suffices.** Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3 / §9.2.3`,
    /// this is the categorical coproduct in the `Authorization`
    /// category — the missing "alternation" primitive.
    ///
    /// **App drivers.** *Multi-key cipherclerks* ("authorized by any of
    /// these 3 keys"); *recovery flows* ("primary OR backup OR
    /// social-recovery quorum"); *cross-mode bridge requests* ("signed
    /// by this federation OR proven by this STARK"); *hot/cold cap
    /// exercise* ("by the hot key OR by a Custom presentation of the
    /// cold-vault proof"). Each candidate may itself be any
    /// [`Authorization`] variant — `Signature`, `Proof`, `Custom`,
    /// `Bearer`, even a nested `OneOf` (combinatorial blow-up is the
    /// app's problem; nest sparingly).
    ///
    /// **Caveat: M-of-N is *not* `OneOf` of M-tuples** (combinatorial
    /// blow-up). For genuine M-of-N threshold authorization use
    /// [`Authorization::Custom`] with a threshold-sig
    /// `WitnessedPredicate`. `OneOf` is *purely* 1-of-N alternation;
    /// the executor verifies *exactly one* indexed candidate.
    ///
    /// **Soundness contract.** `proof_index` is the prover's
    /// declaration of *which* candidate they're satisfying. The
    /// executor recursively verifies only that one candidate. The
    /// signing-message / nonce / federation-id bindings of the
    /// **indexed candidate** are what guard against replay — the
    /// outer `OneOf` does not add its own binding.
    ///
    /// **Authorization::OneOf::Unchecked is rejected.** A candidate
    /// of `Authorization::Unchecked` reduces this primitive to
    /// "auth-bypass-by-naming-Unchecked" — the executor rejects
    /// any `OneOf` whose indexed candidate is `Unchecked`, mirroring
    /// the executor honesty audit's posture against `Unchecked`
    /// auth (`EXECUTOR-HONESTY-AUDIT.md`).
    ///
    /// **Nested `OneOf` is rejected.** A `OneOf` whose indexed
    /// candidate is itself a `OneOf` is rejected to bound the
    /// recursion depth and audit surface. Apps that want nested
    /// alternation should flatten the `candidates` list.
    OneOf {
        /// The disjunctive candidates. Any *one* satisfying the
        /// chosen `proof_index` authorizes the action.
        candidates: Vec<Authorization>,
        /// Which candidate (0-indexed into `candidates`) the prover
        /// is claiming satisfies the authorization.
        proof_index: u32,
    },
    /// **Stealth (one-time-key) invocation — anonymity of the *actor*.**
    ///
    /// The caller authorizes this action with a ONE-TIME Ed25519 key
    /// derived per-call from their persistent *spend* key `S` (the
    /// target cell's `public_key`, treated as a stealth spend pubkey)
    /// plus a fresh ephemeral secret `r`, using the
    /// [`dregg_cell_crypto::stealth`] machinery. The on-chain turn carries only
    /// the one-time public key `P`, the ephemeral public key `R = r·G`,
    /// the derived blinding scalar `c`, and a signature by the one-time
    /// private key `k = c + s` (`s` = spend scalar). The **persistent
    /// spend public key never appears in the turn**, and because `r` is
    /// fresh per call, `P`/`R`/`c` differ every call → two invocations
    /// are unlinkable to a turn-stream observer.
    ///
    /// ## Soundness relation
    /// The executor verifies the stealth-spend relation
    ///   `P == c·G + S`
    /// (point arithmetic, NO Diffie-Hellman / view key needed at verify
    /// time — see `derive_one_time_pubkey` in `cell::stealth`) and that
    /// `signature` verifies under `P` over
    /// [`Self::stealth_signing_message`]. Producing a valid signature
    /// under any `P = c·G + S` requires knowledge of the discrete log of
    /// `S` (the spend scalar), so only the legitimate spend-key holder
    /// can authorize — an attacker who only knows the public `S` cannot
    /// forge. `c` is bound into `P` and into the action hash, so a
    /// tampering relay cannot swap `c` (which would change `P`, breaking
    /// the signature).
    ///
    /// ## Replay
    /// The signing message binds `federation_id` + `turn_nonce` + the
    /// action body, exactly like the `Signature` path, so a stealth
    /// authorization for one (federation, nonce, action) does not
    /// re-verify against another turn. `(P, R)` MAY additionally be
    /// recorded by the federation as a one-time-key nullifier to make
    /// in-window replay of the *same* turn observable; that gate lives in
    /// the executor's nonce/receipt-chain machinery (the persistent
    /// per-agent `previous_receipt_hash` already rejects same-turn
    /// resubmission).
    Stealth {
        /// One-time public key `P = c·G + S` (compressed Ed25519). The
        /// signature verifies under this key.
        one_time_pubkey: [u8; 32],
        /// Ephemeral public key `R = r·G` (X25519/Ed25519 point bytes),
        /// published for the cell owner's own scanning/bookkeeping. Not
        /// load-bearing for verification, but bound into the action hash
        /// so a relay cannot strip or swap it.
        ephemeral_pubkey: [u8; 32],
        /// The blinding scalar `c = H(shared_secret)` reduced mod l,
        /// carried so the verifier can recompute `P = c·G + S` without
        /// any Diffie-Hellman (the view key stays private).
        blinding_scalar: [u8; 32],
        /// Ed25519 signature by the one-time key `k = c + s` over
        /// [`Self::stealth_signing_message`].
        #[serde(with = "serde_sig64")]
        signature: [u8; 64],
    },
    /// **First-class biscuit/macaroon credential authorization** per
    /// `docs/TOKEN-CAPABILITY-UNIFICATION.md` (goal 3). A peer of
    /// `Bearer`/`CapTpDelivered`: the caller authorizes by *presenting a
    /// token* whose caveats/Datalog are verified — deterministically and
    /// on-chain — against THIS call's `(action, resource, effects,
    /// nonce, federation, block_height)` via a turn-side
    /// `TokenAuthorityVerifier`.
    ///
    /// - **Biscuit** (prefix `eb2_`): decentralized public-key verify.
    ///   The root key is a granting authority the executor trusts; any
    ///   federation can verify offline.
    /// - **Macaroon** (prefix `em2_`): intra-authority fast path; only
    ///   sound where the verifier legitimately holds the root secret
    ///   (cell-scoped derived key).
    ///
    /// Replay against a different call fails because the bound
    /// `AuthRequest` facts differ. Expiry is block-height-bound (no
    /// wall-clock). Capability-cover is enforced (the token must grant
    /// ≥ what the cell requires). All checks fail closed.
    Token {
        /// Self-describing encoded credential (`eb2_…` biscuit /
        /// `em2_…` macaroon), as produced by `dregg_token`.
        encoded: Vec<u8>,
        /// How the verifier resolves the root key + trust anchor.
        key_ref: TokenKeyRef,
        /// Optional discharge tokens satisfying third-party caveats
        /// (each itself verifiable against a known gateway pubkey).
        // Always serialize (postcard positional wire format — see witness_blobs).
        #[serde(default)]
        discharges: Vec<Vec<u8>>,
    },
    /// **HYBRID (ed25519 + ML-DSA-65) signature — the quantum-safe turn
    /// perimeter.** Both halves cover the SAME canonical signing message
    /// ([`crate::executor::TurnExecutor::compute_signing_message`] /
    /// `compute_partial_signing_message`). A hybrid authorization verifies only
    /// when `classical ∧ pq`: the ed25519 half is checked against the target
    /// cell's identity, and the ML-DSA half (FIPS 204, ctx
    /// [`crate::pq::HYBRID_TURN_PQ_CTX`]) is checked against `ml_dsa_pk`.
    ///
    /// STAGED, fail-closed: a present-but-invalid `ml_dsa` half REJECTS the
    /// action regardless of `TurnExecutor::require_pq`; whether the PQ half is
    /// *required* (vs. the ed25519 half alone sufficing during rollout) is gated
    /// by that flag (default off). `ml_dsa` empty ⇒ the PQ half is absent (only
    /// valid when `require_pq` is off). The classical [`Authorization::Signature`]
    /// variant stays valid throughout the rollout.
    HybridSignature {
        /// The ed25519 signature over the canonical signing message (64 bytes).
        #[serde(with = "serde_sig64")]
        ed25519: [u8; 64],
        /// The ML-DSA-65 signature over the SAME message under
        /// [`crate::pq::HYBRID_TURN_PQ_CTX`]. Empty ⇒ PQ half absent.
        ml_dsa: Vec<u8>,
        /// The signer's serialized ML-DSA-65 public key (FIPS 204), carried so
        /// the verifier is self-contained during the staged rollout. Derived
        /// deterministically from the same seed as the ed25519 identity
        /// ([`crate::pq::MlDsaTurnKey::from_ed25519_seed`]).
        ml_dsa_pk: Vec<u8>,
    },
}

/// How a [`Authorization::Token`] verifier resolves the credential's
/// root key and trust anchor (per `TOKEN-CAPABILITY-UNIFICATION.md`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenKeyRef {
    /// Biscuit: verify offline against this granting-authority Ed25519
    /// public key. The key MUST be one the target cell's permissions /
    /// trusted-issuer set authorizes (the executor's
    /// `TokenAuthorityVerifier` holds that allowlist); an untrusted
    /// issuer is rejected even if the token verifies cryptographically.
    BiscuitIssuer { issuer_pubkey: [u8; 32] },
    /// Macaroon: verify against the target cell's deterministically
    /// derived root secret (cell-scoped). The verifier derives the
    /// secret from the cell id + a domain-separated KDF; cross-cell
    /// macaroons (whose secret the verifier does not hold) are rejected.
    CellScopedMacaroon { cell: CellId },
}

/// Derive the deterministic, cell-scoped macaroon root secret for a
/// [`TokenKeyRef::CellScopedMacaroon`] credential.
///
/// This is the SINGLE source of truth for the secret: the executor derives it
/// at verify time (see `TurnExecutor::verify_token_authorization`), and a
/// credential minter (e.g. the SDK's `AgentRuntime` spawning a sub-agent) must
/// mint the macaroon under the SAME secret so the executor's
/// `Authorization::Token` path is the real, in-runtime gate — not an out-of-band
/// `cap.verify()`.
///
/// HMAC macaroons require the verifier to hold the root secret, so this path is
/// only sound where the federation legitimately owns the cell's secret. The
/// secret is a domain-separated BLAKE3 KDF over the federation id + the cell id,
/// so it is deterministic (consensus-safe, no wall-clock), cell-scoped (a
/// different cell yields a different secret), and federation-scoped (a
/// cross-federation mint produces a different secret and will not verify).
pub fn derive_cell_macaroon_secret(federation_id: &[u8; 32], cell: &CellId) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-cell-macaroon-secret-v1");
    hasher.update(federation_id);
    hasher.update(cell.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Proof-carrying bearer capability: demonstrates delegated authority to exercise
/// a capability without holding it in a c-list.
///
/// Bearer caps are ephemeral -- they exist only for the duration of a single turn
/// and never persist in any cell's state. This makes them ideal for immediate
/// inline delegation where a one-turn delay is unacceptable.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BearerCapProof {
    /// The capability target being exercised.
    pub target: CellId,
    /// The permission level being exercised (must be subset of delegator's permissions).
    pub permissions: AuthRequired,
    /// The delegation chain proof (shows how authority flows from root to bearer).
    pub delegation_proof: DelegationProofData,
    /// Expiry height (mandatory for bearer caps -- limits the revocation window).
    pub expires_at: u64,
    /// Optional revocation channel binding. If set, the channel must be active
    /// for the bearer cap to be exercisable.
    pub revocation_channel: Option<[u8; 32]>,
    /// Optional facet restriction on this bearer capability.
    ///
    /// When set, the bearer can only exercise effects whose kind bits are within
    /// this mask. This must be a subset of the delegator's `allowed_effects` (if any).
    /// Enforces E-language facet attenuation: a delegated bearer can only restrict,
    /// never amplify, the delegator's facet.
    // Always serialize (postcard positional wire format — see witness_blobs).
    #[serde(default)]
    pub allowed_effects: Option<dregg_cell::EffectMask>,
}

/// How the delegation chain is proven for a bearer capability.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DelegationProofData {
    /// Signed attestation: delegator signs "I delegate {permissions} on {target}
    /// to {bearer_pk} until {expires_at}".
    SignedDelegation {
        /// Public key of the delegator (must hold the cap in their c-list).
        delegator_pk: [u8; 32],
        /// Ed25519 signature from delegator over the delegation message.
        #[serde(with = "serde_sig64")]
        signature: [u8; 64],
        /// Public key of the bearer (the entity exercising the cap).
        bearer_pk: [u8; 32],
    },
    /// STARK proof of derivation chain (verifiable without delegator online).
    StarkDelegation {
        /// Serialized STARK proof bytes.
        proof_bytes: Vec<u8>,
        /// Commitment to the root issuer of the capability.
        root_issuer_commitment: [u8; 32],
    },
}

/// Encode a 32-byte hash as 8 `BabyBear` field elements (4 bytes each, LE),
/// reduced mod the BabyBear prime.
///
/// Byte-for-byte identical to the executor's
/// `TurnExecutor::bytes32_to_babybear` (`executor/proof_verify.rs`). Kept here
/// so the bearer-cap STARK public-input layout has ONE definition that both the
/// in-ledger executor arm and the Ledger-free inspector/wasm verifier share.
fn stark_delegation_bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<dregg_circuit::field::BabyBear> {
    use dregg_circuit::field::{BABYBEAR_P, BabyBear};
    let mut result = Vec::with_capacity(8);
    for chunk in bytes.chunks(4) {
        let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        result.push(BabyBear(val % BABYBEAR_P));
    }
    result
}

/// Recompute the canonical public-input vector a [`DelegationProofData::StarkDelegation`]
/// bearer proof must commit to, given the `root_issuer_commitment` and the
/// (federation, target, permission-tier, expiry) scope it is being exercised under.
///
/// Layout (each 32-byte value → 8 `BabyBear` limbs, in order):
///   `root_issuer_commitment` ‖ `target` ‖ `scope_hash`
/// where `scope_hash = blake3("dregg-stark-delegation-scope-v1:" ‖ federation_id
/// ‖ perm_tag(LE u32) [‖ vk_hash if Custom] ‖ expires_at(LE u64))`.
///
/// This is the SAME vector the executor's [`crate::executor::TurnExecutor::verify_bearer_cap`]
/// `StarkDelegation` arm recomputes (`executor/authorize.rs`). The
/// delegator/bearer pubkeys are deliberately NOT bound — anonymity of the
/// delegation chain is the whole point of the STARK path; only the public
/// scope facts (which appear on the turn anyway) are bound, so a relay cannot
/// reuse a valid proof for a *wider* grant (different target, permission tier,
/// expiry, federation, or root issuer).
pub fn stark_delegation_expected_public_inputs(
    target: &CellId,
    permissions: &AuthRequired,
    expires_at: u64,
    federation_id: &[u8; 32],
    root_issuer_commitment: &[u8; 32],
) -> Vec<dregg_circuit::field::BabyBear> {
    let mut public_inputs = Vec::new();
    public_inputs.extend(stark_delegation_bytes32_to_babybear(root_issuer_commitment));
    public_inputs.extend(stark_delegation_bytes32_to_babybear(target.as_bytes()));
    let perm_tag: u32 = match permissions {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        AuthRequired::Custom { .. } => 5,
    };
    let scope_hash = {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-stark-delegation-scope-v1:");
        h.update(federation_id);
        h.update(&perm_tag.to_le_bytes());
        if let AuthRequired::Custom { vk_hash } = permissions {
            h.update(vk_hash);
        }
        h.update(&expires_at.to_le_bytes());
        *h.finalize().as_bytes()
    };
    public_inputs.extend(stark_delegation_bytes32_to_babybear(&scope_hash));
    public_inputs
}

/// Why a STARK-delegation bearer proof's scope binding was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StarkDelegationBindingError {
    /// The serialized STARK proof bytes did not parse.
    Deserialization(String),
    /// The proof carries fewer public inputs than the bound scope requires.
    TooFewPublicInputs { have: usize, expected: usize },
    /// A bound public input did not equal the recomputed scope value.
    PublicInputMismatch { index: usize },
}

impl core::fmt::Display for StarkDelegationBindingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            StarkDelegationBindingError::Deserialization(e) => {
                write!(f, "STARK proof deserialization failed: {e}")
            }
            StarkDelegationBindingError::TooFewPublicInputs { have, expected } => write!(
                f,
                "STARK proof has {have} public inputs, expected at least {expected}"
            ),
            StarkDelegationBindingError::PublicInputMismatch { index } => {
                write!(f, "STARK public input mismatch at index {index}")
            }
        }
    }
}

/// Verify the *scope binding* of a [`DelegationProofData::StarkDelegation`] bearer
/// proof: deserialize the STARK proof bytes and require that the public inputs it
/// commits to equal the canonical scope vector for `(target, permissions,
/// expires_at, federation_id, root_issuer_commitment)`.
///
/// This is the Ledger-free cryptographic core of the executor's `StarkDelegation`
/// authorization arm — the part that catches a forged or relayed proof whose
/// committed scope does not match the grant being exercised (wrong root issuer,
/// wider target/permission/expiry/federation). It is feature-uniform (no
/// recursion/prover dependency), so the inspector/wasm verifier runs the *same*
/// binding check the in-ledger executor runs.
///
/// The proof blob is the IR-v2 wire format (`postcard(Ir2BatchProof)`). This runs
/// the FULL [`verify_vm_descriptor2`](dregg_circuit::descriptor_ir2::verify_vm_descriptor2)
/// batch verification against the [`delegate_binding_descriptor`](dregg_circuit::delegate_descriptor::delegate_binding_descriptor):
/// its 24 row-0 `PiBinding`s pin every scope limb to the recomputed
/// `stark_delegation_expected_public_inputs`, so the proof verifies iff it was
/// minted for EXACTLY this scope. The scope-forge rejection that the old
/// executor-side field compare performed is now enforced in-circuit by the batch
/// STARK (a proof bound to scope `A` fails to verify against any forged wider
/// scope `B` — the boundary constraint is UNSAT).
pub fn verify_stark_delegation_binding(
    proof_bytes: &[u8],
    root_issuer_commitment: &[u8; 32],
    target: &CellId,
    permissions: &AuthRequired,
    expires_at: u64,
    federation_id: &[u8; 32],
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    StarkDelegationBindingError,
> {
    use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};

    // Decode the IR-v2 batch proof (the wire format `postcard(Ir2BatchProof)`).
    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| StarkDelegationBindingError::Deserialization(e.to_string()))?;

    // The canonical 24-limb scope vector for the grant being exercised.
    let expected = stark_delegation_expected_public_inputs(
        target,
        permissions,
        expires_at,
        federation_id,
        root_issuer_commitment,
    );

    // Full in-circuit binding verification against the delegation descriptor: its
    // 24 row-0 `PiBinding`s pin every scope limb to `expected[i]`, so the proof
    // verifies iff it was minted for EXACTLY this scope. A relayed proof bound to a
    // narrower grant commits to a different scope vector and the binding is UNSAT.
    let desc = dregg_circuit::delegate_descriptor::delegate_binding_descriptor();
    verify_vm_descriptor2(&desc, &proof, &expected)
        .map_err(|_| StarkDelegationBindingError::PublicInputMismatch { index: 0 })?;

    Ok(proof)
}

impl Authorization {
    /// Map this authorization to the corresponding AuthKind for permission checking.
    /// Returns None for Authorization::Unchecked, Breadstuff, and Bearer (handled separately).
    pub fn to_auth_kind(&self) -> Option<dregg_cell::AuthKind> {
        match self {
            Authorization::Signature(_, _) => Some(dregg_cell::AuthKind::Signature),
            // A hybrid (ed25519 + ML-DSA) signature satisfies a Signature
            // requirement; it IS a signature (with a post-quantum half).
            Authorization::HybridSignature { .. } => Some(dregg_cell::AuthKind::Signature),
            Authorization::Proof { .. } => Some(dregg_cell::AuthKind::Proof),
            Authorization::Breadstuff(_) => None,
            Authorization::Bearer(_) => None,
            Authorization::Unchecked => None,
            Authorization::CapTpDelivered { .. } => None,
            // Custom is not part of the Sig/Proof lattice; cells that
            // require Custom auth declare `AuthRequired::Custom { vk_hash }`
            // and the executor checks the predicate directly.
            Authorization::Custom { .. } => None,
            // OneOf is a disjunction — its discriminant depends on
            // which candidate the executor verifies, not on the
            // wrapper. Permission checks dispatch by inspecting the
            // chosen candidate at `verify_authorization` time.
            Authorization::OneOf { .. } => None,
            // Stealth authorizes by a one-time Ed25519 signature; it
            // satisfies the Signature requirement (the one-time key is
            // a derived signing key). Reported as Signature so cells
            // requiring `AuthRequired::Signature` accept it.
            Authorization::Stealth { .. } => Some(dregg_cell::AuthKind::Signature),
            // Token is verified holistically by the TokenAuthorityVerifier
            // (capability-cover decides whether it satisfies the cell's
            // requirement), so it is not part of the Sig/Proof lattice.
            Authorization::Token { .. } => None,
        }
    }

    /// Placeholder authorization for an [`Action`] that is ASSEMBLED unsigned by
    /// a higher-level routing/builder core and MUST be signed before submission
    /// (e.g. via `AppCipherclerk::sign_action`, which OVERWRITES this field).
    ///
    /// Semantically identical to [`Authorization::Unchecked`], but named so an
    /// unsigned-then-signed assembly does not have to write the review-fenced
    /// `Unchecked` literal in production framework source (see
    /// `app-framework/tests/no_unchecked.rs`): a reader sees a loud,
    /// to-be-signed placeholder, and the grep-guard stays the single source of
    /// truth for code that actually SHIPS unauthenticated.
    pub fn unsigned_placeholder() -> Self {
        Authorization::Unchecked
    }

    /// Create a Signature authorization from a 64-byte signature.
    pub fn from_sig_bytes(bytes: [u8; 64]) -> Self {
        let mut r = [0u8; 32];
        let mut s = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        s.copy_from_slice(&bytes[32..]);
        Authorization::Signature(r, s)
    }

    /// Canonical signing message for `Authorization::CapTpDelivered`.
    ///
    /// Legacy v1 wrapper for callers that did not yet pass an explicit
    /// federation id. New verification paths should use
    /// [`Self::captp_delivered_signing_message_for_federation`].
    pub fn captp_delivered_signing_message(
        cert_nonce: &[u8; 32],
        agent: &dregg_cell::CellId,
        target: &dregg_cell::CellId,
        turn_nonce: u64,
        effects: &[Effect],
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(128);
        msg.extend_from_slice(b"dregg-captp-delivered-v1");
        msg.extend_from_slice(cert_nonce);
        msg.extend_from_slice(&agent.0);
        msg.extend_from_slice(&target.0);
        msg.extend_from_slice(&turn_nonce.to_le_bytes());
        let effects_bytes = postcard::to_allocvec(effects).expect("effects serialization failed");
        msg.extend_from_slice(&(effects_bytes.len() as u32).to_le_bytes());
        msg.extend_from_slice(&effects_bytes);
        msg
    }

    /// Federation-bound signing message for `Authorization::CapTpDelivered`.
    ///
    /// Binds the sender's signature to:
    /// - domain separator (`b"dregg-captp-delivered-v2"`),
    /// - the local federation id (cross-federation replay protection),
    /// - the handoff certificate's nonce (cert-binding — same delegation),
    /// - the agent CellId (who runs the turn at the receiving federation),
    /// - the target CellId (which cell the action mutates),
    /// - the turn nonce (replay protection),
    /// - and the canonical postcard encoding of the action's effects.
    ///
    /// Verifiers MUST recompute this from the on-the-wire Turn fields and the
    /// cert nonce — the recipient cannot retroactively repoint their signed
    /// claim to a different turn.
    pub fn captp_delivered_signing_message_for_federation(
        federation_id: &[u8; 32],
        cert_nonce: &[u8; 32],
        agent: &dregg_cell::CellId,
        target: &dregg_cell::CellId,
        turn_nonce: u64,
        effects: &[Effect],
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(160);
        msg.extend_from_slice(b"dregg-captp-delivered-v2");
        msg.extend_from_slice(federation_id);
        msg.extend_from_slice(cert_nonce);
        msg.extend_from_slice(&agent.0);
        msg.extend_from_slice(&target.0);
        msg.extend_from_slice(&turn_nonce.to_le_bytes());
        // Effects are postcard-serialized for a canonical bytewise encoding.
        // The wire-layer builder uses the same encoding, so both sides agree.
        let effects_bytes = postcard::to_allocvec(effects).expect("effects serialization failed");
        msg.extend_from_slice(&(effects_bytes.len() as u32).to_le_bytes());
        msg.extend_from_slice(&effects_bytes);
        msg
    }

    /// Canonical signing message for [`Authorization::Stealth`].
    ///
    /// The one-time private key `k = c + s` signs this message. It binds
    /// the same fields the `Signature` path's preimage covers plus the
    /// blinding scalar `c` and the ephemeral pubkey `R`, so that:
    ///   * a tampering relay cannot retarget the signature to a
    ///     different action / federation / nonce (T2 + T6 + T11), and
    ///   * `c` and `R` are committed (a relay cannot swap them; `c` also
    ///     determines `P`, so swapping it breaks the signature anyway).
    ///
    /// `position` is the action's index in the forest root, mirroring
    /// the partial-commitment binding.
    pub fn stealth_signing_message(
        federation_id: &[u8; 32],
        action_hash: &[u8; 32],
        ephemeral_pubkey: &[u8; 32],
        blinding_scalar: &[u8; 32],
        position: usize,
        turn_nonce: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-stealth-sig-v1:");
        hasher.update(federation_id);
        hasher.update(action_hash);
        hasher.update(ephemeral_pubkey);
        hasher.update(blinding_scalar);
        hasher.update(&(position as u64).to_le_bytes());
        hasher.update(&turn_nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// Delegation mode for a child action that targets a cell *other* than its
/// parent's target.
///
/// Implemented modes: `None` (no cross-cell delegation) and `SnapshotRefresh`
/// (frozen point-in-time inheritance of an ancestor's capabilities, walked via
/// the `cell.delegate` chain). `ParentsOwn` and `Inherit` are TYPED but NOT
/// implemented: a child that targets a different cell under either mode is
/// rejected FAIL-CLOSED with [`crate::error::TurnError::DelegationModeUnimplemented`]
/// — a distinct error so callers never confuse "this mode is a no-op" with a
/// real authority denial. For explicit cross-cell capability transfer use
/// `Effect::Introduce` (three-party introduction), a bearer capability, or
/// `SnapshotRefresh`.
///
/// Note: a same-cell child needs no delegation at all and executes regardless
/// of this mode (the child acts under its own authority over the shared target).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DelegationMode {
    /// Children cannot use the parent's capabilities to reach a different cell.
    None,
    /// (Typed, NOT implemented.) Intent: children may use capabilities the
    /// parent owns. A cross-cell child under this mode is rejected fail-closed
    /// with `TurnError::DelegationModeUnimplemented`.
    ParentsOwn,
    /// (Typed, NOT implemented.) Intent: children inherit the parent's delegation
    /// mode transitively. A cross-cell child under this mode is rejected
    /// fail-closed with `TurnError::DelegationModeUnimplemented`.
    Inherit,
    /// Snapshot+refresh: child inherits parent's capabilities as a point-in-time
    /// snapshot. Child can act using the snapshot offline. Refresh to pick up new
    /// capabilities. Revocation is eventual (bounded by max_staleness).
    SnapshotRefresh,
}

/// Linearity discipline of an [`Effect`] family.
///
/// Per `HOUYHNHNM-COMPARISON.md` §4.3, §8.2: dregg already enforces
/// conservation per effect family — `Transfer` conserves balances,
/// `Mint`/`Burn` is the asymmetric pair, capability grant/revoke is the
/// cap pair, the bilateral schedule (γ.2) is almost a linear-logic
/// move. Houyhnhnm's framing makes the conservation discipline a *typed
/// answer*: each effect declares its `LinearityClass`, and any new
/// `Effect` variant added to the system MUST answer the conservation
/// question via the exhaustive `match` in [`Effect::linearity`].
///
/// The discriminants are deliberately *narrow* and *exhaustive at
/// compile time*: no `_ =>` default arm exists in [`Effect::linearity`],
/// so a contributor who adds a new effect cannot silently leave its
/// conservation status implicit.
///
/// # Variants
///
/// - [`LinearityClass::Conservative`] — paired effect; the sum of
///   resource deltas across the turn is zero (Transfer, the inner
///   balance moves of escrow create/release, the bilateral message
///   accumulator on γ.2).
/// - [`LinearityClass::Monotonic`] — strictly nondecreasing scalar
///   (nonces, height counters, attestation counters, refcount
///   *increments*).
/// - [`LinearityClass::Terminal`] — one-way, no inverse (revoke,
///   destroy, drop). These categorically cannot be "undone" by a
///   future effect; rollback requires a fresh creation.
/// - [`LinearityClass::Generative`] — creates a resource without a
///   paired consumer (Mint without Burn pair, CreateCell, CreateNote
///   without paired SpendNote). Must be operator-permissioned;
///   appears in receipts as a disclosed non-conservation.
/// - [`LinearityClass::Annihilative`] — destroys a resource without
///   a paired producer (Burn without Mint pair). Operator-disclosed
///   non-conservation; the receipt's `was_burn` flag is bound into
///   `receipt_hash` so the executor cannot strip the disclosure.
/// - [`LinearityClass::Neutral`] — no resource delta (state-field
///   mutations on cell-local accounting, event emission, refresh).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LinearityClass {
    /// Sum of resource deltas across the turn is zero. The
    /// conservation checker MAY require a paired sibling effect in the
    /// same turn (the dual of this effect's primary delta).
    Conservative,
    /// The effect monotonically grows a scalar (e.g. nonce, height,
    /// attestation counter, refcount-up). The executor's invariant
    /// checker rejects any operation that would decrement.
    Monotonic,
    /// One-way structural transition with no inverse (revoke, destroy,
    /// drop, archive). The cell-lifecycle state machine
    /// (`dregg_cell::lifecycle::CellLifecycle::is_terminal`) is the
    /// canonical example.
    Terminal,
    /// Creates a resource ex nihilo (Mint without a paired Burn,
    /// CreateCell, CreateNote without paired Spend). MUST be
    /// operator-permissioned; appears on-chain as a disclosed
    /// non-conservation.
    Generative,
    /// Destroys a resource without a paired creator (Burn,
    /// non-bridge-bound NoteCreate consumption paths). The disclosure
    /// is bound into the receipt; the executor cannot silently strip
    /// it.
    Annihilative,
    /// No resource delta — pure book-keeping (event emission, cell-
    /// local field mutations whose conservation lives elsewhere,
    /// refresh-from-parent).
    Neutral,
}

impl LinearityClass {
    /// Should the conservation checker require a paired sibling
    /// (the dual of this effect's delta in the same turn)?
    ///
    /// Returns `true` only for [`LinearityClass::Conservative`]; the
    /// other variants explicitly accept that no paired sibling is
    /// required (Mint/Burn ex nihilo, monotonic increments,
    /// one-way terminations, no-delta neutrals).
    pub fn requires_paired_sibling(self) -> bool {
        matches!(self, LinearityClass::Conservative)
    }

    /// Is this an *operator-disclosed non-conservation* — a deliberate
    /// break with the conservation invariant that the operator must
    /// disclose on-chain?
    ///
    /// This is the predicate the executor's adversarial path uses to
    /// decide whether to require a `was_burn`/`was_mint` disclosure
    /// flag in the receipt.
    pub fn is_disclosed_non_conservation(self) -> bool {
        matches!(
            self,
            LinearityClass::Generative | LinearityClass::Annihilative
        )
    }
}

/// One value-commitment leg of a shielded transfer on the wire: the (single-asset
/// M2-a) public asset type and the opaque compressed Pedersen value commitment
/// `commit(v, r)`. The amount `v` stays hidden behind the commitment; the
/// downstream conservation proof certifies `Σ in = Σ out` without revealing any
/// `v`. Mirrors `dregg_circuit_prove::shielded::ShieldedValueLeg` as plain,
/// always-serializable data so the `Effect` vocabulary needs no circuit type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShieldedLeg {
    /// Asset type (public in M2-a; the multi-asset pool hides it into a scalar).
    pub asset_type: u64,
    /// Compressed Ristretto encoding of the Pedersen value commitment.
    pub commitment_bytes: [u8; 32],
}

/// One spent input of a shielded transfer on the wire: the revealed nullifier and
/// value-binding (canonical `u32` field elements) plus the postcard-serialized
/// **hidden** note-spend proof (the hiding uni-STARK that proves membership +
/// nullifier derivation with owner/key/path blind). Reconstructed by the executor
/// via `dregg_circuit_prove::shielded::ShieldedTransfer::from_serialized_parts`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShieldedInputPayload {
    /// The revealed nullifier (the double-spend tag), as a canonical BabyBear u32.
    pub nullifier: u32,
    /// The published value-binding `hash_fact(value,[randomness,0,0])`, BabyBear u32.
    pub value_binding: u32,
    /// Canonical postcard bytes of the hiding note-spend proof (`DslZkProof`).
    pub proof: Vec<u8>,
}

/// The wire payload of a shielded transfer effect (privacy M2-a).
///
/// A **shielded transfer** spends hidden input notes and mints hidden output
/// notes with the **value** and the **owner** blind, leaving only: the nullifiers
/// (so the chain rejects double-spends), the output value commitments, and a
/// proof that the flow is genuine, conserved (`Σ in = Σ out`), and in-range. This
/// is the always-serializable, circuit-type-free mirror of
/// `dregg_circuit_prove::shielded::ShieldedTransfer` plus the Pedersen
/// conservation proof, so the `Effect` enum is wire-stable in every build (the
/// heavy STARK *verify* is reconstructed only in a `prover`-enabled executor).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShieldedTransferPayload {
    /// Commitment-tree root every input note is proven a member of (BabyBear u32).
    pub merkle_root: u32,
    /// One hidden note-spend proof per spent input.
    pub inputs: Vec<ShieldedInputPayload>,
    /// Input value-commitment legs (the spent notes' Pedersen commitments).
    pub input_legs: Vec<ShieldedLeg>,
    /// Output value-commitment legs (the minted notes' Pedersen commitments).
    pub output_legs: Vec<ShieldedLeg>,
    /// One serialized Bulletproof range proof per output leg (same order), each
    /// attesting the committed value is in `[0, 2^64)` — the inflation gate.
    pub output_range_proofs: Vec<Vec<u8>>,
    /// The Pedersen conservation (Schnorr-excess) proof over the legs, certifying
    /// `Σ C_in − Σ C_out = r_excess·R` (i.e. `Σ v_in = Σ v_out`) without revealing
    /// any amount. Bound — with the range proofs and STARK nullifiers/value-bindings
    /// — to the transfer's Fiat-Shamir transcript so the two halves cannot be spliced.
    pub conservation: dregg_cell_crypto::ConservationProof,
}

/// An effect produced by an action — what changes in the ledger.
///
/// Analogous to Mina's balance_change + state updates, but generalized for
/// the cell model.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Effect {
    /// Set a state field on a cell.
    SetField {
        cell: CellId,
        index: usize,
        value: FieldElement,
    },
    /// Transfer computrons between cells.
    Transfer {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    /// Grant a capability from one cell to another.
    GrantCapability {
        from: CellId,
        to: CellId,
        cap: CapabilityRef,
    },
    /// Revoke a capability from a cell.
    RevokeCapability { cell: CellId, slot: u32 },
    /// Emit an event from a cell (does not modify state, but is part of the receipt).
    EmitEvent { cell: CellId, event: Event },
    /// Increment a cell's nonce by 1.
    IncrementNonce { cell: CellId },
    /// Create a new cell in the ledger.
    CreateCell {
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: u64,
    },
    /// Update the permissions on a cell.
    ///
    /// SECURITY: This effect is always applied LAST within an action, after all
    /// other effects. Permission checks for all effects use the ORIGINAL permissions
    /// (snapshotted before any effects in this action run). This prevents an action
    /// from weakening permissions and then exploiting the weakened permissions in
    /// subsequent effects within the same action.
    SetPermissions {
        cell: CellId,
        new_permissions: dregg_cell::Permissions,
    },
    /// Update the verification key on a cell.
    ///
    /// SECURITY: Like SetPermissions, this is applied LAST within an action.
    SetVerificationKey {
        cell: CellId,
        new_vk: Option<dregg_cell::VerificationKey>,
    },
    /// Re-program a cell's [`CellProgram`] (its caveat table) as an ORDERED
    /// effect — the in-protocol home for the genuinely-dynamic reprogram case
    /// (the per-present compositor re-bake, a live trustline/flash-well program
    /// install). Replaces the timeless out-of-band genesis-path `set_cell_program`
    /// mutation: by riding a turn it lands a `CommitRecord`, so a durable image
    /// reproduces it on replay instead of mis-recording it as timeless genesis
    /// (the persist-durability category error — runtime customization is an
    /// ORDERED turn, not build-time genesis).
    ///
    /// Authority-gated by cell ownership: applied LAST within an action (like
    /// [`SetPermissions`]/[`SetVerificationKey`]), and a cross-cell program
    /// install requires the actor to hold `SetVerificationKey` permission on the
    /// target (the closest existing program-authority gate — a cell's program
    /// and VK are one authority surface).
    ///
    /// CIRCUIT WITNESS (FOLLOW-UP): this is a light-client-relevant ordered
    /// effect, but it has NO descriptor rung yet — binding the program write into
    /// the turn commitment is VK-affecting (ember-gated). The EXECUTOR path lands
    /// now so the redirect away from genesis works; the in-circuit witness is the
    /// owed follow-up (HORIZONLOG / circuit-soundness-apex).
    SetProgram {
        cell: CellId,
        program: dregg_cell::CellProgram,
    },
    /// Spend (consume) a note by revealing its nullifier.
    /// The proof must demonstrate: the nullifier corresponds to a valid note
    /// in the note tree, and the spender has authority.
    NoteSpend {
        nullifier: Nullifier,
        /// Root of the note tree at the time of proof generation.
        note_tree_root: [u8; 32],
        /// The value being released (for conservation tracking).
        value: u64,
        /// The asset type of the note being spent.
        asset_type: u64,
        /// The STARK spending proof (serialized). Proves:
        /// 1. The spender knows the note's opening (preimage of the commitment)
        /// 2. The nullifier is correctly derived from the note's secret data
        /// 3. The note commitment exists in the note tree (Merkle membership against the root)
        spending_proof: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path instead
        /// of cleartext value comparison. All notes in a turn must either all have
        /// commitments or all lack them (mixed is rejected).
        // Always serialize (postcard positional wire format — see witness_blobs).
        #[serde(default)]
        value_commitment: Option<[u8; 32]>,
    },
    /// Create a new note (add commitment to note tree).
    NoteCreate {
        commitment: NoteCommitment,
        /// The value being locked in this note (for conservation tracking).
        value: u64,
        /// The asset type of the note being created.
        asset_type: u64,
        /// Encrypted note content (only recipient can decrypt).
        encrypted_note: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path.
        // Always serialize (postcard positional wire format — see witness_blobs).
        #[serde(default)]
        value_commitment: Option<[u8; 32]>,
        /// Optional range proof attesting the committed value is in [0, 2^64).
        /// Required when value_commitment is present to prevent hidden inflation.
        // Always serialize (postcard positional wire format — see witness_blobs).
        #[serde(default)]
        range_proof: Option<Vec<u8>>,
    },
    /// Spawn a child cell with snapshot+refresh delegation.
    /// The child inherits the actor's current c-list as a snapshot.
    SpawnWithDelegation {
        /// Public key of the new child cell.
        child_public_key: [u8; 32],
        /// Token domain of the new child cell.
        child_token_id: [u8; 32],
        /// Maximum acceptable staleness (seconds) for the delegation snapshot.
        max_staleness: u64,
    },
    /// Child refreshes its delegation snapshot from its parent.
    /// The actor must be the child cell (self-refresh).
    RefreshDelegation {
        /// The child cell whose delegation snapshot is re-armed (self-refresh:
        /// `child == action target`).
        child: CellId,
        /// The refreshed delegation snapshot commitment (the c-list commitment
        /// re-armed from the parent). The executor DERIVES the genuine value at
        /// apply time and refuses a mismatching declaration (the forge antibody);
        /// both `child` and `snapshot` bind into `effects_hash` so a light client
        /// knows WHICH delegation was re-armed and to WHAT value.
        snapshot: [u8; 32],
    },
    /// Parent revokes delegation to a child by bumping its own epoch.
    /// The child's snapshot becomes stale relative to the new epoch.
    RevokeDelegation {
        /// The child cell whose delegation is being revoked.
        child: CellId,
    },
    /// Bridge a note from another federation by presenting a portable spending proof.
    ///
    /// When processed:
    /// 1. Verify the portable note proof against trusted federation roots.
    /// 2. Check the nullifier hasn't already been bridged (prevent double-bridge).
    /// 3. Create a new note commitment in the local note tree.
    /// 4. Credit the value to the receiving cell.
    BridgeMint {
        /// The portable proof carrying the STARK spending proof from the source federation.
        portable_proof: PortableNoteProof,
    },
    /// Pipelined send: dispatch an action to the result of a pending turn.
    /// Three-party introduction.
    Introduce {
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        permissions: dregg_cell::AuthRequired,
    },
    PipelinedSend {
        /// The eventual target — resolved during pipeline execution.
        target: crate::eventual::EventualRef,
        /// The action to send to the resolved target.
        action: Box<Action>,
    },
    /// Exercise a capability from the actor's c-list in one atomic step.
    ///
    /// This is the categorical "evaluation map" (eval: B^A x A -> B): look up a
    /// capability by slot, verify permissions, and execute inner effects against
    /// the capability's target cell. Combines c-list lookup + sub-action into a
    /// single effect, eliminating the two-step lookup-then-submit pattern.
    ExerciseViaCapability {
        /// Which slot in the actor's c-list to exercise.
        cap_slot: u32,
        /// The effects to perform on the target cell (resolved from the capability).
        inner_effects: Vec<Effect>,
    },
    /// Transition a hosted cell to sovereign mode.
    ///
    /// When executed: moves the cell from `cells` to `sovereign_commitments`
    /// (stores only the 32-byte state commitment, deletes the full state).
    /// The agent becomes responsible for maintaining and providing cell state.
    MakeSovereign {
        /// The cell to make sovereign.
        cell: CellId,
    },
    /// Create a new cell from a deployed factory.
    ///
    /// The factory's constraints are validated against the creation parameters.
    /// On success, the new cell is created with the specified program, capabilities,
    /// initial state, and provenance recording which factory created it.
    CreateCellFromFactory {
        /// The factory VK hash identifying which factory to use.
        factory_vk: [u8; 32],
        /// Owner public key for the new cell.
        owner_pubkey: [u8; 32],
        /// Token domain for the new cell.
        token_id: [u8; 32],
        /// Creation parameters (validated against factory descriptor).
        params: dregg_cell::factory::FactoryCreationParams,
    },

    /// **Categorical dual of acting-effects: proof of *non-action*.**
    ///
    /// A `Refusal` is a structural artifact that the prover did *not*
    /// take action `offered_action_commitment` within some window.
    /// This is NOT a cancellation (which would mutate the cancelled
    /// action) — it is *evidence of absence*, the categorical
    /// "initial object" in the Effect category that
    /// `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3 / §9.2.2` names.
    ///
    /// **App drivers:**
    /// - *Auditable rejection in HFT-style flows.* "I received an
    ///   order; I declined to fill; here is the proof I declined and
    ///   the reason." Silence is otherwise indistinguishable from
    ///   outage; a `Refusal` makes the rejection a first-class on-
    ///   chain artifact.
    /// - *Non-repudiation of timely response.* The receiver
    ///   committed, on-chain, to having considered (and declined) a
    ///   specific offer-commitment within a window.
    /// - *Compliance: "I did not bid above X within block-range
    ///   [a, b]."* The proof binds the *absence* of a matching
    ///   action under the prover's identity within the window.
    ///
    /// **How the proof works.** Proving a *negative* is hard; the
    /// proof references a `proof_witness_index` into the action's
    /// `witness_blobs`, and the carried bytes are one of:
    /// - A *receipt-chain scan witness* — postcard-encoded receipt
    ///   chain of every turn the prover authored within the window,
    ///   plus an inclusion-completeness proof that no other turn
    ///   exists. The verifier checks none match
    ///   `offered_action_commitment`.
    /// - A *bloom-filter non-membership proof* against an
    ///   offered-actions registry; the witnessed-predicate verifier
    ///   dispatches by `WitnessedPredicateKind::NonMembership` on
    ///   the registry's sorted-set root.
    /// - A *custom non-action AIR* the app registers via
    ///   `WitnessedPredicateKind::Custom`.
    ///
    /// The choice is left to the app — the executor only validates
    /// the carried witness through the
    /// `WitnessedPredicateRegistry`, treating the `Refusal` as a
    /// state-mutating effect that bumps the target cell's nonce and
    /// records the refusal commitment + reason for auditability.
    Refusal {
        /// The cell whose history attests to the non-action.
        ///
        /// The refusal is anchored to a specific cell — its nonce
        /// bumps, its refusal-log slot (cell-specific; typically the
        /// "audit" slot) records `(offered_action_commitment,
        /// refusal_reason)`. Cross-cell refusals chain through
        /// multiple `Refusal` effects.
        cell: CellId,
        /// 32-byte commitment to the (action, offerer, window) tuple
        /// the prover is refusing. Typically `blake3("dregg-offered-
        /// action-v1" || offerer || action_bytes || window_start ||
        /// window_end)`. The verifier of the carried non-action
        /// witness checks the witness binds to this commitment.
        offered_action_commitment: [u8; 32],
        /// Why the prover refused.
        refusal_reason: RefusalReason,
        /// Index into `Action::witness_blobs` carrying the non-action
        /// proof bytes. The witness is verified via the
        /// `WitnessedPredicateRegistry` keyed on a kind chosen by
        /// the app (typically `NonMembership` against an offered-
        /// actions registry root; or a `Custom` non-action AIR).
        ///
        /// The witness verifier's commitment is implicitly
        /// `offered_action_commitment` — i.e. the verifier checks
        /// that the carried proof binds the absence to *this*
        /// specific offered action.
        proof_witness_index: u32,
    },
    // ─── Cell lifecycle effects (Silver-Vision lifecycle subset) ─────────────
    //
    // Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4–§1.5` and the cell-side
    // primitives shipped with `CellLifecycle` (commit `9d819ea3`),
    // `Cell::seal`/`unseal`/`destroy`/`archive` (commit `c0496d79`), and
    // `CapabilitySet::attenuate_in_place` (commit `136ef24f`).
    //
    /// Seal a cell: transition its lifecycle to `CellLifecycle::Sealed`.
    /// The cell rejects new effects after sealing but state and history
    /// are preserved; reversible via [`Effect::CellUnseal`]. The reason
    /// is committed (cleartext lives off-chain).
    CellSeal {
        /// Which cell to seal (must match `action.target`).
        target: CellId,
        /// 32-byte commitment to the sealing reason (the cleartext lives
        /// off-chain).
        reason: [u8; 32],
    },
    /// Reverse a seal: transition the cell from `Sealed` back to `Live`.
    /// Rejected if the cell is not currently sealed.
    CellUnseal {
        /// Which cell to unseal (must match `action.target`).
        target: CellId,
    },
    /// Permanently retire a cell: transition lifecycle to `Destroyed`
    /// and bind the [`DeathCertificate`] hash into the final state.
    /// Once destroyed, the cell cannot transition to any other state
    /// (it is `is_terminal()`); subsequent effects targeting it are
    /// rejected.
    CellDestroy {
        /// Which cell to destroy (must match `action.target`).
        target: CellId,
        /// The death certificate. Its `cell_id` must match `target`;
        /// the executor binds `certificate.certificate_hash()` into
        /// the new `CellLifecycle::Destroyed`.
        certificate: DeathCertificate,
    },
    /// Burn an explicit, non-conservation amount from a cell's balance
    /// slot. Unlike `Transfer`, no destination credit happens — the
    /// supply is provably reduced. The receipt's `was_burn` flag is
    /// bound into `receipt_hash` so an executor cannot strip the
    /// disclosure (analogous to `was_encrypted`).
    Burn {
        /// The cell whose balance is reduced.
        target: CellId,
        /// Slot identifier. Sentinel `0` is the canonical cell-balance
        /// slot (per `state.balance()`). Any other value is rejected
        /// in Silver-Vision; a future expansion may use this to burn
        /// other ledgered quantities.
        slot: u32,
        /// Amount to burn (must not exceed the balance).
        amount: u64,
    },
    /// Monotonically narrow an existing capability in the actor's
    /// c-list via [`CapabilitySet::attenuate_in_place`]. Widening is
    /// rejected (the underlying primitive returns `None`).
    AttenuateCapability {
        /// The actor whose c-list holds the slot.
        cell: CellId,
        /// Slot index in the actor's c-list to narrow.
        slot: u32,
        /// New permissions — must be `is_narrower_or_equal` to the
        /// existing permissions.
        narrower_permissions: AuthRequired,
        /// New effect-mask facet (subset-only). `None` leaves it as-is.
        narrower_effects: Option<dregg_cell::EffectMask>,
        /// New expiry. Can only shrink relative to the existing expiry
        /// (or bind a finite expiry to a previously unbounded cap).
        narrower_expiry: Option<u64>,
    },
    /// Declare that the cell's receipt-chain prefix up to
    /// `prefix_end_height` is summarized by the carried
    /// [`ArchivalAttestation`]. Lifecycle transitions to `Archived`
    /// (the cell remains live); prior chain links may be pruned from
    /// the live tail (off-chain), with `checkpoint` as the standing
    /// witness.
    ReceiptArchive {
        /// Inclusive end-height of the archived prefix.
        prefix_end_height: u64,
        /// The archival attestation; its `cell_id` must match
        /// `action.target` and its `archive_end_height` must equal
        /// `prefix_end_height`.
        checkpoint: ArchivalAttestation,
    },

    // ─── Reactive effects (Track 2): the first-class async-coordination
    //     vocabulary — Promise / Notify / React. The kernel weld lives in
    //     [`crate::reactive`]; these are the turn-level Effect faces the
    //     executor dispatches. (`docs/deos/REACTIVE-EFFECTS.md`.)
    //
    // The keystone (the soundness gift): a promise-hole IS a nullifier. To
    // `React` is to SPEND the hole. One-shot linearity — react exactly once —
    // is the SAME double-spend non-membership the circuit already enforces on
    // `NoteSpend`. The executor spends `pending_id` into the very same
    // `note_nullifiers` set, so a second react (or a replayed `pending_id`) is
    // rejected by the identical nullifier gate.
    /// A STANDING COMMITMENT: `cell` commits to run a turn once
    /// `resolution_condition` holds — the promise-hole. The executor records
    /// the commitment in the cell's reactive registry; the hole is later
    /// discharged by a [`Effect::React`]. (Generative: it creates a hole.)
    Promise {
        /// The cell whose pending registry holds this commitment.
        cell: CellId,
        /// The condition under which the held turn fires.
        resolution_condition: crate::pending::ResolutionCondition,
        /// The turn the cell commits to run when it reacts.
        wake: Box<crate::turn::Turn>,
        /// Block height past which the hole expires (un-reactable).
        timeout_height: u64,
    },
    /// A WAKE from `from` to `to`: deposit a promise-hole (the kernel-backed
    /// `NotifyEdge`) in `to`'s registry that `to` may later react to. The
    /// recipient commits to run `wake` when it discharges `resolution_condition`.
    /// (Generative: it creates a hole in the recipient.)
    Notify {
        /// The waking cell (the sender / provenance).
        from: CellId,
        /// The woken cell (the recipient; holds the hole in its registry).
        to: CellId,
        /// The turn the recipient commits to run when it reacts.
        wake: Box<crate::turn::Turn>,
        /// The condition the recipient must discharge to react.
        resolution_condition: crate::pending::ResolutionCondition,
        /// Block height past which the hole expires (un-reactable).
        timeout_height: u64,
    },
    /// REACT to a deposited hole: discharge `pending_id` by presenting a proof
    /// of `condition`. THE ONE-SHOT SPEND — `pending_id` is consumed into the
    /// production nullifier set exactly as a [`Effect::NoteSpend`] nullifier is,
    /// so a second react (or a replay of the same `pending_id`) is rejected by
    /// the double-spend gate. (Terminal: one-way consume of the hole, no inverse.)
    React {
        /// The hole being discharged, AS A NULLIFIER. The 32-byte hole id
        /// (the deposited `wake` turn hash) IS the nullifier spent into the
        /// production `note_nullifiers` set — the promise-hole-as-nullifier.
        pending_id: Nullifier,
        /// The condition the proof must satisfy (the spend is gated on it).
        condition: crate::conditional::ProofCondition,
        /// The proof discharging the condition (the witness for the spend).
        resolution_proof: crate::conditional::ConditionProof,
        /// The turn whose genuine receipt the resolution produces (the `wake`
        /// the matching `Notify`/`Promise` committed to). Its hash MUST equal
        /// `pending_id` — the executor binds the spent nullifier to the resolved
        /// turn so a react cannot spend one hole while resolving another.
        wake: Box<crate::turn::Turn>,
    },
    /// Mint new supply of an asset into a holder's balance slot — the
    /// cap-gated SUPPLY ENTRY (`docs/SUPPLY-MODEL.md` Stage 2, the dual
    /// of `Burn`). The issuer WELL of `target`'s asset is DEBITED (going
    /// more negative — the `−supply` account grows) and `target` is
    /// CREDITED, so a mint CONSERVES exactly (`Σδ=0`, per-asset): supply
    /// enters only through this authored verb. Unlike `Transfer`, the
    /// source is the asset's well (resolved from `target`'s `token_id`,
    /// never a field) rather than another holder.
    ///
    /// AUTHORITY (the one place mint ≠ burn): the actor must hold a
    /// control-grade capability over the issuer WELL carrying the
    /// `EFFECT_MINT` facet — the Rust image of Lean `mintAuthorizedB`
    /// (issuer/node authority, NOT bare ownership: "a cell cannot coin
    /// its own supply"). Burning your own value is permissionless;
    /// minting is privileged.
    ///
    /// PLACED LAST in the enum so its serde discriminant does NOT shift
    /// any existing variant's index — the durable `postcard` codec
    /// (commit log / checkpoint) is index-sensitive, so a new variant
    /// MUST append, never insert.
    Mint {
        /// The recipient cell whose balance is increased.
        target: CellId,
        /// Slot identifier. Sentinel `0` is the canonical cell-balance
        /// slot (per `state.balance()`). Any other value is rejected,
        /// exactly as `Burn`.
        slot: u32,
        /// Amount to mint (credited to `target`, debited from the well).
        amount: u64,
    },
    /// Shielded transfer (privacy M2-a): spend hidden input notes and mint hidden
    /// output notes with **value and owner blind**. The opt-in privacy upgrade of
    /// the cleartext note path — the cleartext `NoteSpend`/`NoteCreate` stay the
    /// default; this hides amounts and owners entirely.
    ///
    /// What the executor admits it on: (1) the **hidden STARK side** — every
    /// input's membership in the commitment tree + correct nullifier derivation,
    /// proved through `HidingFriPcs` so owner/key/path are blind; (2) the **hidden
    /// Pedersen side** — homomorphic value-commitment conservation (`Σ in = Σ out`)
    /// plus a per-output range proof closing the negative-value inflation hole;
    /// (3) the **nullifier gate** — each revealed nullifier is consumed once in the
    /// production `note_nullifiers` set (double-spend rejected, journaled for
    /// rollback). The two halves are Fiat-Shamir-bound to one transcript so they
    /// cannot be spliced across transfers.
    ///
    /// Self-authorizing: the ZK proof of note ownership IS the authority (like
    /// `NoteSpend` / `BridgeMint`), so it carries no cross-cell capability gate.
    ///
    /// APPENDED LAST (after `Mint`) so its serde discriminant shifts no existing
    /// variant — the durable postcard codec is index-sensitive.
    ///
    /// CIRCUIT WITNESS (named residual): the executor VERIFIES the shielded proof
    /// and conserves live, but binding the shielded-proof verification into the
    /// `effect_vm` descriptor (so a pure LIGHT CLIENT — not just a re-executing
    /// validator — witnesses it) is the VK-affecting follow-up. See
    /// `docs/posters/privacy.txt` and the M2 weld plan.
    ShieldedTransfer {
        /// The shielded transfer's wire payload (hidden STARK proofs + Pedersen
        /// value-commitment legs + range proofs + the conservation proof).
        payload: ShieldedTransferPayload,
    },
    /// **THE CUSTOM-VK DOOR** — apply a custom-program transition to a sovereign
    /// cell, adjudicated by an external STARK sub-proof. This is the turn-level
    /// leg of the Custom-VK extension point (`circuit::effect_vm::Effect::Custom` /
    /// `customVmDescriptor2R24`): the marker that makes a proof-carrying turn
    /// carrying `Turn::custom_program_proofs` REACHABLE — without it
    /// `convert_turn_effects_to_vm` never emits `VmEffect::Custom`, the in-circuit
    /// committed Custom-effect count is 0, and the turn is rejected
    /// (`CustomProofCountMismatch`). It is the substrate leg a Custom-VK game (the
    /// Braid resolver) rides.
    ///
    /// ## Where its authority lives, and where it is REFUSED
    ///
    /// A custom transition carries authority ONLY through its paired
    /// [`CustomProgramProof`](crate::turn::CustomProgramProof) (same index in
    /// `Turn::custom_program_proofs`), verified on the proof-carrying sovereign
    /// path ([`crate::executor::TurnExecutor::verify_and_commit_proof`]). There the
    /// executor (a) dispatches the sub-proof to its REGISTERED verifier
    /// (fail-closed on an unregistered `program_vk_hash`); (b) WELDS the sub-proof's
    /// `[old_commit8, new_commit8]` public-input prefix to the cell's committed
    /// pre-state root and this turn's claimed post-state root
    /// (`dregg_circuit::effect_vm::custom_state_binding` ABI); (c) STORES the
    /// attested post-state as the cell's new sovereign commitment (provably equal
    /// to the sub-proof's `new_commit8` by the weld). On ANY other path there is no
    /// proof, no weld, and no sovereign commitment to store, so the classical
    /// apply path REFUSES this effect fail-closed
    /// ([`crate::error::TurnError::CustomEffectRequiresProofCarryingTurn`]).
    ///
    /// ## The carried fields (the bridge preimage)
    ///
    /// * `cell` — the sovereign cell whose committed root this transition advances
    ///   (must equal the proof-carrying turn's `execution_proof_cell`).
    /// * `program_vk_hash` — the 32-byte custom-program identity (the registry
    ///   dispatch key). Projected to the `VmEffect::Custom.program_vk_hash` 8-felt
    ///   PI via `dregg_circuit::effect_vm::bytes32_to_8_limbs` — the SAME encoding
    ///   `enforce_custom_proof_entry_binding` uses, so the wire sub-proof's
    ///   `vk_hash` and the in-circuit committed VK agree.
    /// * `proof_commitment` — the 32-byte carrier
    ///   (`dregg_cell::commitment::felt8_to_bytes32`) of the 8-felt
    ///   `custom_proof_pi_commitment(public_inputs)` the Custom row PUBLISHES and
    ///   the per-turn fold binds to the sub-proof leaf. Set independently of the
    ///   wire proof so the STARK binds it and the executor cross-checks the wire
    ///   proof backs it — a lie here is caught by the fold (no backing sub-proof ⇒
    ///   no aggregate root) or by the sub-proof's own registry verify.
    Custom {
        cell: CellId,
        program_vk_hash: [u8; 32],
        proof_commitment: [u8; 32],
    },
}

/// Why a [`Effect::Refusal`] was issued. Refusals are *evidence of
/// absence*, but the reason field gives downstream auditors a
/// structured signal beyond raw non-action.
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RefusalReason {
    /// The prover deliberately declined the offered action — explicit
    /// rejection (e.g. "the price was wrong").
    Declined,
    /// The prover lacked authority to take the action (e.g. cap
    /// revoked, facet disallows). Distinct from `Declined` because
    /// the failure is structural rather than discretionary.
    NoAuthority,
    /// The window during which the offered action was valid has
    /// expired before the prover could (or would) act.
    WindowExpired,
    /// App-specific reason — the 32-byte commitment is opaque to the
    /// substrate; apps decode via their `CustomEffectVerifier` or by
    /// pairing this with an `EmitEvent` carrying the decoded reason.
    Custom { reason_hash: [u8; 32] },
}

/// An event emitted by an action.
///
/// Events are logged in the receipt but do not modify ledger state.
/// They are indexed by topic for off-chain consumption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Event {
    /// The topic of this event (hashed method/event name).
    pub topic: Symbol,
    /// Arbitrary data fields.
    pub data: Vec<FieldElement>,
}

impl Action {
    /// Compute the BLAKE3 hash of this action (for Merkle tree inclusion).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"dregg-action-v2:");
        hasher.update(self.target.as_bytes());
        hasher.update(&self.method);
        for arg in &self.args {
            hasher.update(arg);
        }
        // Hash authorization discriminant + data.
        match &self.authorization {
            Authorization::Signature(r, s) => {
                hasher.update(&[0u8]);
                hasher.update(r);
                hasher.update(s);
            }
            Authorization::HybridSignature {
                ed25519,
                ml_dsa,
                ml_dsa_pk,
            } => {
                // New discriminant (10) — distinct from `Signature` (0) so a
                // classical and a hybrid authorization over the same action
                // never collide in the action hash. Binding the PQ material
                // (signature + public key) here means the OUTER turn envelope's
                // signatures cover it: a tampering executor cannot swap or strip
                // the PQ half under a signed-turn envelope.
                hasher.update(&[10u8]);
                hasher.update(ed25519);
                hasher.update(&(ml_dsa.len() as u64).to_le_bytes());
                hasher.update(ml_dsa);
                hasher.update(&(ml_dsa_pk.len() as u64).to_le_bytes());
                hasher.update(ml_dsa_pk);
            }
            Authorization::Proof {
                proof_bytes,
                bound_action,
                bound_resource,
            } => {
                hasher.update(&[1u8]);
                hasher.update(proof_bytes);
                hasher.update(bound_action.as_bytes());
                hasher.update(bound_resource.as_bytes());
            }
            Authorization::Breadstuff(token) => {
                hasher.update(&[2u8]);
                hasher.update(token);
            }
            Authorization::Bearer(proof) => {
                hasher.update(&[4u8]);
                hasher.update(proof.target.as_bytes());
                hasher.update(&proof.expires_at.to_le_bytes());
                match &proof.delegation_proof {
                    DelegationProofData::SignedDelegation {
                        delegator_pk,
                        signature,
                        bearer_pk,
                    } => {
                        hasher.update(&[0u8]);
                        hasher.update(delegator_pk);
                        hasher.update(signature);
                        hasher.update(bearer_pk);
                    }
                    DelegationProofData::StarkDelegation {
                        proof_bytes,
                        root_issuer_commitment,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
                        hasher.update(proof_bytes);
                        hasher.update(root_issuer_commitment);
                    }
                }
                if let Some(rc) = &proof.revocation_channel {
                    hasher.update(&[1u8]);
                    hasher.update(rc);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Authorization::Unchecked => {
                hasher.update(&[3u8]);
            }
            Authorization::CapTpDelivered {
                handoff_cert,
                introducer_pk,
                sender_pk,
                sender_signature,
            } => {
                hasher.update(&[5u8]);
                // Hash the cert's signing message (covers all cert fields) + its
                // signature, plus the sender pk and signature.
                let cert_msg = handoff_cert.signing_message();
                hasher.update(&(cert_msg.len() as u64).to_le_bytes());
                hasher.update(&cert_msg);
                hasher.update(&handoff_cert.introducer_signature.0);
                hasher.update(introducer_pk);
                hasher.update(sender_pk);
                hasher.update(sender_signature);
            }
            Authorization::Custom { predicate } => {
                hasher.update(&[6u8]);
                // Hash the predicate's structural shape so a tampering
                // executor can't substitute a different predicate
                // (different kind, commitment, input_ref, or proof
                // index) under the same signed-turn envelope. Use
                // postcard for a canonical byte encoding that's
                // forward-compatible with the kind enum.
                let pred_bytes = postcard::to_allocvec(predicate).unwrap_or_default();
                hasher.update(&(pred_bytes.len() as u64).to_le_bytes());
                hasher.update(&pred_bytes);
            }
            Authorization::OneOf {
                candidates,
                proof_index,
            } => {
                hasher.update(&[7u8]);
                hasher.update(&proof_index.to_le_bytes());
                hasher.update(&(candidates.len() as u64).to_le_bytes());
                // Bind the entire candidate list into the hash so a
                // tampering executor can't shuffle / add / remove
                // candidates after signing. We use postcard for a
                // canonical byte encoding — `Authorization` already
                // derives Serialize.
                let cand_bytes = postcard::to_allocvec(candidates).unwrap_or_default();
                hasher.update(&(cand_bytes.len() as u64).to_le_bytes());
                hasher.update(&cand_bytes);
            }
            Authorization::Stealth {
                one_time_pubkey,
                ephemeral_pubkey,
                blinding_scalar,
                signature,
            } => {
                hasher.update(&[8u8]);
                hasher.update(one_time_pubkey);
                hasher.update(ephemeral_pubkey);
                hasher.update(blinding_scalar);
                // IMPORTANT: the signature is NOT hashed here. The
                // stealth signing message (`stealth_signing_message`)
                // consumes `action.hash()`, so including the signature
                // would be circular at signing time. Excluding it
                // mirrors how the `Signature` path's
                // `compute_signing_message` does not hash its own
                // signature. The keys + blinding scalar above fully
                // determine `P`, and `P` is what the signature binds.
                let _ = signature;
            }
            Authorization::Token {
                encoded,
                key_ref,
                discharges,
            } => {
                hasher.update(&[9u8]);
                hasher.update(&(encoded.len() as u64).to_le_bytes());
                hasher.update(encoded);
                let kr_bytes = postcard::to_allocvec(key_ref).unwrap_or_default();
                hasher.update(&(kr_bytes.len() as u64).to_le_bytes());
                hasher.update(&kr_bytes);
                hasher.update(&(discharges.len() as u64).to_le_bytes());
                for d in discharges {
                    hasher.update(&(d.len() as u64).to_le_bytes());
                    hasher.update(d);
                }
            }
        }
        // Hash delegation mode.
        hasher.update(&[self.may_delegate as u8]);
        // Hash commitment mode.
        hasher.update(&[self.commitment_mode as u8]);
        // Hash balance_change.
        if let Some(delta) = self.balance_change {
            hasher.update(&[1u8]); // discriminant: Some
            hasher.update(&delta.to_le_bytes());
        } else {
            hasher.update(&[0u8]); // discriminant: None
        }
        // Hash effects.
        for effect in &self.effects {
            hasher.update(&effect.hash());
        }
        // Hash preconditions to prevent downgrade attacks where an attacker removes
        // preconditions (e.g., minimum balance guards) from a signed action.
        let preconds_bytes = postcard::to_allocvec(&self.preconditions).unwrap_or_default();
        hasher.update(&preconds_bytes);
        // Hash witness_blobs (Cav-Codex Block 3) so a tampering verifier
        // can't strip or substitute the witness payloads a signed action
        // committed to. Empty vec hashes to the length prefix only; this
        // is byte-equivalent to actions that were signed before this
        // field was added (Turn v3 preimage extension).
        hasher.update(&(self.witness_blobs.len() as u64).to_le_bytes());
        for wb in &self.witness_blobs {
            let kind_disc: u8 = match wb.kind {
                WitnessKind::Preimage32 => 0,
                WitnessKind::MerklePath => 1,
                WitnessKind::RateLimitCount => 2,
                WitnessKind::ProofBytes => 3,
                WitnessKind::Cleartext => 4,
            };
            hasher.update(&[kind_disc]);
            hasher.update(&(wb.bytes.len() as u64).to_le_bytes());
            hasher.update(&wb.bytes);
        }
        *hasher.finalize().as_bytes()
    }
}

impl Effect {
    /// Declare this effect's [`LinearityClass`].
    ///
    /// **This match is exhaustive on purpose.** No `_ =>` default arm
    /// exists; every new [`Effect`] variant added in the future is
    /// forced — by `rustc` — to *answer the conservation question* per
    /// `HOUYHNHNM-COMPARISON.md` §4.3, §8.2. The compiler is the
    /// enforcer of "the designer had to think about this."
    ///
    /// The conservation checker in the executor uses this to know
    /// whether to require a paired sibling effect
    /// ([`LinearityClass::Conservative`]) or to accept a disclosed
    /// non-conservation ([`LinearityClass::Generative`] /
    /// [`LinearityClass::Annihilative`]).
    pub fn linearity(&self) -> LinearityClass {
        match self {
            // -- Conservative: paired-delta resource moves. --
            Effect::Transfer { .. } => LinearityClass::Conservative,

            // Notes spent-and-created together must conserve value; the
            // executor's conservation checker enforces this across
            // sibling spend/create pairs in the same turn.
            Effect::NoteSpend { .. } => LinearityClass::Conservative,
            Effect::NoteCreate { .. } => LinearityClass::Conservative,

            // A shielded transfer is value-conserving by construction: the
            // Pedersen conservation proof certifies `Σ in = Σ out` (blind).
            Effect::ShieldedTransfer { .. } => LinearityClass::Conservative,
            // Obligation creation locks stake; fulfillment returns it;
            // slash transfers it. Each is a conservative move.

            // Queue enqueue/dequeue pair: the message moves; the
            // deposit moves with it (paid on enqueue, refunded on
            // dequeue).

            // Atomic queue transactions and pipeline steps batch
            // conservative moves; the executor enforces all-or-nothing.

            // Bridge phases form a cross-federation conservative
            // schedule: lock+finalize is the dual of mint on the other
            // side; cancel is a roll-back; lock-without-finalize is
            // value-locking, not value-creation.

            // -- Monotonic: scalar counters / refcounts going up. --
            Effect::IncrementNonce { .. } => LinearityClass::Monotonic,
            // (The retired CapTP verbs — ExportSturdyRef / EnlivenRef /
            // ValidateHandoff — were monotonic counter bumps; they no longer
            // exist as effects. Caps-in-slots replaced them.)

            // Refusals bump the cell's nonce and append to the
            // refusal-log slot; both monotonic.
            Effect::Refusal { .. } => LinearityClass::Monotonic,

            // -- Terminal: one-way state transitions, no inverse. --
            Effect::RevokeCapability { .. } => LinearityClass::Terminal,
            Effect::RevokeDelegation { .. } => LinearityClass::Terminal,
            // (Retired: DropRef — the CapTP refcount decrement — is gone with
            // the CapTP verb set.)

            // Cell destroy is the canonical terminal — once Destroyed
            // the cell cannot transition to any other state
            // (CellLifecycle::is_terminal).
            Effect::CellDestroy { .. } => LinearityClass::Terminal,
            // MakeSovereign drops local state in favor of a sovereign
            // commitment — that's a one-way move from the federation's
            // perspective.
            Effect::MakeSovereign { .. } => LinearityClass::Terminal,
            // ReceiptArchive sets the cell into Archived lifecycle;
            // the chain prefix is no longer locally addressable as
            // individual receipts (the attestation summarises it).
            Effect::ReceiptArchive { .. } => LinearityClass::Terminal,
            // AttenuateCapability only narrows — widening is rejected.
            // Once narrowed, you cannot widen back.
            Effect::AttenuateCapability { .. } => LinearityClass::Terminal,
            // Cell seal/unseal is *reversible* but the seal-while-
            // sealed transition is terminal in the sense that no
            // effects (other than CellUnseal) can target the cell.
            // Classify CellSeal as Terminal — its inverse is CellUnseal,
            // which is itself Terminal in the reverse direction; the
            // pair is *not* a balanced linear pair the way
            // Transfer/Mint+Burn is, because no resource is conserved.
            Effect::CellSeal { .. } => LinearityClass::Terminal,
            Effect::CellUnseal { .. } => LinearityClass::Terminal,

            // -- Generative: creates a resource ex nihilo. --
            // BridgeMint mints local notes from a remote spend proof —
            // generative from the local ledger's POV (the conservation
            // lives in the bridge protocol, not in this federation).
            Effect::BridgeMint { .. } => LinearityClass::Generative,
            Effect::CreateCell { .. } => LinearityClass::Generative,
            Effect::CreateCellFromFactory { .. } => LinearityClass::Generative,
            Effect::SpawnWithDelegation { .. } => LinearityClass::Generative,

            // (Retired: CreateSealPair / Seal — generative sealer/unsealer
            // handle creation — are gone with the CapTP verb set; sealing is
            // the CapSlotFactory caps-in-slots route now.)

            // Grant and Introduce mint new capability slots in the
            // recipient's c-list; from the receiving cell's POV
            // these are generative.
            Effect::GrantCapability { .. } => LinearityClass::Generative,
            Effect::Introduce { .. } => LinearityClass::Generative,

            // Promise / Notify mint a fresh promise-hole (a standing
            // commitment) in a cell's reactive registry — a resource created
            // without a paired consumer in the same turn. The dual is the
            // later React (Terminal) in a separate turn.
            Effect::Promise { .. } => LinearityClass::Generative,
            Effect::Notify { .. } => LinearityClass::Generative,

            // -- Annihilative: destroys a resource, operator-disclosed. --
            Effect::Burn { .. } => LinearityClass::Annihilative,

            // Mint creates fresh supply (well → holder) — a resource
            // produced without a paired consumer in the same turn (the
            // well-debit is the conserving dual, but from the holder's
            // POV value appears). The dual of Burn's Annihilative.
            Effect::Mint { .. } => LinearityClass::Generative,

            // React consumes (spends) a promise-hole exactly once: a one-way
            // structural transition with no inverse — the hole is gone. The
            // resource destroyed is the hole-nullifier, spent into the
            // production nullifier set (no monetary delta, so not disclosed
            // non-conservation; the consume is the dual of the Promise/Notify
            // that created it in a prior turn).
            Effect::React { .. } => LinearityClass::Terminal,

            // -- Neutral: no resource delta; state-local accounting. --
            Effect::SetField { .. } => LinearityClass::Neutral,
            Effect::EmitEvent { .. } => LinearityClass::Neutral,
            Effect::SetPermissions { .. } => LinearityClass::Neutral,
            Effect::SetVerificationKey { .. } => LinearityClass::Neutral,
            Effect::SetProgram { .. } => LinearityClass::Neutral,
            Effect::RefreshDelegation { .. } => LinearityClass::Neutral,
            Effect::PipelinedSend { .. } => LinearityClass::Neutral,
            Effect::ExerciseViaCapability { .. } => LinearityClass::Neutral,

            // A custom transition mutates only the SOVEREIGN COMMITMENT (an opaque
            // 8-felt root); it debits/credits no substrate-tracked linear resource
            // (balance/notes/caps). Conservation of the app's own resources is the
            // custom AIR's job, proven in the sub-proof and welded to the committed
            // roots — not a turn-effect-layer linearity obligation. So: Neutral.
            Effect::Custom { .. } => LinearityClass::Neutral,
        }
    }

    /// Compute the BLAKE3 hash of this effect.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        match self {
            Effect::SetField { cell, index, value } => {
                hasher.update(&[0u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&(*index as u64).to_le_bytes());
                hasher.update(value);
            }
            Effect::Transfer { from, to, amount } => {
                hasher.update(&[1u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(&amount.to_le_bytes());
            }
            Effect::GrantCapability { from, to, cap } => {
                hasher.update(&[2u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(cap.target.as_bytes());
                hasher.update(&cap.slot.to_le_bytes());
            }
            Effect::RevokeCapability { cell, slot } => {
                hasher.update(&[3u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&slot.to_le_bytes());
            }
            Effect::EmitEvent { cell, event } => {
                hasher.update(&[4u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&event.topic);
                for d in &event.data {
                    hasher.update(d);
                }
            }
            Effect::IncrementNonce { cell } => {
                hasher.update(&[5u8]);
                hasher.update(cell.as_bytes());
            }
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => {
                hasher.update(&[6u8]);
                hasher.update(public_key);
                hasher.update(token_id);
                hasher.update(&balance.to_le_bytes());
            }
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => {
                hasher.update(&[7u8]);
                hasher.update(cell.as_bytes());
                // Hash each permission field's discriminant.
                let perms = [
                    &new_permissions.send,
                    &new_permissions.receive,
                    &new_permissions.set_state,
                    &new_permissions.set_permissions,
                    &new_permissions.set_verification_key,
                    &new_permissions.increment_nonce,
                    &new_permissions.delegate,
                    &new_permissions.access,
                ];
                for p in perms {
                    match p {
                        dregg_cell::AuthRequired::None => {
                            hasher.update(&[0u8]);
                        }
                        dregg_cell::AuthRequired::Signature => {
                            hasher.update(&[1u8]);
                        }
                        dregg_cell::AuthRequired::Proof => {
                            hasher.update(&[2u8]);
                        }
                        dregg_cell::AuthRequired::Either => {
                            hasher.update(&[3u8]);
                        }
                        dregg_cell::AuthRequired::Impossible => {
                            hasher.update(&[4u8]);
                        }
                        dregg_cell::AuthRequired::Custom { vk_hash } => {
                            hasher.update(&[5u8]);
                            hasher.update(vk_hash);
                        }
                    }
                }
            }
            Effect::SetVerificationKey { cell, new_vk } => {
                hasher.update(&[8u8]);
                hasher.update(cell.as_bytes());
                if let Some(vk) = new_vk {
                    hasher.update(&[1u8]);
                    hasher.update(&vk.data);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Effect::SetProgram { cell, program } => {
                hasher.update(&[54u8]);
                hasher.update(cell.as_bytes());
                // Fold the program's canonical postcard bytes so distinct
                // programs hash distinctly (deterministic, like the wire codec).
                if let Ok(bytes) = postcard::to_allocvec(program) {
                    hasher.update(&bytes);
                }
            }
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                asset_type,
                spending_proof,
                value_commitment,
            } => {
                hasher.update(&[9u8]);
                hasher.update(&nullifier.0);
                hasher.update(note_tree_root);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(spending_proof);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::NoteCreate {
                commitment,
                value,
                asset_type,
                encrypted_note,
                value_commitment,
                range_proof,
            } => {
                hasher.update(&[10u8]);
                hasher.update(&commitment.0);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&(encrypted_note.len() as u64).to_le_bytes());
                hasher.update(encrypted_note);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                match range_proof {
                    Some(rp) => {
                        hasher.update(&[1u8]);
                        hasher.update(&(rp.len() as u64).to_le_bytes());
                        hasher.update(rp);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }

            Effect::BridgeMint { portable_proof } => {
                hasher.update(&[21u8]);
                hasher.update(&portable_proof.nullifier);
                hasher.update(&portable_proof.destination_commitment.0);
                hasher.update(&portable_proof.value.to_le_bytes());
                hasher.update(&portable_proof.asset_type.to_le_bytes());
                hasher.update(&portable_proof.source_root.merkle_root);
                hasher.update(&portable_proof.source_root.height.to_le_bytes());
            }

            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => {
                hasher.update(&[17u8]);
                hasher.update(introducer.as_bytes());
                hasher.update(recipient.as_bytes());
                hasher.update(target.as_bytes());
                match permissions {
                    dregg_cell::AuthRequired::None => {
                        hasher.update(&[0u8]);
                    }
                    dregg_cell::AuthRequired::Signature => {
                        hasher.update(&[1u8]);
                    }
                    dregg_cell::AuthRequired::Proof => {
                        hasher.update(&[2u8]);
                    }
                    dregg_cell::AuthRequired::Either => {
                        hasher.update(&[3u8]);
                    }
                    dregg_cell::AuthRequired::Impossible => {
                        hasher.update(&[4u8]);
                    }
                    dregg_cell::AuthRequired::Custom { vk_hash } => {
                        hasher.update(&[5u8]);
                        hasher.update(vk_hash);
                    }
                }
            }
            Effect::PipelinedSend { target, action } => {
                hasher.update(&[16u8]);
                hasher.update(&target.source_turn);
                hasher.update(&target.output_slot.to_le_bytes());
                hasher.update(&action.hash());
            }

            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => {
                hasher.update(&[18u8]);
                hasher.update(child_public_key);
                hasher.update(child_token_id);
                hasher.update(&max_staleness.to_le_bytes());
            }
            Effect::RefreshDelegation { child, snapshot } => {
                hasher.update(&[19u8]);
                hasher.update(child.as_bytes());
                hasher.update(snapshot);
            }
            Effect::RevokeDelegation { child } => {
                hasher.update(&[20u8]);
                hasher.update(child.as_bytes());
            }
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => {
                hasher.update(&[25u8]);
                hasher.update(&cap_slot.to_le_bytes());
                for inner in inner_effects {
                    hasher.update(&inner.hash());
                }
            }
            Effect::MakeSovereign { cell } => {
                hasher.update(&[35u8]);
                hasher.update(cell.as_bytes());
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            } => {
                hasher.update(&[36u8]);
                hasher.update(factory_vk);
                hasher.update(owner_pubkey);
                hasher.update(token_id);
                // Hash params deterministically.
                let mode_byte = match params.mode {
                    dregg_cell::CellMode::Hosted => 0u8,
                    dregg_cell::CellMode::Sovereign => 1u8,
                };
                hasher.update(&[mode_byte]);
                match &params.program_vk {
                    Some(vk) => {
                        hasher.update(&[1u8]);
                        hasher.update(vk);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                hasher.update(&(params.initial_fields.len() as u64).to_le_bytes());
                for (idx, val) in &params.initial_fields {
                    hasher.update(&idx.to_le_bytes());
                    hasher.update(&val.to_le_bytes());
                }
                hasher.update(&(params.initial_caps.len() as u64).to_le_bytes());
                for cap in &params.initial_caps {
                    match &cap.target {
                        dregg_cell::factory::CapTarget::SelfCell => {
                            hasher.update(&[0u8]);
                        }
                        dregg_cell::factory::CapTarget::Specific(id) => {
                            hasher.update(&[1u8]);
                            hasher.update(id.as_bytes());
                        }
                        dregg_cell::factory::CapTarget::Any => {
                            hasher.update(&[2u8]);
                        }
                    }
                    hash_auth_required(&mut hasher, &cap.max_permissions);
                    hasher.update(&[cap.attenuatable as u8]);
                }
                hasher.update(&params.owner_pubkey);
            }

            // ── CapTP runtime effects (Stage 7 / P1.A) ────────────────────
            Effect::CellSeal { target, reason } => {
                hasher.update(&[48u8]);
                hasher.update(target.as_bytes());
                hasher.update(reason);
            }
            Effect::CellUnseal { target } => {
                hasher.update(&[49u8]);
                hasher.update(target.as_bytes());
            }
            Effect::CellDestroy {
                target,
                certificate,
            } => {
                hasher.update(&[50u8]);
                hasher.update(target.as_bytes());
                // Bind the canonical death-certificate hash (cell-side
                // routine `DeathCertificate::certificate_hash`).
                hasher.update(&certificate.certificate_hash());
            }
            Effect::Burn {
                target,
                slot,
                amount,
            } => {
                hasher.update(&[51u8]);
                hasher.update(target.as_bytes());
                hasher.update(&slot.to_le_bytes());
                hasher.update(&amount.to_le_bytes());
            }
            Effect::Mint {
                target,
                slot,
                amount,
            } => {
                hasher.update(&[63u8]);
                hasher.update(target.as_bytes());
                hasher.update(&slot.to_le_bytes());
                hasher.update(&amount.to_le_bytes());
            }
            Effect::AttenuateCapability {
                cell,
                slot,
                narrower_permissions,
                narrower_effects,
                narrower_expiry,
            } => {
                hasher.update(&[52u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&slot.to_le_bytes());
                match narrower_permissions {
                    AuthRequired::None => {
                        hasher.update(&[0u8]);
                    }
                    AuthRequired::Signature => {
                        hasher.update(&[1u8]);
                    }
                    AuthRequired::Proof => {
                        hasher.update(&[2u8]);
                    }
                    AuthRequired::Either => {
                        hasher.update(&[3u8]);
                    }
                    AuthRequired::Impossible => {
                        hasher.update(&[4u8]);
                    }
                    AuthRequired::Custom { vk_hash } => {
                        hasher.update(&[5u8]);
                        hasher.update(vk_hash);
                    }
                }
                match narrower_effects {
                    Some(mask) => {
                        hasher.update(&[1u8]);
                        hasher.update(&mask.to_le_bytes());
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                match narrower_expiry {
                    Some(exp) => {
                        hasher.update(&[1u8]);
                        hasher.update(&exp.to_le_bytes());
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::ReceiptArchive {
                prefix_end_height,
                checkpoint,
            } => {
                hasher.update(&[53u8]);
                hasher.update(&prefix_end_height.to_le_bytes());
                hasher.update(&checkpoint.checkpoint_hash());
            }
            Effect::Refusal {
                cell,
                offered_action_commitment,
                refusal_reason,
                proof_witness_index,
            } => {
                hasher.update(&[47u8]);
                hasher.update(cell.as_bytes());
                hasher.update(offered_action_commitment);
                match refusal_reason {
                    RefusalReason::Declined => {
                        hasher.update(&[0u8]);
                    }
                    RefusalReason::NoAuthority => {
                        hasher.update(&[1u8]);
                    }
                    RefusalReason::WindowExpired => {
                        hasher.update(&[2u8]);
                    }
                    RefusalReason::Custom { reason_hash } => {
                        hasher.update(&[3u8]);
                        hasher.update(reason_hash);
                    }
                }
                hasher.update(&proof_witness_index.to_le_bytes());
            }
            Effect::Promise {
                cell,
                resolution_condition,
                wake,
                timeout_height,
            } => {
                hasher.update(&[60u8]);
                hasher.update(cell.as_bytes());
                // Canonical postcard encoding of the resolution condition.
                let rc = postcard::to_allocvec(resolution_condition).unwrap_or_default();
                hasher.update(&(rc.len() as u64).to_le_bytes());
                hasher.update(&rc);
                hasher.update(&wake.hash());
                hasher.update(&timeout_height.to_le_bytes());
            }
            Effect::Notify {
                from,
                to,
                wake,
                resolution_condition,
                timeout_height,
            } => {
                hasher.update(&[61u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(&wake.hash());
                let rc = postcard::to_allocvec(resolution_condition).unwrap_or_default();
                hasher.update(&(rc.len() as u64).to_le_bytes());
                hasher.update(&rc);
                hasher.update(&timeout_height.to_le_bytes());
            }
            Effect::React {
                pending_id,
                condition,
                resolution_proof,
                wake,
            } => {
                hasher.update(&[62u8]);
                // The hole-as-nullifier — the same shape NoteSpend folds (the
                // 32-byte nullifier directly into the effect hash).
                hasher.update(&pending_id.0);
                let c = postcard::to_allocvec(condition).unwrap_or_default();
                hasher.update(&(c.len() as u64).to_le_bytes());
                hasher.update(&c);
                let p = postcard::to_allocvec(resolution_proof).unwrap_or_default();
                hasher.update(&(p.len() as u64).to_le_bytes());
                hasher.update(&p);
                hasher.update(&wake.hash());
            }
            Effect::ShieldedTransfer { payload } => {
                hasher.update(&[63u8]);
                hasher.update(&payload.merkle_root.to_le_bytes());
                hasher.update(&(payload.inputs.len() as u64).to_le_bytes());
                for input in &payload.inputs {
                    hasher.update(&input.nullifier.to_le_bytes());
                    hasher.update(&input.value_binding.to_le_bytes());
                    hasher.update(&(input.proof.len() as u64).to_le_bytes());
                    hasher.update(&input.proof);
                }
                for (tag, legs) in [(0u8, &payload.input_legs), (1u8, &payload.output_legs)] {
                    hasher.update(&[tag]);
                    hasher.update(&(legs.len() as u64).to_le_bytes());
                    for leg in legs {
                        hasher.update(&leg.asset_type.to_le_bytes());
                        hasher.update(&leg.commitment_bytes);
                    }
                }
                hasher.update(&(payload.output_range_proofs.len() as u64).to_le_bytes());
                for rp in &payload.output_range_proofs {
                    hasher.update(&(rp.len() as u64).to_le_bytes());
                    hasher.update(rp);
                }
                let c = postcard::to_allocvec(&payload.conservation).unwrap_or_default();
                hasher.update(&(c.len() as u64).to_le_bytes());
                hasher.update(&c);
            }
            Effect::Custom {
                cell,
                program_vk_hash,
                proof_commitment,
            } => {
                hasher.update(&[64u8]);
                hasher.update(cell.as_bytes());
                hasher.update(program_vk_hash);
                hasher.update(proof_commitment);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Return the number of bytes of data in this effect (for cost estimation).
    pub fn data_bytes(&self) -> usize {
        match self {
            Effect::SetField { .. } => 32 + 8 + 32, // cell + index + value
            Effect::Transfer { .. } => 32 + 32 + 8,
            Effect::GrantCapability { .. } => 32 + 32 + 36,
            Effect::RevokeCapability { .. } => 32 + 4,
            Effect::EmitEvent { event, .. } => 32 + 32 + event.data.len() * 32,
            Effect::IncrementNonce { .. } => 32,
            Effect::CreateCell { .. } => 32 + 32 + 8,
            Effect::SetPermissions { .. } => 32 + 8 * 1, // cell + 8 permission fields
            Effect::SetVerificationKey { new_vk, .. } => {
                32 + new_vk.as_ref().map_or(1, |vk| 1 + vk.data.len())
            }
            Effect::NoteSpend {
                spending_proof,
                value_commitment,
                ..
            } => {
                32 + 32 + 8 + 8 + spending_proof.len() + value_commitment.map_or(0, |_| 32) // nullifier + root + value + asset_type + proof + opt commitment
            }
            Effect::NoteCreate {
                encrypted_note,
                value_commitment,
                range_proof,
                ..
            } => {
                32 + 8
                    + 8
                    + encrypted_note.len()
                    + value_commitment.map_or(0, |_| 32)
                    + range_proof.as_ref().map_or(0, |rp| rp.len()) // commitment + value + asset_type + ciphertext + opt vc + opt rp
            }

            Effect::BridgeMint { portable_proof } => {
                32 + 32 + 8 + 8 + portable_proof.spending_proof.len() // nullifier + commitment + value + asset + proof
            }

            // nullifier
            Effect::PipelinedSend { .. } => 32 + 4 + 32,
            Effect::Introduce { .. } => 97,
            Effect::SpawnWithDelegation { .. } => 32 + 32 + 8,
            Effect::RefreshDelegation { .. } => 32 + 32, // child + snapshot
            Effect::RevokeDelegation { .. } => 32,

            Effect::ExerciseViaCapability { inner_effects, .. } => {
                4 + inner_effects.iter().map(|e| e.data_bytes()).sum::<usize>()
            }
            Effect::MakeSovereign { .. } => 32, // cell id
            Effect::CreateCellFromFactory { params, .. } => {
                32 + 32
                    + 32
                    + 1
                    + 33
                    + params.initial_fields.len() * 12
                    + params.initial_caps.len() * 34
                    + 32
            }

            // queue + message_hash + deposit
            // queue
            // queue + new_capacity

            // CapTP runtime effects: small fixed-size blobs.
            // swiss + target + perms (1 byte + opt 32-byte vk_hash for Custom)
            // swiss + bearer + expected_cell_id + perms
            // ref_id
            // cert_hash + recipient_pk + introducer_pk
            // Refusal: cell + commitment + reason-discriminant (+ opt 32-byte
            // custom reason hash) + u32 witness index.
            Effect::Refusal { refusal_reason, .. } => {
                32 + 32
                    + 1
                    + match refusal_reason {
                        RefusalReason::Custom { .. } => 32,
                        _ => 0,
                    }
                    + 4
            }
            // Lifecycle effects: small fixed-size payloads.
            Effect::CellSeal { .. } => 32 + 32, // target + reason
            Effect::CellUnseal { .. } => 32,    // target
            Effect::CellDestroy { .. } => 32 + 32, // target + cert hash
            Effect::Burn { .. } => 32 + 4 + 8,  // target + slot + amount
            Effect::Mint { .. } => 32 + 4 + 8,  // target + slot + amount
            Effect::AttenuateCapability { .. } => 32 + 4 + 1 + 4 + 8, // cell + slot + perms + mask + expiry
            Effect::ReceiptArchive { .. } => 8 + 32,                  // height + checkpoint hash
            // cell + the program's canonical postcard length.
            Effect::SetProgram { program, .. } => {
                32 + postcard::to_allocvec(program).map(|b| b.len()).unwrap_or(0)
            }
            // Reactive effects: cell ids + wake-turn hash + canonical condition/
            // proof encodings (the carried turn dominates; charge its hash size).
            Effect::Promise {
                resolution_condition,
                ..
            } => 32 + 32 + 8 + postcard::to_allocvec(resolution_condition).map_or(0, |b| b.len()),
            Effect::Notify {
                resolution_condition,
                ..
            } => {
                32 + 32
                    + 32
                    + 8
                    + postcard::to_allocvec(resolution_condition).map_or(0, |b| b.len())
            }
            Effect::React {
                condition,
                resolution_proof,
                ..
            } => {
                32 + 32
                    + postcard::to_allocvec(condition).map_or(0, |b| b.len())
                    + postcard::to_allocvec(resolution_proof).map_or(0, |b| b.len())
            }
            // Shielded transfer: dominated by the hidden per-input STARK proofs +
            // the value-commitment legs + range proofs + conservation proof.
            Effect::ShieldedTransfer { payload } => {
                4 + payload
                    .inputs
                    .iter()
                    .map(|i| 4 + 4 + 8 + i.proof.len())
                    .sum::<usize>()
                    + (payload.input_legs.len() + payload.output_legs.len()) * (8 + 32)
                    + payload
                        .output_range_proofs
                        .iter()
                        .map(|rp| 8 + rp.len())
                        .sum::<usize>()
                    + 96 // the three 32-byte ConservationProof fields
            }
            // Custom: the bridge preimage only — cell + program vk_hash + the
            // 8-felt PI-commitment carrier. The sub-proof BYTES are not carried by
            // the effect; they ride `Turn::custom_program_proofs` (and are charged
            // where the turn is sized), so this is the effect's own data footprint.
            Effect::Custom { .. } => 32 + 32 + 32,
        }
    }

    /// Returns true if this effect is a permission-changing effect.
    ///
    /// Permission-changing effects (SetPermissions, SetVerificationKey) are always
    /// applied LAST within an action to prevent an action from weakening permissions
    /// and exploiting the weakened state in subsequent effects.
    pub fn is_permission_effect(&self) -> bool {
        matches!(
            self,
            Effect::SetPermissions { .. }
                | Effect::SetVerificationKey { .. }
                | Effect::SetProgram { .. }
        )
    }

    /// Return the effect kind bitmask for this effect.
    ///
    /// Used by `ExerciseViaCapability` to check whether a faceted capability
    /// permits this operation. Each effect type maps to exactly one bit in the
    /// [`EffectMask`](dregg_cell::EffectMask).
    pub fn effect_kind_mask(&self) -> dregg_cell::EffectMask {
        match self {
            Effect::SetField { .. } => dregg_cell::EFFECT_SET_FIELD,
            Effect::Transfer { .. } => dregg_cell::EFFECT_TRANSFER,
            Effect::GrantCapability { .. } => dregg_cell::EFFECT_GRANT_CAPABILITY,
            Effect::RevokeCapability { .. } => dregg_cell::EFFECT_REVOKE_CAPABILITY,
            Effect::EmitEvent { .. } => dregg_cell::EFFECT_EMIT_EVENT,
            Effect::IncrementNonce { .. } => dregg_cell::EFFECT_INCREMENT_NONCE,
            Effect::CreateCell { .. } => dregg_cell::EFFECT_CREATE_CELL,
            Effect::SetPermissions { .. } => dregg_cell::EFFECT_SET_PERMISSIONS,
            Effect::SetVerificationKey { .. } => dregg_cell::EFFECT_SET_VERIFICATION_KEY,
            // A program install (rewriting the cell's caveat program) is its OWN
            // authority surface — DISTINCT from VK rotation: a cap that grants VK
            // rotation must not implicitly grant a program install. Its in-circuit
            // witness is the record-pin `setProgramV3` descriptor + the
            // `setProgram_descriptorRefines_sat` rung (the program folds into
            // `compute_authority_digest_felt`, r23 / B_RECORD_DIGEST).
            Effect::SetProgram { .. } => dregg_cell::EFFECT_SET_PROGRAM,
            Effect::NoteSpend { .. } => dregg_cell::EFFECT_NOTE_SPEND,
            Effect::NoteCreate { .. } => dregg_cell::EFFECT_NOTE_CREATE,

            Effect::Introduce { .. } | Effect::PipelinedSend { .. } => dregg_cell::EFFECT_INTRODUCE,
            Effect::BridgeMint { .. } => dregg_cell::EFFECT_BRIDGE_OPS,
            Effect::SpawnWithDelegation { .. }
            | Effect::RefreshDelegation { .. }
            | Effect::RevokeDelegation { .. } => dregg_cell::EFFECT_DELEGATION_OPS,
            Effect::ExerciseViaCapability { .. } => dregg_cell::EFFECT_ALL,
            Effect::MakeSovereign { .. } => dregg_cell::EFFECT_SOVEREIGN_OPS,
            Effect::CreateCellFromFactory { .. } => dregg_cell::EFFECT_CREATE_CELL,

            Effect::Refusal { .. } => dregg_cell::EFFECT_REFUSAL,
            Effect::CellSeal { .. }
            | Effect::CellUnseal { .. }
            | Effect::CellDestroy { .. }
            | Effect::ReceiptArchive { .. } => dregg_cell::EFFECT_LIFECYCLE_OPS,
            Effect::Burn { .. } => dregg_cell::EFFECT_BURN,
            Effect::Mint { .. } => dregg_cell::EFFECT_MINT,
            Effect::AttenuateCapability { .. } => dregg_cell::EFFECT_ATTENUATE_CAPABILITY,
            Effect::Promise { .. } | Effect::Notify { .. } | Effect::React { .. } => {
                dregg_cell::EFFECT_REACTIVE_OPS
            }
            // A shielded transfer consumes (hidden) note nullifiers — the same
            // note-spend facet a faceted capability gates `NoteSpend` with.
            Effect::ShieldedTransfer { .. } => dregg_cell::EFFECT_NOTE_SPEND,
            // A custom transition advances a SOVEREIGN cell's committed root under
            // an external proof — the sovereign-ops facet, the same class a faceted
            // capability would gate `MakeSovereign` / proof-carrying operation with.
            Effect::Custom { .. } => dregg_cell::EFFECT_SOVEREIGN_OPS,
        }
    }
}

impl Event {
    /// Create a new event.
    pub fn new(topic: Symbol, data: Vec<FieldElement>) -> Self {
        Self { topic, data }
    }
}

// =============================================================================
// LinearityClass tests
// =============================================================================
//
// Per `HOUYHNHNM-COMPARISON.md` §4.3, §8.2: the conservation question must
// have a typed, *forced* answer. These tests assert the contract:
//
//   * Conservative effects declare they need a paired sibling (the
//     executor's conservation checker dispatches off this).
//   * Disclosed non-conservation (Generative / Annihilative) is named
//     `is_disclosed_non_conservation()` and reachable for Mint / Burn.
//   * Neutral effects don't claim conservation they don't enforce.
//
// The `linearity()` method itself is exhaustive at compile time; adding a
// new `Effect` variant without answering the linearity question is a
// `rustc` error, not a runtime surprise.
#[cfg(test)]
mod linearity_tests {
    use super::*;

    fn cid(byte: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = byte;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn create_cell_from_factory_hash_binds_initial_cap_contents() {
        let mut cap_a_target = [0u8; 32];
        cap_a_target[0] = 0xA0;
        let mut cap_b_target = [0u8; 32];
        cap_b_target[0] = 0xB0;

        let base_params = dregg_cell::FactoryCreationParams {
            mode: dregg_cell::CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![dregg_cell::factory::CapGrant {
                target: dregg_cell::factory::CapTarget::Specific(CellId(cap_a_target)),
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            owner_pubkey: [1u8; 32],
        };
        let mut tampered_params = base_params.clone();
        tampered_params.initial_caps[0] = dregg_cell::factory::CapGrant {
            target: dregg_cell::factory::CapTarget::Specific(CellId(cap_b_target)),
            max_permissions: AuthRequired::None,
            attenuatable: false,
        };

        let honest = Effect::CreateCellFromFactory {
            factory_vk: [2u8; 32],
            owner_pubkey: [1u8; 32],
            token_id: [3u8; 32],
            params: base_params,
        };
        let tampered = Effect::CreateCellFromFactory {
            factory_vk: [2u8; 32],
            owner_pubkey: [1u8; 32],
            token_id: [3u8; 32],
            params: tampered_params,
        };

        assert_ne!(
            honest.hash(),
            tampered.hash(),
            "initial capability contents, not only their count, must be effect-hash-bound"
        );
    }

    #[test]
    fn transfer_is_conservative_and_requires_sibling() {
        // Adversarial framing: a Transfer claims Conservative linearity,
        // which the executor's conservation checker reads as
        // "demand a paired credit on the receive side."
        let e = Effect::Transfer {
            from: cid(1),
            to: cid(2),
            amount: 7,
        };
        assert_eq!(e.linearity(), LinearityClass::Conservative);
        assert!(e.linearity().requires_paired_sibling());
        assert!(!e.linearity().is_disclosed_non_conservation());
    }

    #[test]
    fn mint_without_paired_burn_is_generative_not_conservative() {
        // **Adversarial:** an `Effect::CreateCell` / mint-like move is
        // *generative* — the conservation checker MUST NOT require a
        // paired sibling, but the operator MUST be authorized to mint
        // (caught elsewhere). If we accidentally tagged CreateCell as
        // `Conservative`, the checker would reject every legitimate
        // genesis-style mint. If we accidentally tagged it `Neutral`,
        // the operator could mint without disclosure.
        let e = Effect::CreateCell {
            public_key: [0; 32],
            token_id: [0; 32],
            balance: 1_000_000,
        };
        assert_eq!(e.linearity(), LinearityClass::Generative);
        assert!(!e.linearity().requires_paired_sibling());
        assert!(e.linearity().is_disclosed_non_conservation());
        // Equivalent for SpawnWithDelegation: a fresh-child mint must
        // also be generative.
        let e2 = Effect::SpawnWithDelegation {
            child_public_key: [0; 32],
            child_token_id: [0; 32],
            max_staleness: 0,
        };
        assert_eq!(e2.linearity(), LinearityClass::Generative);
    }

    #[test]
    fn burn_is_annihilative_and_disclosed() {
        // **Adversarial:** Burn's disclosure (`was_burn`) is bound into
        // `receipt_hash`. If LinearityClass::Burn were mis-tagged as
        // `Neutral`, the executor would not know to *require* the
        // disclosure flag; mis-tagging as `Conservative` would make the
        // checker demand a paired credit that doesn't exist. The only
        // correct tag is `Annihilative`.
        let e = Effect::Burn {
            target: cid(3),
            slot: 0,
            amount: 42,
        };
        assert_eq!(e.linearity(), LinearityClass::Annihilative);
        assert!(!e.linearity().requires_paired_sibling());
        assert!(e.linearity().is_disclosed_non_conservation());
    }

    #[test]
    fn terminal_effects_dont_require_pairing() {
        // Revoke is one-way; it MUST NOT trip the "demand a paired sibling" branch.
        let revoke = Effect::RevokeCapability {
            cell: cid(1),
            slot: 0,
        };
        let e = revoke;
        assert_eq!(e.linearity(), LinearityClass::Terminal);
        assert!(!e.linearity().requires_paired_sibling());
        assert!(!e.linearity().is_disclosed_non_conservation());
    }

    #[test]
    fn monotonic_counters_are_neither_conservative_nor_disclosed() {
        let e = Effect::IncrementNonce { cell: cid(4) };
        assert_eq!(e.linearity(), LinearityClass::Monotonic);
        assert!(!e.linearity().requires_paired_sibling());
        assert!(!e.linearity().is_disclosed_non_conservation());
    }

    #[test]
    fn neutral_effects_have_no_resource_delta() {
        // SetField on a cell-local slot has no resource delta from the
        // ledger's POV — the cell's own program may enforce a delta,
        // but the universal conservation checker doesn't see one here.
        let e = Effect::SetField {
            cell: cid(5),
            index: 0,
            value: [0; 32],
        };
        assert_eq!(e.linearity(), LinearityClass::Neutral);
        assert!(!e.linearity().requires_paired_sibling());
        assert!(!e.linearity().is_disclosed_non_conservation());
    }

    #[test]
    fn disclosed_predicate_is_only_generative_and_annihilative() {
        // The disclosed-non-conservation set MUST be exactly Generative
        // ∪ Annihilative. Conservation-respecting variants (Conservative,
        // Monotonic, Terminal, Neutral) MUST NOT be flagged as
        // disclosed non-conservation; doing so would prompt the
        // executor to expect a `was_burn`/`was_mint` flag that isn't
        // there and reject legitimate turns.
        for c in [
            LinearityClass::Conservative,
            LinearityClass::Monotonic,
            LinearityClass::Terminal,
            LinearityClass::Neutral,
        ] {
            assert!(
                !c.is_disclosed_non_conservation(),
                "{c:?} must not be a disclosed non-conservation class"
            );
        }
        for c in [LinearityClass::Generative, LinearityClass::Annihilative] {
            assert!(
                c.is_disclosed_non_conservation(),
                "{c:?} must be a disclosed non-conservation class"
            );
        }
    }
}
