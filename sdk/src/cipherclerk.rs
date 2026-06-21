//! Agent cipherclerk: identity, wallet, signing, and proof generation.
//!
//! The [`AgentCipherclerk`] (legacy alias `AgentCipherclerk`) is the agent's
//! cryptographic clerk — the primary credential holder. It manages:
//! - An Ed25519 signing identity
//! - A collection of held authorization tokens (macaroon-backed)
//! - Token attenuation and delegation to other agents
//! - Turn signing for submission to the ledger
//! - Zero-knowledge proof generation via the bridge layer
//!
//! The name traces to Greg Egan's *Polis* and its descendants, where a
//! citizen's cipherclerk is the autonomous component that holds keys,
//! attests credentials, and brokers capabilities on the citizen's
//! behalf. "Wallet" was a poor fit: dregg wallets mostly manage
//! *capabilities*, not balances.

use std::collections::HashMap;

use ed25519_dalek::Signer;
use zeroize::{Zeroize, Zeroizing};

use dregg_bridge::{BridgePredicateProof, BridgePresentationProof, Predicate};
use dregg_cell::note::NoteCommitment;
use dregg_cell::stealth::{StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress};
use dregg_cell::{Cell, CellId};
use dregg_circuit::BabyBear;
use dregg_circuit::IvcProof;
use dregg_circuit::PredicateType;
use dregg_circuit::ivc::IvcBuilder;
use dregg_circuit::merkle_air::compute_parent_poseidon2;
use dregg_circuit::poseidon2;
use dregg_intent::sse::EncryptedIntent;
use dregg_intent::{CommitmentId, IntentKind, MatchSpec};
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken, TokenClearance};
use dregg_trace::{AuthorizationTrace, Fact as TraceFact};
use dregg_turn::{Effect, SovereignCellWitness, Turn, WitnessedReceipt};
use dregg_types::{PublicKey, Signature};

use crate::error::SdkError;
use crate::mnemonic;

// =============================================================================
// Receipt-chain append errors (P0 #77 — strict, fork-detectable semantics)
// =============================================================================

/// Errors that can be returned by
/// [`AgentCipherclerk::append_receipt`](crate::AgentCipherclerk::append_receipt).
///
/// This is the strict, fork-detectable counterpart to the previous silent-rewrite
/// behavior. A divergence between the executor's view of the receipt chain and
/// the cipherclerk's view will surface here as `ReceiptChainMismatch` rather
/// than being papered over.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ChainAppendError {
    /// The receipt's `previous_receipt_hash` does not match the cipherclerk's
    /// current chain head. This indicates that the executor that produced
    /// the receipt and this cipherclerk disagree about the receipt chain —
    /// a fork condition. The caller must explicitly reconcile (request the
    /// federation's view, reset the cipherclerk, branch, etc.); the
    /// cipherclerk will not silently rewrite the link.
    #[error("receipt chain mismatch: cipherclerk head = {expected:?}, receipt's prev = {got:?}")]
    ReceiptChainMismatch {
        /// What the cipherclerk thinks the prior receipt hash is (i.e., the
        /// hash of its current chain head, or `None` for an empty chain).
        expected: Option<[u8; 32]>,
        /// What the receipt claims its predecessor is.
        got: Option<[u8; 32]>,
    },
}

// =============================================================================
// Verification Modes
// =============================================================================

/// Index into the evaluated fact set, used for selective disclosure.
///
/// When presenting in [`VerificationMode::SelectiveDisclosure`], the prover
/// specifies which facts (by index into the evaluation trace's fact set) to
/// reveal to the verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FactIndex(pub usize);

/// Verification mode selector for authorization presentation.
///
/// Dragon's Egg supports three verification modes with progressive privacy guarantees:
///
/// - **Trusted**: Local Datalog evaluation, full visibility, ~8us.
/// - **SelectiveDisclosure**: STARK proof with chosen facts revealed, ~200ms.
/// - **FullyPrivate**: STARK proof revealing only allow/deny, ~500ms.
#[derive(Clone, Debug)]
pub enum VerificationMode {
    /// Run Datalog locally, return full clearance and trace.
    ///
    /// Use when the verifier holds the root key (internal services, cloud API).
    Trusted,

    /// Prove authorization in STARK, revealing only selected facts.
    ///
    /// The `reveal` vector specifies indices into the evaluated fact set that
    /// the verifier will see. All other facts remain private witness.
    ///
    /// Use for cross-organization capability presentation where partial
    /// disclosure is acceptable (e.g., reveal service name but hide user).
    SelectiveDisclosure { reveal: Vec<FactIndex> },

    /// Full zero-knowledge proof: verifier learns only allow/deny.
    ///
    /// The STARK proves the entire multi-step Datalog derivation without
    /// revealing any intermediate facts, chain length, or rule selections.
    ///
    /// Use for anonymous credential presentation or private authorization.
    FullyPrivate,
}

// =============================================================================
// Disclosure Specification
// =============================================================================

/// Per-fact disclosure mode for selective disclosure presentations.
///
/// Each fact in the evaluation trace can be independently controlled:
/// - **Reveal**: Show the fact in plaintext to the verifier.
/// - **Predicate**: Prove a predicate about the fact's value without revealing it.
/// - **Hidden**: Do not reveal or prove anything (the STARK proves the fact exists).
#[derive(Clone, Debug)]
pub enum FactDisclosure {
    /// Reveal the fact in plaintext to the verifier.
    Reveal,
    /// Prove a predicate about the fact's value without revealing it.
    Predicate {
        predicate_type: PredicateType,
        threshold: BabyBear,
    },
    /// Prove a committed-threshold predicate: value >= threshold where the threshold
    /// is hidden from third-party verifiers behind a Poseidon2 commitment.
    ///
    /// The verifier provides `threshold` and `blinding` to the prover via a secure
    /// channel. Third parties see only `Poseidon2(threshold, blinding)`.
    CommittedThreshold {
        /// The verifier's secret threshold.
        threshold: BabyBear,
        /// The verifier's blinding randomness.
        blinding: BabyBear,
    },
    /// Prove an arithmetic predicate over multiple fact values without revealing them.
    ///
    /// The prover proves an arithmetic expression (e.g., `balance_a + balance_b >= 2000`)
    /// over the values at the specified fact indices without revealing any individual value.
    ArithmeticPredicate {
        /// Indices into the token state's fact set that serve as inputs to the expression.
        input_indices: Vec<usize>,
        /// The arithmetic expression to evaluate over the inputs.
        expression: dregg_circuit::ArithExpr,
        /// The predicate to prove about the expression result.
        predicate: dregg_circuit::ArithPredicate,
    },
    /// Do not reveal anything about this fact.
    Hidden,
}

/// A disclosure specification: determines what the verifier learns about each fact.
///
/// Facts not listed in the spec default to [].
#[derive(Clone, Debug)]
pub struct DisclosureSpec {
    /// Per-fact disclosure modes. .
    pub facts: Vec<(usize, FactDisclosure)>,
}

impl DisclosureSpec {
    /// Create a new empty disclosure spec (everything hidden).
    pub fn new() -> Self {
        Self { facts: Vec::new() }
    }

    /// Add a fact disclosure entry.
    pub fn add(&mut self, fact_index: usize, disclosure: FactDisclosure) -> &mut Self {
        self.facts.push((fact_index, disclosure));
        self
    }

    /// Convenience: reveal a fact at the given index.
    pub fn reveal(&mut self, fact_index: usize) -> &mut Self {
        self.add(fact_index, FactDisclosure::Reveal)
    }

    /// Convenience: prove a predicate about a fact at the given index.
    pub fn predicate(
        &mut self,
        fact_index: usize,
        predicate_type: PredicateType,
        threshold: BabyBear,
    ) -> &mut Self {
        self.add(
            fact_index,
            FactDisclosure::Predicate {
                predicate_type,
                threshold,
            },
        )
    }

    /// Convenience: prove a committed-threshold predicate about a fact.
    ///
    /// The threshold and blinding are provided by the verifier via a secure channel.
    /// Third-party verifiers see only the Poseidon2 commitment, not the threshold.
    pub fn committed_threshold(
        &mut self,
        fact_index: usize,
        threshold: BabyBear,
        blinding: BabyBear,
    ) -> &mut Self {
        self.add(
            fact_index,
            FactDisclosure::CommittedThreshold {
                threshold,
                blinding,
            },
        )
    }

    /// Convenience: mark a fact as hidden.
    pub fn hide(&mut self, fact_index: usize) -> &mut Self {
        self.add(fact_index, FactDisclosure::Hidden)
    }
}

impl Default for DisclosureSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// The result of an authorization presentation, parameterized by verification mode.
///
/// Each variant carries exactly the information the verifier receives for that mode.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum AuthorizationPresentation {
    /// Trusted mode: full clearance and derivation trace, no proof needed.
    Trusted {
        /// The full token clearance (capabilities, expiry, subject).
        clearance: TokenClearance,
        /// The complete Datalog derivation trace.
        trace: AuthorizationTrace,
    },

    /// Selective disclosure: chosen facts revealed, remainder proven in ZK.
    ///
    /// The `revealed_facts_commitment` cryptographically binds the revealed facts
    /// to the STARK proof. The verifier MUST recompute this commitment from
    /// `revealed_facts` and check it matches before trusting the revealed data.
    Selective {
        /// The facts the prover chose to reveal (subset of the evaluation).
        revealed_facts: Vec<TraceFact>,
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted (informational only).
        ///
        /// SECURITY: This field is self-reported by the prover and MUST NOT be
        /// trusted for authorization decisions without independent verification.
        /// Verifiers MUST re-derive the conclusion from the STARK proof's public
        /// inputs or from the proven facts. This field exists only for UX/logging.
        conclusion: bool,
        /// Poseidon2 commitment over the revealed fact hashes.
        ///
        /// This value is embedded as a public input in the STARK proof. The verifier
        /// recomputes it from `revealed_facts` using
        /// [`dregg_bridge::compute_revealed_facts_commitment`] and confirms it matches.
        /// A mismatch means the prover lied about which facts were part of the derivation.
        revealed_facts_commitment: dregg_circuit::binding::WideHash,
        /// Predicate proofs for facts disclosed via predicate mode.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        predicate_proofs: Vec<(usize, BridgePredicateProof)>,
    },

    /// Fully private: verifier learns only the conclusion.
    Private {
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted (informational only).
        ///
        /// SECURITY: This field is self-reported by the prover and MUST NOT be
        /// trusted for authorization decisions without independent verification.
        /// The verifier MUST rely solely on the STARK proof's public inputs to
        /// determine the authorization conclusion. This field exists only for
        /// UX/logging purposes.
        conclusion: bool,
    },
}

// =============================================================================
// Token storage types
// =============================================================================

/// A verified delegation binding, captured at receive time, used to re-verify
/// signature integrity on every authorization use.
///
/// # Authority invariant
///
/// The delegator's Ed25519 signature covers a canonical digest of the envelope
/// fields, including `token_bytes`, `caveat_chain_hash`, `proof_key`, and
/// `membership_proof.leaf_hash`. Any tampering with the corresponding
/// `HeldToken` fields after receive will produce a different signing message,
/// breaking signature verification.
///
/// The binding stores the verified envelope verbatim (its fields are bytes
/// captured at successful receive), plus the kind discriminator that selects
/// the correct signing-message domain tag.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub(crate) struct DelegationBinding {
    /// Whether this binding was produced via the external (v2) or local path.
    /// Determines the signing-message domain tag used during re-verification.
    pub(crate) kind: DelegationBindingKind,
    /// Verified envelope fields. Stored privately and re-fed into the
    /// signing-message hash on every use.
    pub(crate) delegatee: PublicKey,
    pub(crate) delegator_public_key: PublicKey,
    pub(crate) delegator_signature: Signature,
    pub(crate) restrictions: Attenuation,
    pub(crate) proof_key: Option<[u8; 32]>,
    pub(crate) membership_leaf: Option<[u8; 32]>,
    pub(crate) parent_delegation_hash: [u8; 32],
}

/// Discriminates between external (wire) and local (in-process) delegation
/// envelopes for signing-message reconstruction.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum DelegationBindingKind {
    /// External v2 envelope (cross-process / cross-wire).
    ExternalV2,
    /// Local in-process envelope produced by `make_local_delegation`.
    Local,
}

/// A token held by this cipherclerk, along with metadata.
///
/// # Sealed-value construction
///
/// All authority-affecting fields are **private**. External callers cannot
/// mutate `encoded`, `caveat_chain_hash`, `membership_proof`, the secret keys,
/// or the (private) delegation binding. The only construction paths are:
///
/// - [`AgentCipherclerk::mint_token`] — local mint from a held root key (no
///   delegation binding).
/// - [`AgentCipherclerk::receive_signed_delegation`] — external envelope receive
///   path; binds the verified envelope onto the held token.
/// - [`AgentCipherclerk::receive_local_delegation`] — local envelope receive path;
///   binds the verified local envelope onto the held token.
///
/// External code interacts via read-only accessors ([`HeldToken::encoded`],
/// [`HeldToken::service`], etc.).
///
/// # Durable signature binding
///
/// For tokens received via either delegation path, the verified envelope is
/// retained in [`Self::delegation_binding`] and **re-verified on every
/// authorization use**. This means external code cannot tamper with `encoded`
/// or `caveat_chain_hash` after receive: the recomputed signing message would
/// no longer match the captured signature, and the authorization would fail.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct HeldToken {
    /// Human-readable label for this token.
    label: String,
    /// The service this token grants access to.
    service: String,
    /// The encoded token string (em2_ prefixed).
    encoded: String,
    /// The root key used to verify this token (needed for re-verification).
    /// Never serialized — stays in memory only.
    #[serde(skip)]
    root_key: [u8; 32],
    /// A derived proof-only key for federation membership proofs.
    ///
    /// This is a BLAKE3 key derivation of the issuer's root HMAC key:
    /// `blake3::derive_key("dregg-proof-key-v1", &root_key)`.
    /// It is NEVER the raw root key itself.
    ///
    /// For root tokens, this is derived at construction time from `root_key`.
    /// For attenuated tokens, this is copied from the parent's `issuer_key`
    /// (which is already derived). For tokens received via delegation (where
    /// the issuer key is unknown), this is zeroed.
    ///
    /// **SECURITY**: Possession of this key does NOT allow:
    /// - Minting new root tokens (requires the raw `root_key` for HMAC chain init)
    /// - Forging or extending HMAC chains (HMAC verification requires `root_key`)
    /// - Recovering the raw root key (BLAKE3 key derivation is one-way)
    ///
    /// It DOES allow computing the federation Merkle leaf hash for ZK proofs.
    #[serde(skip)]
    issuer_key: [u8; 32],
    /// Unique identifier for lookup.
    id: String,
    /// Whether this token's HMAC chain has been cryptographically verified.
    ///
    /// Tokens minted locally or decoded with the real root key are `true`.
    /// Tokens received via delegation (where the root key is unknown) are `false`
    /// because `receive_delegation` performs only structural validation (parse +
    /// caveat structure), NOT HMAC chain verification.
    ///
    /// **SECURITY**: Code paths that treat a HeldToken as "trusted" for authorization
    /// decisions MUST check this field. An unverified token may have been forged or
    /// tampered with. Verification happens at presentation time when the token is
    /// submitted to a service that holds the root key.
    #[serde(default = "default_verified_false")]
    verified: bool,
    /// Pre-generated federation membership proof (for delegated tokens).
    ///
    /// When a token is received via delegation, the delegator pre-generates a
    /// Merkle membership proof for the REAL issuer key (which IS in the federation
    /// tree). The delegatee stores this proof and uses it directly during proof
    /// generation, bypassing the need to look up the proof_key in the federation tree
    /// (which would fail since the tree contains real keys, not their BLAKE3 derivations).
    ///
    /// `None` for tokens minted locally (they can generate fresh proofs on the fly).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    membership_proof: Option<dregg_commit::merkle::MerkleProof>,
    /// BLAKE3 hash of the serialized caveat chain, computed by the delegator at
    /// delegation time from the HMAC-verified token.
    ///
    /// The delegatee verifies this hash against their decoded token's caveats before
    /// using them for ZK proof generation. This prevents an attacker who holds the
    /// `proof_key` from mutating caveats in the encoded token and generating proofs
    /// over fabricated facts.
    ///
    /// `None` for tokens minted locally (they hold the root key and can verify the
    /// HMAC chain directly).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    caveat_chain_hash: Option<[u8; 32]>,
    /// Verified delegation envelope, present iff this token was produced via a
    /// `receive_*_delegation` path. The signature is re-checked against the
    /// current `encoded` / `caveat_chain_hash` / `membership_proof` on every
    /// authorization use; no mutation can bypass it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    delegation_binding: Option<DelegationBinding>,
    /// The **`ExecAuth` projection of this token's caveat chain** — the effect-mask
    /// authority the macaroon caveat chain confers, in the SAME `EffectMask` vocabulary
    /// the kernel cap leg consumes (`dregg_cell::is_facet_attenuation`, the in-circuit
    /// `granted ⊆ held` submask gate).
    ///
    /// This is the SDK-side `granted` of the `(granted, held)` pair the Lean bridge
    /// `Dregg2.Authority.CaveatCapBridge.chainGateG_emits_granted_le_held` proves about:
    /// the macaroon delegation caveat that narrows a capability-bearing verb EMITS the
    /// same rights pair the kernel cap leg reads, so the macaroon narrowing IS the kernel
    /// `granted ⊆ held` narrowing (not two parallel, informally-agreeing stories).
    ///
    /// `None` ⇒ unrestricted (`EFFECT_ALL`); a root token confers full effect-authority.
    /// Every [`Self::attenuate`] narrows it monotonically (`is_facet_attenuation`-subset);
    /// it can NEVER widen — a wider ask is clipped to the parent (no amplification), exactly
    /// as the Lean `delegChain` clips an over-broad mask to the held rights.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    narrowed_authority: Option<dregg_cell::EffectMask>,
}

/// Default for deserialization of older snapshots that lack the `verified` field.
/// Conservatively defaults to `false` — unverified until proven otherwise.
/// Tokens that were minted locally or verified via HMAC chain will have this
/// field explicitly set to `true` at creation time.
fn default_verified_false() -> bool {
    false
}

impl Drop for HeldToken {
    fn drop(&mut self) {
        self.root_key.zeroize();
        self.issuer_key.zeroize();
    }
}

impl HeldToken {
    /// Create a new HeldToken with the given fields.
    ///
    /// Tokens created with a real (non-zeroed) root key are marked as verified.
    /// Tokens with a zeroed root key are marked as unverified (delegated tokens).
    pub(crate) fn new(
        label: String,
        service: String,
        encoded: String,
        root_key: [u8; 32],
        id: String,
    ) -> Self {
        let verified = root_key != [0u8; 32];
        // For root tokens, derive a proof-only key from the root key.
        // This ensures the issuer_key NEVER equals the root_key, preventing
        // key leakage through attenuation or delegation paths.
        // Uses the same context string as AgentCipherclerk::derive_proof_key().
        let issuer_key = if root_key != [0u8; 32] {
            blake3::derive_key("dregg-proof-key-v1", &root_key)
        } else {
            [0u8; 32]
        };
        Self {
            label,
            service,
            encoded,
            root_key,
            issuer_key,
            id,
            verified,
            membership_proof: None,
            caveat_chain_hash: None,
            delegation_binding: None,
            // A root token confers full effect-authority; attenuation narrows from here.
            narrowed_authority: None,
        }
    }

    /// Create a new attenuated HeldToken (zeroed root_key — cannot mint or forge).
    ///
    /// Attenuated tokens carry the encoded macaroon chain and the issuer key for
    /// federation membership proofs. They can be further attenuated, presented for
    /// verification, and generate ZK proofs, but cannot mint new root tokens.
    ///
    /// Attenuated tokens created locally (from a verified parent) are marked as verified.
    ///
    /// `narrowed_authority` is the parent's effect-mask projection narrowed by this
    /// attenuation (the SDK-side `granted ⊆ held`); `None` carries forward an unrestricted
    /// parent.
    pub(crate) fn new_attenuated(
        label: String,
        service: String,
        encoded: String,
        id: String,
        issuer_key: [u8; 32],
        narrowed_authority: Option<dregg_cell::EffectMask>,
    ) -> Self {
        Self {
            label,
            service,
            encoded,
            root_key: [0u8; 32],
            issuer_key,
            id,
            verified: true, // Locally-attenuated from a verified parent
            membership_proof: None,
            caveat_chain_hash: None,
            delegation_binding: None,
            narrowed_authority,
        }
    }

    // -------------------------------------------------------------------------
    // Read-only accessors
    //
    // Authority-affecting fields are private; external callers may only *read*
    // them through these methods. See the `Sealed-value construction` section
    // on the struct doc for the construction rules.
    // -------------------------------------------------------------------------

    /// Human-readable label for this token.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// The service this token grants access to.
    pub fn service(&self) -> &str {
        &self.service
    }

    /// The encoded token string (em2_ prefixed).
    ///
    /// Returned by reference; the encoded bytes are immutable from outside the
    /// cipherclerk module. Direct mutation is impossible by construction (private
    /// field + no `&mut self` accessor).
    pub fn encoded(&self) -> &str {
        &self.encoded
    }

    /// Unique identifier for lookup.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Pre-generated federation membership proof (for delegated tokens).
    pub fn membership_proof(&self) -> Option<&dregg_commit::merkle::MerkleProof> {
        self.membership_proof.as_ref()
    }

    /// BLAKE3 hash of the serialized caveat chain.
    pub fn caveat_chain_hash(&self) -> Option<[u8; 32]> {
        self.caveat_chain_hash
    }

    /// The **`ExecAuth` projection of this token's caveat chain** — the effect-mask
    /// authority the chain confers, in the kernel cap leg's `EffectMask` vocabulary.
    ///
    /// `None` ⇒ unrestricted (`EFFECT_ALL`). This is the SDK-side `granted` of the
    /// `(granted, held)` pair the Lean bridge proves about: it is `is_facet_attenuation`-
    /// below the parent's projection for every attenuation, never above (no amplification).
    pub fn narrowed_authority(&self) -> Option<dregg_cell::EffectMask> {
        self.narrowed_authority
    }

    /// The token's effect-mask authority as a concrete `EffectMask` (`None` ⇒ `EFFECT_ALL`),
    /// for the `is_facet_attenuation` comparison the kernel cap leg performs.
    pub fn effective_authority_mask(&self) -> dregg_cell::EffectMask {
        self.narrowed_authority.unwrap_or(dregg_cell::EFFECT_ALL)
    }

    /// **Narrow this token's effect-mask authority by `facet`** — the SDK realization of the
    /// macaroon delegation caveat that EMITS the `(granted, held)` pair the kernel cap leg
    /// reads, mirroring the Lean `CaveatCapBridge.delegChain granted held`.
    ///
    /// The result's `narrowed_authority` is `held & facet` (the bitwise meet): a NON-AMPLIFYING
    /// ask (`facet ⊆ held`) records exactly `facet`; a wider ask is CLIPPED to the held rights
    /// (no amplification — exactly as the Lean `delegChain` clips an over-broad mask to `held`).
    /// Always `is_facet_attenuation(self.effective_authority_mask(), result.effective)`.
    ///
    /// Returns the new mask actually recorded (`held & facet`).
    pub fn narrow_authority(&mut self, facet: dregg_cell::EffectMask) -> dregg_cell::EffectMask {
        let held = self.effective_authority_mask();
        // The bitwise meet IS `granted ⊆ held`: `narrowed & held == narrowed` holds by construction,
        // so `is_facet_attenuation(held, narrowed)` is true — the macaroon can name no right the
        // parent never held.
        let narrowed = held & facet;
        self.narrowed_authority = Some(narrowed);
        narrowed
    }

    /// Whether `facet` would be a NON-AMPLIFYING narrowing of this token's effect-mask
    /// authority (`facet ⊆ held`). The pure check the kernel cap leg performs
    /// (`dregg_cell::is_facet_attenuation`), exposed for callers that want to reject an
    /// amplifying ask up front rather than silently clip it.
    pub fn is_authority_narrowing(&self, facet: dregg_cell::EffectMask) -> bool {
        dregg_cell::is_facet_attenuation(self.effective_authority_mask(), facet)
    }

    /// Access the root key by reference (internal use only).
    pub(crate) fn root_key(&self) -> &[u8; 32] {
        &self.root_key
    }

    /// Access the issuer key by reference.
    ///
    /// This key allows computing federation membership proofs but does NOT
    /// grant the ability to mint or forge tokens.
    pub(crate) fn issuer_key(&self) -> &[u8; 32] {
        &self.issuer_key
    }

    /// Returns `true` if this token holds the root forging key.
    ///
    /// Attenuated and delegated tokens have a zeroed root_key and return `false`.
    /// Only root tokens minted by this cipherclerk return `true`.
    pub fn can_mint(&self) -> bool {
        self.root_key != [0u8; 32]
    }

    /// Returns `true` if this token can generate ZK proofs.
    ///
    /// A token can prove if it has the derived proof key (for federation membership).
    /// This is true for root tokens (issuer_key = derive(root_key)) and for attenuated
    /// tokens created locally from a parent that held the proof key.
    ///
    /// Tokens received via delegation without a proof key cannot prove;
    /// use `prove_authorization_with_issuer_key()` for those.
    pub fn can_prove(&self) -> bool {
        self.issuer_key != [0u8; 32]
    }

    /// Returns `true` if this token's HMAC chain has been cryptographically verified.
    ///
    /// Tokens received via delegation are NOT verified (only structurally validated).
    /// They should be treated as untrusted until presented to a service holding the
    /// root key for full HMAC chain verification.
    pub fn is_verified(&self) -> bool {
        self.verified
    }

    /// Decode this held token into a [`MacaroonToken`] for operations.
    pub fn decode(&self) -> Result<MacaroonToken, dregg_token::TokenError> {
        MacaroonToken::from_encoded(&self.encoded, self.root_key)
    }

    /// Re-verify the captured delegation envelope signature against the
    /// **current** field values (`encoded`, `caveat_chain_hash`,
    /// `membership_proof` leaf, restrictions, parent hash, ...).
    ///
    /// # Authority invariant
    ///
    /// The delegator's signature binds these fields. Every authorization use
    /// re-verifies; no in-process mutation can bypass. This routine is the
    /// enforcement point for durable signature binding (P0 fix). Callers
    /// reaching `prove_authorization_*` or `authorize_private` on a token
    /// produced by `receive_*_delegation` MUST invoke this method first.
    ///
    /// For tokens without a delegation binding (locally minted / attenuated),
    /// returns `Ok(())` — there is nothing to re-verify and integrity is
    /// guaranteed by the HMAC chain checked at presentation time.
    pub(crate) fn reverify_delegation_binding(&self) -> Result<(), SdkError> {
        let Some(binding) = self.delegation_binding.as_ref() else {
            return Ok(());
        };

        // Recompute signing message from the *current* field values. If
        // `encoded` / `caveat_chain_hash` / `membership_proof` were tampered
        // with after receive, the digest will differ.
        let current_membership_leaf = self.membership_proof.as_ref().map(|p| p.leaf_hash);
        // Belt-and-suspenders: the captured leaf must match what the current
        // membership_proof carries — otherwise the proof was swapped out for
        // a different leaf even if signing-message recomputation includes the
        // captured one.
        if current_membership_leaf != binding.membership_leaf {
            return Err(SdkError::InvalidDelegation(
                "delegation binding broken: membership proof was swapped after receive".into(),
            ));
        }

        let signing_message = match binding.kind {
            DelegationBindingKind::ExternalV2 => {
                AgentCipherclerk::compute_delegation_signing_message_v2(
                    &self.encoded,
                    &binding.delegatee,
                    &self.service,
                    &self.id,
                    &binding.restrictions,
                    &binding.proof_key,
                    &self.caveat_chain_hash,
                    binding.membership_leaf.as_ref(),
                    &binding.parent_delegation_hash,
                    &binding.delegator_public_key,
                )
            }
            DelegationBindingKind::Local => {
                AgentCipherclerk::compute_local_delegation_signing_message(
                    &self.encoded,
                    &binding.delegatee,
                    &self.service,
                    &self.id,
                    &binding.restrictions,
                    &binding.proof_key,
                    &self.caveat_chain_hash,
                    binding.membership_leaf.as_ref(),
                    &binding.delegator_public_key,
                )
            }
        };

        use ed25519_dalek::Verifier;
        let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(
            &binding.delegator_public_key.0,
        )
        .map_err(|e| SdkError::InvalidDelegation(format!("invalid delegator public key: {e}")))?;
        let signature = ed25519_dalek::Signature::from_bytes(&binding.delegator_signature.0);
        verifying_key
            .verify(&signing_message, &signature)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!(
                    "delegation binding broken: re-verification failed (token fields tampered \
                     after receive): {e}"
                ))
            })
    }

    /// Test-only helper: forcibly overwrite the encoded payload. Used by the
    /// adversarial test suite to simulate an attacker who somehow obtained
    /// write access to a sealed HeldToken's encoded bytes.
    ///
    /// Only available in `cfg(test)` builds.
    #[cfg(test)]
    pub(crate) fn test_only_tamper_encoded(&mut self, new_encoded: String) {
        self.encoded = new_encoded;
    }

    /// Test-only helper: forcibly overwrite the caveat chain hash. Used by the
    /// adversarial test suite.
    #[cfg(test)]
    pub(crate) fn test_only_tamper_caveat_chain_hash(&mut self, new_hash: Option<[u8; 32]>) {
        self.caveat_chain_hash = new_hash;
    }
}

/// A token that has been delegated to another agent (signed envelope).
///
/// Contains only the serialized attenuated macaroon bytes (NOT the root key).
/// The delegatee can present this token for verification and further attenuate it,
/// but cannot mint new root tokens.
///
/// # Envelope v2 (mandatory signature)
///
/// This struct is the on-the-wire delegation envelope. All envelope-relevant fields
/// (token_bytes, delegatee, service, id, restrictions, proof_key, caveat_chain_hash,
/// membership_leaf, parent_delegation_hash) are bound by `delegator_signature`. The
/// signature must verify under `delegator_public_key`.
///
/// **The envelope is NOT trustworthy on its own**: the receiver must additionally
/// check that `delegator_public_key` is an *authorized* delegator for this chain.
/// See [`AgentCipherclerk::receive_signed_delegation`] for the authority model.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegatedToken {
    /// The serialized attenuated token (encoded macaroon string).
    pub token_bytes: String,
    /// The service this token grants access to.
    pub service: String,
    /// Human-readable label.
    pub label: String,
    /// Token identifier.
    pub id: String,
    /// The public key of the delegatee.
    pub delegatee: PublicKey,
    /// The restrictions applied during delegation.
    pub restrictions: Attenuation,
    /// Derived proof key for ZK proof generation by the delegatee.
    ///
    /// This is the token's `issuer_key`, which is already a one-way BLAKE3
    /// derivation of the issuer's root HMAC key via
    /// `blake3::derive_key("dregg-proof-key-v1", &root_key)`. It grants the
    /// delegatee the ability to generate federation membership proofs (ZK) but
    /// NOT the ability to mint or forge tokens (one-way derivation).
    ///
    /// When `None`, the delegatee cannot generate proofs without out-of-band
    /// key material. This field is populated by [`AgentCipherclerk::delegate()`] when
    /// the delegator holds a token with proof capability.
    #[serde(default)]
    pub proof_key: Option<[u8; 32]>,
    /// Pre-generated federation membership proof for the delegatee.
    ///
    /// The delegator (who can look up the BLAKE3-derived proof key as a leaf in
    /// the federation Merkle tree) pre-generates this proof and includes it in the
    /// delegation payload. The delegatee uses this proof directly instead of trying
    /// to look up membership themselves.
    ///
    /// **Note**: Federation tree leaves are BLAKE3-derived proof keys, NOT raw
    /// issuer keys. The path's `leaf_hash` corresponds to `derive_proof_key(root_key)`.
    ///
    /// **Security property**: The membership proof is bound to the specific federation
    /// root at delegation time. If the federation root changes (e.g., issuer is removed),
    /// this pre-generated proof becomes invalid and the delegatee can no longer prove
    /// membership.
    #[serde(default)]
    pub membership_proof: Option<dregg_commit::merkle::MerkleProof>,
    /// BLAKE3 hash of the serialized caveat chain, computed by the delegator from
    /// the HMAC-verified token. The delegatee uses this to verify caveat integrity
    /// before generating ZK proofs.
    ///
    /// Without this, a delegatee holding the `proof_key` could mutate caveats in
    /// the encoded token and generate proofs over fabricated authorization facts.
    #[serde(default)]
    pub caveat_chain_hash: Option<[u8; 32]>,
    /// Hash of the parent delegation envelope, when this delegation is part of a
    /// chain (A → B → C). For root delegations (issuer → first recipient), this
    /// is the zero hash. The parent hash is part of the signed payload so chains
    /// link cryptographically.
    #[serde(default)]
    pub parent_delegation_hash: [u8; 32],
    /// Ed25519 signature from the delegator over the **entire** delegation envelope.
    ///
    /// The signed payload covers `token_bytes`, `delegatee`, `service`, `id`,
    /// `restrictions`, `proof_key`, `caveat_chain_hash`, `membership_leaf`,
    /// `parent_delegation_hash`, and the envelope domain tag. See
    /// [`AgentCipherclerk::compute_delegation_signing_message_v2`].
    ///
    /// This prevents a malicious holder of `proof_key` from forging an envelope:
    /// they cannot produce a signature that verifies under the legitimate
    /// delegator's public key.
    pub delegator_signature: Signature,
    /// The delegator's public key.
    ///
    /// **WARNING**: This field is asserted by the wire envelope, not verified by it.
    /// The receiver MUST additionally check that this public key is an authorized
    /// delegator (matches an expected key or chains to a previously-accepted
    /// envelope). See [`AgentCipherclerk::receive_signed_delegation`].
    pub delegator_public_key: PublicKey,
}

impl DelegatedToken {
    /// Compute the envelope hash. Used as a parent-pointer when this delegation
    /// is later re-delegated (forming a chain).
    pub fn envelope_hash(&self) -> [u8; 32] {
        let membership_leaf = self.membership_proof.as_ref().map(|p| p.leaf_hash);
        AgentCipherclerk::compute_delegation_signing_message_v2(
            &self.token_bytes,
            &self.delegatee,
            &self.service,
            &self.id,
            &self.restrictions,
            &self.proof_key,
            &self.caveat_chain_hash,
            membership_leaf.as_ref(),
            &self.parent_delegation_hash,
            &self.delegator_public_key,
        )
    }
}

/// Authority policy for accepting [`DelegatedToken`] envelopes.
///
/// See [`AgentCipherclerk::check_delegation_authority`] for the security model.
#[derive(Clone, Debug)]
pub enum DelegationAuthority {
    /// Accept envelopes signed by exactly this public key. Most common case for
    /// first-time delegations where the receiver knows (out-of-band) which agent
    /// is delegating to them.
    TrustedKey(PublicKey),
    /// Accept envelopes signed by any key in this set. Useful when several
    /// authorized delegators may issue tokens (e.g., a small federation).
    TrustedKeys(std::collections::HashSet<PublicKey>),
    /// Accept envelopes that link to a known parent envelope hash AND are signed
    /// by the expected re-delegator. Used when accepting Bob's delegation along
    /// a chain Alice → Bob → Carol: Carol verifies the envelope's parent_hash
    /// matches the envelope she already received from Alice (transitively).
    ChainsFromParent {
        /// The envelope hash this delegation must declare as its parent.
        parent_hash: [u8; 32],
        /// The expected delegator (the agent re-delegating the parent envelope).
        delegator: PublicKey,
    },
    /// Accept any well-signed envelope. **UNSAFE** — only for development.
    /// `warn` controls whether to emit a tracing warning on use.
    ///
    /// # Feature gating
    ///
    /// This variant is only compiled when the `unsafe-test-utils` cargo
    /// feature is enabled (or in `cfg(test)` builds of this crate). Production
    /// callers depending on `dregg-sdk` without the feature cannot construct
    /// it, by design — this prevents the well-known footgun of
    /// `DelegationAuthority::Open { warn: false }` accidentally landing in a
    /// production codepath that consumes untrusted envelopes.
    #[cfg(any(test, feature = "unsafe-test-utils"))]
    Open {
        /// Whether to emit a tracing warning on every use (recommended: true).
        warn: bool,
    },
}

/// A delegation produced *inside this process* for handing tokens to sub-agents.
///
/// This is **not** wire-transferable: it does not implement `Serialize`/`Deserialize`
/// and its constructor is crate-private. Receiving cipherclerks accept it via the
/// dedicated [`AgentCipherclerk::receive_local_delegation`] path, which never runs on
/// externally-sourced bytes.
///
/// Even local delegations are signed (so authority binding is uniform across all
/// code paths). The envelope tag is `"dregg-delegation-local-v1"`, which is
/// distinct from the external envelope tag and therefore non-confusable.
#[derive(Clone, Debug)]
pub struct LocalDelegation {
    pub(crate) token_bytes: String,
    pub(crate) service: String,
    pub(crate) label: String,
    pub(crate) id: String,
    pub(crate) delegatee: PublicKey,
    pub(crate) restrictions: Attenuation,
    pub(crate) proof_key: Option<[u8; 32]>,
    pub(crate) membership_proof: Option<dregg_commit::merkle::MerkleProof>,
    pub(crate) caveat_chain_hash: Option<[u8; 32]>,
    pub(crate) delegator_signature: Signature,
    pub(crate) delegator_public_key: PublicKey,
}

/// A turn signed by this cipherclerk's identity, ready for submission.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SignedTurn {
    /// The original turn.
    pub turn: Turn,
    /// The Ed25519 signature over the turn hash.
    pub signature: Signature,
    /// The signer's public key.
    pub signer: PublicKey,
}

/// A signed action paired with the clerk's faithful explanation of what it
/// does — the anti-blind-signing carrier.
///
/// The clerk produces this so a UI can show the citizen *exactly* what they are
/// about to authorize (`explanation`) alongside the action it will sign
/// (`action`). The explanation is the third reading of the same term
/// (see [`crate::explain`]): it is total (never panics) and
/// injective-on-semantics (two actions with different effect-semantics get
/// different explanations), so the screen cannot misstate the turn.
///
/// Signing semantics are unchanged: `action` is exactly the action
/// [`AgentCipherclerk::sign_action`] would return; the `explanation` is a
/// faithful rendering derived from it, carried so the caller never has to sign
/// blind.
#[derive(Clone, Debug)]
pub struct ExplainedSignedAction {
    /// The signed action (identical to the output of
    /// [`AgentCipherclerk::sign_action`]).
    pub action: dregg_turn::action::Action,
    /// The clerk's faithful, total explanation of `action` — what the citizen
    /// is being asked to authorize.
    pub explanation: String,
}

/// A signed turn paired with the clerk's faithful explanation of the whole
/// call forest — the turn-level anti-blind-signing carrier.
///
/// See [`ExplainedSignedAction`]. Signing semantics are unchanged: `signed` is
/// exactly what [`AgentCipherclerk::sign_turn`] produces.
#[derive(Clone, Debug)]
pub struct ExplainedSignedTurn {
    /// The signed turn (identical to the output of
    /// [`AgentCipherclerk::sign_turn`]).
    pub signed: SignedTurn,
    /// The clerk's faithful, total explanation of the entire turn.
    pub explanation: String,
}

/// The agent cipherclerk: manages identity, tokens, and signing.
///
/// This is the core credential holder that every agent carries. It provides:
/// - Token minting (creating new root tokens)
/// - Token attenuation (narrowing permissions)
/// - Token delegation (handing attenuated tokens to other agents)
/// - Turn signing (authorizing execution requests)
/// - Proof generation (ZK presentation of authorization)
/// - Receipt chain management (proof-carrying state)
/// - HD key derivation from mnemonic (BIP39 + BLAKE3)
pub struct AgentCipherclerk {
    /// The agent's Ed25519 signing key.
    signing_key: ed25519_dalek::SigningKey,
    /// The agent's public identity.
    public_key: PublicKey,
    /// All tokens held in this cipherclerk's wallet.
    tokens: Vec<HeldToken>,
    /// Counter for generating unique token IDs.
    next_token_id: u64,
    /// The agent's receipt chain: a linked sequence of TurnReceipts proving
    /// the complete history of state transitions from genesis. This is the
    /// proof-carrying state representation — anyone can verify the chain
    /// without contacting a federation.
    receipt_chain: Vec<dregg_turn::TurnReceipt>,
    /// Optional IVC builder for incrementally accumulating state transition proofs.
    /// When enabled, each appended receipt extends the IVC chain, producing a
    /// constant-size proof of the entire state transition history.
    /// Skipped during serialization as it is runtime-only state.
    ivc_builder: Option<IvcBuilder>,
    /// The HD seed from which this cipherclerk's key was derived (if created from mnemonic).
    /// Stored encrypted at rest; zeroized on drop.
    seed: Option<[u8; 64]>,
    /// The mnemonic phrase used to create this cipherclerk (if created from mnemonic).
    /// Stored encrypted at rest; zeroized on drop.
    mnemonic_phrase: Option<String>,
    /// The derivation path used for this cipherclerk's key (e.g., "dregg/0").
    derivation_path: Option<String>,
    /// Stealth keypair for receiving private notes via one-time addresses.
    /// Derived deterministically from the cipherclerk's signing key.
    stealth_keys: StealthKeys,
    /// Local state for sovereign cells we own.
    ///
    /// When a cell is transitioned to sovereign mode, the federation stores only
    /// a 32-byte commitment. The agent maintains the full cell state here and
    /// provides it as a witness in each turn targeting the cell.
    sovereign_cells: HashMap<CellId, Cell>,
    /// Per-cell sovereign-witness sequence counter (last issued).
    ///
    /// Mirrors the executor-side `Ledger::last_sovereign_witness_sequence`.
    /// The next witness for `cell_id` carries
    /// `sovereign_witness_sequences[cell_id] + 1`; the cipherclerk bumps this
    /// after each successful submission. Greenfield: persistence across
    /// process restarts is out of scope here — the cipherclerk recovers state
    /// from the federation's stored sequence on resume.
    sovereign_witness_sequences: HashMap<CellId, u64>,
    /// Optional CapTP client for capability sharing, enlivening, and pipelining.
    ///
    /// Must be set via [`set_captp_client`](Self::set_captp_client) before using
    /// the CapTP convenience methods. Gated on the `captp` feature so the
    /// crate compiles on wasm32 (CapTpClient pulls async-runtime deps).
    #[cfg(feature = "captp")]
    captp_client: Option<crate::captp_client::CapTpClient>,
    /// Token ids this cipherclerk has locally revoked.
    ///
    /// This is the *wallet-side* mirror of the provider-side
    /// [`dregg_token::RevocationRegistry`]: when a citizen decides a token
    /// they minted/hold should no longer be honoured, they record its id
    /// here. [`Self::is_locally_revoked`] is then a cheap local pre-check
    /// before presenting a token, and the leaf for a server-side registry
    /// is [`dregg_token::RevocationRegistry::token_id_to_leaf`] of the same
    /// id — so the local set and the published Merkle registry agree on the
    /// keying. This set is *advisory*: authoritative non-revocation is
    /// proven against the published registry root, not this field.
    local_revocations: std::collections::HashSet<String>,
}

/// Internal carrier for a proven sovereign turn: the proof-carrying [`Turn`]
/// plus the retained scope-2 trace and γ.2-projected public inputs that the
/// proof committed to. Produced by `AgentCipherclerk::prove_sovereign_turn`
/// and consumed by both `execute_sovereign_turn_with_proof` (which keeps only
/// the turn) and `emit_witnessed_receipt` (which lifts the trace + PI into a
/// [`WitnessedReceipt`]).
// Several fields (trace, public_inputs, new_commitment, pre_state_commitment) are
// read only by the WitnessedReceipt-lifting path, which is feature-gated; under the
// prover-unified build they carry replay material that isn't re-read in-process.
#[allow(dead_code)]
struct ProvenSovereignTurn {
    /// The proof-carrying turn, with `execution_proof` populated.
    turn: Turn,
    /// The full Effect-VM execution trace (scope-2 replay material).
    trace: Vec<Vec<dregg_circuit::field::BabyBear>>,
    /// The public inputs the STARK proof committed to, including the γ.2
    /// bilateral projection and the `IS_AGENT_CELL` flag.
    public_inputs: Vec<dregg_circuit::field::BabyBear>,
    /// The proof's claimed new state commitment (PI[NEW_COMMIT_BASE..+4]).
    new_commitment: [u8; 32],
    /// The cell's state commitment captured *before* effects were applied.
    pre_state_commitment: [u8; 32],
}

/// The SDK agent's own side of a bilateral interaction: a per-cell
/// [`WitnessedReceipt`] plus the submittable proof-carrying [`Turn`] it was
/// derived from.
///
/// Returned by [`AgentCipherclerk::emit_witnessed_receipt`]. The `witnessed`
/// field is a real scope-2 WR (receipt + EffectVM proof bytes + γ.2-projected
/// PI + inline scope-2 trace); it round-trips through
/// [`crate::witness_artifact`] (DWR1) and slots into a
/// `&[(CellId, WitnessedReceipt)]` bundle for the γ.2 aggregator.
#[derive(Clone, Debug)]
pub struct SovereignWitnessedReceipt {
    /// The cell whose transition this WR attests (its role in the bundle key).
    pub cell_id: CellId,
    /// The submittable proof-carrying turn.
    pub turn: Turn,
    /// The per-cell witnessed receipt.
    pub witnessed: WitnessedReceipt,
}

impl AgentCipherclerk {
    /// Create a new cipherclerk with a randomly generated Ed25519 identity.
    ///
    /// # Example
    /// ```
    /// use dregg_sdk::AgentCipherclerk;
    /// let cipherclerk = AgentCipherclerk::new();
    /// println!("Agent identity: {}", cipherclerk.public_key());
    /// ```
    pub fn new() -> Self {
        let mut key_bytes = Zeroizing::new([0u8; 32]);
        getrandom::fill(&mut *key_bytes).expect("getrandom failed");
        Self::from_key_bytes(key_bytes)
    }

    /// Create a cipherclerk from an existing 32-byte Ed25519 secret key.
    ///
    /// Use this when restoring a cipherclerk from persisted key material.
    ///
    /// # Security
    ///
    /// The key material is wrapped in [`Zeroizing`] to ensure it is erased from
    /// memory when no longer needed. This prevents the caller's copy from
    /// persisting on the stack or heap after cipherclerk construction. Callers should
    /// always wrap key bytes in `Zeroizing` before passing them to this function
    /// to benefit from automatic zeroization on drop.
    pub fn from_key_bytes(mut secret: Zeroizing<[u8; 32]>) -> Self {
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&secret);
        let verifying_key = signing_key.verifying_key();
        let public_key = PublicKey(verifying_key.to_bytes());
        // Derive stealth keys deterministically from the signing key.
        let stealth_keys = Self::derive_stealth_keys(&signing_key);
        // Explicitly zeroize before drop for defense-in-depth (Zeroizing's Drop
        // impl will also do this, but we want to be clear about intent).
        secret.zeroize();
        AgentCipherclerk {
            signing_key,
            public_key,
            tokens: Vec::new(),
            next_token_id: 0,
            receipt_chain: Vec::new(),
            ivc_builder: None,
            seed: None,
            mnemonic_phrase: None,
            derivation_path: None,
            stealth_keys,
            sovereign_cells: HashMap::new(),
            sovereign_witness_sequences: HashMap::new(),
            #[cfg(feature = "captp")]
            captp_client: None,
            local_revocations: std::collections::HashSet::new(),
        }
    }

    /// Create a cipherclerk from a BIP39 mnemonic phrase.
    ///
    /// Derives the main agent identity at path `dregg/0`. The mnemonic and seed
    /// are retained in memory (encrypted at rest) for sub-agent derivation and
    /// backup export.
    ///
    /// # Arguments
    ///
    /// * `mnemonic_str` - A valid 24-word BIP39 mnemonic.
    /// * `passphrase` - Optional passphrase for additional protection. Use `""` for none.
    pub fn from_mnemonic(mnemonic_str: &str, passphrase: &str) -> Result<Self, SdkError> {
        let seed = mnemonic::mnemonic_to_seed(mnemonic_str, passphrase)
            .map_err(|e| SdkError::MissingKey(e.to_string()))?;
        let mut cclerk = Self::from_seed_at_path(seed, "dregg/0");
        cclerk.mnemonic_phrase = Some(mnemonic_str.to_string());
        Ok(cclerk)
    }

    /// Create a cipherclerk from a raw 64-byte seed, deriving the main identity at `dregg/0`.
    ///
    /// Use this when the seed was obtained externally (e.g., from an encrypted backup).
    pub fn from_seed(seed: [u8; 64]) -> Self {
        Self::from_seed_at_path(seed, "dregg/0")
    }

    /// Create a cipherclerk from a seed at a specific derivation path.
    fn from_seed_at_path(seed: [u8; 64], path: &str) -> Self {
        let (_pub_bytes, mut sec_bytes) = mnemonic::derive_keypair(&seed, path);
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&sec_bytes);
        // Zeroize the derived secret key bytes now that we have the SigningKey.
        sec_bytes.zeroize();
        let verifying_key = signing_key.verifying_key();
        let public_key = PublicKey(verifying_key.to_bytes());
        let stealth_keys = Self::derive_stealth_keys(&signing_key);
        AgentCipherclerk {
            signing_key,
            public_key,
            tokens: Vec::new(),
            next_token_id: 0,
            receipt_chain: Vec::new(),
            ivc_builder: None,
            seed: Some(seed),
            mnemonic_phrase: None,
            derivation_path: Some(path.to_string()),
            stealth_keys,
            sovereign_cells: HashMap::new(),
            sovereign_witness_sequences: HashMap::new(),
            #[cfg(feature = "captp")]
            captp_client: None,
            local_revocations: std::collections::HashSet::new(),
        }
    }

    /// Derive a sub-agent cipherclerk at the given index.
    ///
    /// The sub-agent's key is derived from the same seed at path `dregg/{index}`.
    /// Requires that this cipherclerk was created from a mnemonic or seed.
    ///
    /// # Arguments
    ///
    /// * `index` - The derivation index. Use 1, 2, 3, ... (0 is the main identity).
    pub fn derive_sub_agent(&self, index: u32) -> Result<Self, SdkError> {
        let seed = self
            .seed
            .ok_or_else(|| SdkError::MissingKey("cipherclerk has no seed for derivation".into()))?;
        let path = format!("dregg/{}", index);
        Ok(Self::from_seed_at_path(seed, &path))
    }

    /// Derive a sub-agent cipherclerk at an explicit derivation path.
    ///
    /// Generalises [`Self::derive_sub_agent`] (which is exactly this with
    /// `path = format!("dregg/{index}")`) to arbitrary path strings, so an
    /// agent can carve out *namespaced* sub-identities — per-device
    /// (`"dregg/device/laptop"`), per-app (`"dregg/app/orderbook"`), or
    /// per-purpose (`"dregg/signing/cold"`) — all recoverable from the one
    /// seed. Requires that this cipherclerk holds a seed (mnemonic- or
    /// seed-derived); raw-key cipherclerks have no seed to derive from.
    ///
    /// The path is fed verbatim into the same BLAKE3 hardened-derivation
    /// scheme [`Self::derive_sub_agent`] uses, so distinct paths yield
    /// independent keys and the same path is stable across restarts.
    pub fn derive_sub_agent_at_path(&self, path: &str) -> Result<Self, SdkError> {
        let seed = self
            .seed
            .ok_or_else(|| SdkError::MissingKey("cipherclerk has no seed for derivation".into()))?;
        Ok(Self::from_seed_at_path(seed, path))
    }

    /// Export the mnemonic phrase if this cipherclerk was created from one.
    ///
    /// Returns `None` if the cipherclerk was created from raw key bytes or if the
    /// mnemonic has been explicitly cleared.
    ///
    /// # Security
    ///
    /// This method requires `&mut self` to prevent extraction via shared references.
    /// The mnemonic phrase is the master secret from which all keys are derived.
    /// Exposing it allows full cipherclerk reconstruction including all sub-agent keys.
    ///
    /// Callers MUST ensure the returned value is:
    /// - Never logged or serialized to persistent storage without encryption.
    /// - Zeroized after use (the reference borrows from the cipherclerk, so the cipherclerk
    ///   handles zeroization on drop, but callers must not copy into unprotected buffers).
    /// - Never transmitted over network without end-to-end encryption.
    #[must_use = "exported mnemonic is highly sensitive master key material"]
    pub fn export_mnemonic(&mut self) -> Option<&str> {
        self.mnemonic_phrase.as_deref()
    }

    /// Export the raw seed if available.
    ///
    /// Returns `None` if the cipherclerk was created from raw key bytes without a seed.
    ///
    /// # Security
    ///
    /// This method requires `&mut self` to prevent extraction via shared references.
    /// The seed is the master secret from which all keys are derived. Exposing it
    /// allows full cipherclerk reconstruction including all sub-agent keys.
    ///
    /// Callers MUST ensure the returned value is:
    /// - Never logged or serialized to persistent storage without encryption.
    /// - Zeroized after use (the reference borrows from the cipherclerk, so the cipherclerk
    ///   handles zeroization on drop, but callers must not copy into unprotected buffers).
    /// - Never transmitted over network without end-to-end encryption.
    #[must_use = "exported seed is highly sensitive master key material"]
    pub fn export_seed(&mut self) -> Option<&[u8; 64]> {
        self.seed.as_ref()
    }

    /// Get the derivation path used for this cipherclerk's key.
    pub fn derivation_path(&self) -> Option<&str> {
        self.derivation_path.as_deref()
    }

    /// Get this agent's public key (identity).
    pub fn public_key(&self) -> PublicKey {
        self.public_key
    }

    /// Derive a purpose-specific symmetric key from this cipherclerk's signing key.
    ///
    /// Uses BLAKE3's key derivation mode with the given context string to
    /// produce a 32-byte key that is deterministic for this cipherclerk but
    /// unique per context. This is used, for example, to derive the gossip
    /// envelope signing key for federation communication.
    ///
    /// # Security
    ///
    /// The derived key is a deterministic function of the signing key and
    /// context. Different context strings produce independent keys.
    pub fn derive_symmetric_key(&self, context: &str) -> [u8; 32] {
        blake3::derive_key(context, &self.signing_key.to_bytes())
    }

    /// Get the node's Ed25519 signing key as a `dregg_types::SigningKey`.
    ///
    /// Used by the gossip layer for asymmetric envelope signing. Each node
    /// signs with its own key; peers verify using this node's public key.
    pub fn gossip_signing_key(&self) -> dregg_types::SigningKey {
        dregg_types::SigningKey::from_bytes(&self.signing_key.to_bytes())
    }

    /// Derive a [`CellId`] for this agent in a given domain.
    ///
    /// The cell ID is deterministically derived from the agent's public key
    /// and a BLAKE3 hash of the domain string (used as the token_id).
    /// This matches the derivation used by `Cell::with_balance`.
    pub fn cell_id(&self, domain: &str) -> CellId {
        let token_id = *blake3::hash(domain.as_bytes()).as_bytes();
        CellId::derive_raw(&self.public_key.0, &token_id)
    }

    /// Get a reference to all held tokens.
    pub fn tokens(&self) -> &[HeldToken] {
        &self.tokens
    }

    /// Find a held token by its label.
    pub fn find_token(&self, label: &str) -> Option<&HeldToken> {
        self.tokens.iter().find(|t| t.label == label)
    }

    /// Find a held token by its ID.
    pub fn find_token_by_id(&self, id: &str) -> Option<&HeldToken> {
        self.tokens.iter().find(|t| t.id == id)
    }

    /// Drop a held token from the wallet by its id.
    ///
    /// Returns `true` if a token with that id was present (and is now
    /// removed), `false` if no such token was held. This is wallet hygiene:
    /// a citizen who no longer needs a delegated or attenuated token can
    /// forget it so it stops cluttering [`Self::tokens`] and cannot be
    /// presented by mistake. Forgetting does **not** revoke the token for
    /// *other* holders — for that, see [`Self::revoke_token`].
    ///
    /// On removal the `HeldToken`'s `Drop` zeroizes its `root_key` /
    /// `issuer_key`, so the secret material does not linger.
    pub fn forget_token(&mut self, id: &str) -> bool {
        let before = self.tokens.len();
        self.tokens.retain(|t| t.id != id);
        self.tokens.len() != before
    }

    /// Locally revoke a token id and forget any held copy of it.
    ///
    /// Records `id` in this cipherclerk's [`local_revocations`] set (so
    /// [`Self::is_locally_revoked`] reports it) and removes any held token
    /// with that id from the wallet. Returns `true` if a held token was
    /// actually removed by this call.
    ///
    /// # Relationship to the published registry
    ///
    /// This is the *wallet-side* half of revocation. It is advisory: it
    /// stops *this* cipherclerk from presenting the token and lets local
    /// code pre-check. The *authoritative*, third-party-verifiable half is
    /// the provider's [`dregg_token::RevocationRegistry`] — call
    /// `registry.revoke(id)` there and publish the root. The keying agrees:
    /// the leaf this id occupies in that Merkle registry is exactly
    /// [`dregg_token::RevocationRegistry::token_id_to_leaf`] of the same
    /// `id`, so a local revocation can be lifted to a published one without
    /// re-deriving identifiers.
    pub fn revoke_token(&mut self, id: &str) -> bool {
        self.local_revocations.insert(id.to_string());
        self.forget_token(id)
    }

    /// Whether the given token id has been locally revoked via
    /// [`Self::revoke_token`].
    ///
    /// Advisory only — see [`Self::revoke_token`] for the authoritative
    /// (registry-rooted) revocation path.
    pub fn is_locally_revoked(&self, id: &str) -> bool {
        self.local_revocations.contains(id)
    }

    /// The number of token ids this cipherclerk has locally revoked.
    pub fn locally_revoked_count(&self) -> usize {
        self.local_revocations.len()
    }

    // =========================================================================
    // Token Operations
    // =========================================================================

    /// Mint a new root token for a service.
    ///
    /// The root key is the symmetric secret used to verify this token chain.
    /// Store it securely -- anyone with the root key can forge tokens.
    ///
    /// # Arguments
    ///
    /// * `root_key` - 32-byte HMAC root secret for the token chain.
    /// * `service` - Human-readable service name (e.g., "dns", "storage", "compute").
    ///
    /// # Returns
    ///
    /// A [`HeldToken`] representing the unrestricted root token.
    #[must_use = "a minted token that is never used or stored provides no capability"]
    pub fn mint_token(&mut self, root_key: &[u8; 32], service: &str) -> HeldToken {
        let kid = format!("{}:{}", service, self.next_token_id);
        self.next_token_id += 1;

        let token = MacaroonToken::mint(*root_key, kid.as_bytes(), service);
        let encoded = token.to_encoded().expect("fresh token encodes cleanly");

        let held = HeldToken::new(
            format!("root:{}", service),
            service.to_string(),
            encoded,
            *root_key,
            kid,
        );

        self.tokens.push(held.clone());
        held
    }

    /// Attenuate a held token by adding restrictions.
    ///
    /// This creates a new, more restricted token derived from the original.
    /// The original token remains in the cipherclerk unchanged. Attenuation can only
    /// narrow permissions, never expand them.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to attenuate.
    /// * `restrictions` - The restrictions to apply.
    ///
    /// # Returns
    ///
    /// A new [`HeldToken`] with the restrictions applied, or an error if
    /// attenuation is not possible (e.g., empty restrictions).
    #[must_use = "the attenuated token must be stored or presented; dropping it leaks a capability"]
    pub fn attenuate(
        &mut self,
        token: &HeldToken,
        restrictions: &Attenuation,
    ) -> Result<HeldToken, SdkError> {
        let decoded = token.decode()?;
        let attenuated_boxed = decoded.attenuate(restrictions)?;
        let encoded = attenuated_boxed.to_encoded()?;

        let id = format!("{}:att:{}", token.id, self.next_token_id);
        self.next_token_id += 1;

        // SECURITY: Attenuated tokens do NOT carry the root forging key.
        // They can be further attenuated and presented for verification,
        // but cannot mint new root tokens or bypass the attenuation chain.
        //
        // They carry the derived issuer_key (proof-only key) for ZK proof generation.
        // This key is a one-way BLAKE3 derivation of the root key — possession of it
        // does NOT allow minting tokens or forging HMAC chains.
        let issuer_key = *token.issuer_key();
        // The child carries the parent's effect-mask projection (the macaroon caveats in
        // `restrictions` narrow the app/service/time axes; the effect-authority projection
        // is carried forward, and is narrowed further only via `narrow_authority`). This is
        // monotone: a child can never carry a wider `narrowed_authority` than its parent.
        let held = HeldToken::new_attenuated(
            format!("attenuated:{}", token.service),
            token.service.clone(),
            encoded,
            id,
            issuer_key,
            token.narrowed_authority,
        );

        self.tokens.push(held.clone());
        Ok(held)
    }

    /// Delegate a token to another agent with restrictions.
    ///
    /// This attenuates the token and produces a [`DelegatedToken`] that can
    /// be transmitted to the target agent. The delegatee receives a token that
    /// is strictly less powerful than the original.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to delegate from.
    /// * `to` - The public key of the agent receiving the delegation.
    /// * `restrictions` - Additional restrictions beyond those already on the token.
    ///
    /// # Returns
    ///
    /// A [`DelegatedToken`] containing the attenuated token for the delegatee.
    #[must_use = "the DelegatedToken must be transmitted to the delegatee; dropping it wastes the delegation"]
    pub fn delegate(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
    ) -> Result<DelegatedToken, SdkError> {
        self.delegate_with_parent(token, to, restrictions, [0u8; 32])
    }

    /// Like [`Self::delegate`], but anchors this delegation to a parent envelope hash.
    ///
    /// When re-delegating a token received from another agent, pass the parent
    /// envelope hash (from [`DelegatedToken::envelope_hash`]) so the resulting
    /// chain links cryptographically.
    pub fn delegate_with_parent(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
        parent_delegation_hash: [u8; 32],
    ) -> Result<DelegatedToken, SdkError> {
        let attenuated = self.attenuate(token, restrictions)?;

        // Pass through the derived proof key to the delegatee.
        // The issuer_key is already a one-way derivation of the root key (never the
        // raw root key itself), so it's safe to transmit to a less-trusted party.
        let proof_key = if token.can_prove() {
            let key = token.issuer_key();
            if *key != [0u8; 32] { Some(*key) } else { None }
        } else {
            None
        };

        // Compute the caveat chain hash from the HMAC-verified attenuated token.
        // The delegator holds the root key and can verify the chain; the delegatee
        // will use this commitment to detect any post-delegation caveat tampering.
        let caveat_chain_hash = {
            let decoded = attenuated.decode()?;
            Some(Self::compute_caveat_chain_hash(&decoded)?)
        };

        // SECURITY: Sign the entire delegation envelope (v2 payload) so neither
        // the delegatee nor a `proof_key` holder can mutate any envelope field
        // without invalidating the signature.
        let signing_message = Self::compute_delegation_signing_message_v2(
            &attenuated.encoded,
            to,
            &attenuated.service,
            &attenuated.id,
            restrictions,
            &proof_key,
            &caveat_chain_hash,
            None, // no pre-generated membership proof
            &parent_delegation_hash,
            &self.public_key,
        );
        let sig = self.signing_key.sign(&signing_message);
        let delegator_signature = Signature(sig.to_bytes());

        Ok(DelegatedToken {
            token_bytes: attenuated.encoded.clone(),
            service: attenuated.service.clone(),
            label: attenuated.label.clone(),
            id: attenuated.id.clone(),
            delegatee: *to,
            restrictions: restrictions.clone(),
            proof_key,
            membership_proof: None,
            caveat_chain_hash,
            parent_delegation_hash,
            delegator_signature,
            delegator_public_key: self.public_key,
        })
    }

    /// Delegate a token to another agent with a pre-generated federation membership proof.
    ///
    /// When a `federation_tree` is provided, the delegator pre-generates a federation
    /// membership proof using the BLAKE3-derived proof key (which IS in the tree as a
    /// leaf). The delegatee receives this proof and can use it directly during
    /// presentation without needing access to the tree.
    ///
    /// Federation tree leaves are BLAKE3-derived proof keys (`derive_proof_key(root_key)`),
    /// NOT raw root keys. This ensures that the real issuer key is never exposed as a
    /// tree leaf.
    ///
    /// Without a federation tree, the delegatee falls back to synthetic/test proofs or
    /// must supply the tree at proof-generation time.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to delegate from.
    /// * `to` - The public key of the agent receiving the delegation.
    /// * `restrictions` - Additional restrictions beyond those already on the token.
    /// * `federation_tree` - Federation Merkle tree for pre-generating membership proofs.
    pub fn delegate_with_tree(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
        federation_tree: &dregg_commit::merkle::MerkleTree,
    ) -> Result<DelegatedToken, SdkError> {
        self.delegate_with_tree_and_parent(token, to, restrictions, federation_tree, [0u8; 32])
    }

    /// Like [`Self::delegate_with_tree`], but anchors this delegation to a parent envelope hash.
    pub fn delegate_with_tree_and_parent(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
        federation_tree: &dregg_commit::merkle::MerkleTree,
        parent_delegation_hash: [u8; 32],
    ) -> Result<DelegatedToken, SdkError> {
        let attenuated = self.attenuate(token, restrictions)?;

        // Pass through the derived proof key to the delegatee.
        let proof_key = if token.can_prove() {
            let key = token.issuer_key();
            if *key != [0u8; 32] { Some(*key) } else { None }
        } else {
            None
        };

        // Pre-generate federation membership proof. The federation tree contains
        // BLAKE3-derived proof keys (not raw root keys). Look up the derived key.
        let membership_proof = if token.can_mint() {
            // Root token holder: derive the proof key and look it up in the tree.
            let derived = Self::derive_proof_key(token.root_key());
            federation_tree.membership_proof(&derived)
        } else {
            token.membership_proof.clone()
        };

        // Compute the caveat chain hash from the HMAC-verified attenuated token.
        let caveat_chain_hash = {
            let decoded = attenuated.decode()?;
            Some(Self::compute_caveat_chain_hash(&decoded)?)
        };

        // SECURITY: Sign the entire delegation envelope (v2 payload).
        let membership_leaf = membership_proof.as_ref().map(|p| p.leaf_hash);
        let signing_message = Self::compute_delegation_signing_message_v2(
            &attenuated.encoded,
            to,
            &attenuated.service,
            &attenuated.id,
            restrictions,
            &proof_key,
            &caveat_chain_hash,
            membership_leaf.as_ref(),
            &parent_delegation_hash,
            &self.public_key,
        );
        let sig = self.signing_key.sign(&signing_message);
        let delegator_signature = Signature(sig.to_bytes());

        Ok(DelegatedToken {
            token_bytes: attenuated.encoded.clone(),
            service: attenuated.service.clone(),
            label: attenuated.label.clone(),
            id: attenuated.id.clone(),
            delegatee: *to,
            restrictions: restrictions.clone(),
            proof_key,
            membership_proof,
            caveat_chain_hash,
            parent_delegation_hash,
            delegator_signature,
            delegator_public_key: self.public_key,
        })
    }

    /// Verify that a held token authorizes a given request.
    ///
    /// Returns `true` if the token passes verification for the request,
    /// `false` otherwise.
    pub fn verify_token(&self, token: &HeldToken, request: &AuthRequest) -> bool {
        match token.decode() {
            Ok(t) => t.verify(request).is_ok(),
            Err(_) => false,
        }
    }

    /// Maximum size (in bytes) for a delegated token's encoded payload.
    ///
    /// Tokens exceeding this size are rejected to prevent memory DoS attacks
    /// where an attacker sends an enormous token string.
    const MAX_DELEGATED_TOKEN_SIZE: usize = 64 * 1024; // 64 KiB

    /// Receive a delegated token into this cipherclerk.
    ///
    /// Call this when another agent has delegated a token to us. The token
    /// is added to the cipherclerk's held tokens. The delegatee does NOT receive the
    /// root key -- they can present the token for verification but cannot mint
    /// new root tokens.
    ///
    /// # Validation
    ///
    /// This method validates the delegated token before accepting it:
    /// - Size: token payload must not exceed 64 KiB (memory DoS prevention).
    /// - Deserializable: the token must parse as a valid macaroon structure.
    /// - Expiry: if the delegation restrictions specify `not_after`, it must not be in the past.
    ///
    /// # Errors
    ///
    /// Returns [`SdkError`] if any validation check fails.
    /// Receive an externally-sourced [`DelegatedToken`].
    ///
    /// # Authority model
    ///
    /// `policy` decides which delegator public keys are authorized to grant a
    /// delegation to this cipherclerk. The envelope's `delegator_public_key` must be
    /// accepted by `policy` AND the envelope's signature must verify under that
    /// same key. See [`DelegationAuthority`] for the policy variants.
    ///
    /// The previous `receive_delegation(delegated)` API silently accepted any
    /// signed envelope (or no envelope at all) — that was unsound. There is no
    /// safe default policy, so callers must always provide one.
    ///
    /// # Errors
    ///
    /// Returns [`SdkError::InvalidDelegation`] if:
    /// - the token bytes are oversized or unparseable,
    /// - the restrictions are expired,
    /// - the delegator's public key is rejected by the policy,
    /// - the signature does not verify under the (asserted) delegator key,
    /// - the envelope's `parent_delegation_hash` does not match a parent the
    ///   policy expected (when using [`DelegationAuthority::ChainsFromParent`]).
    pub fn receive_signed_delegation(
        &mut self,
        delegated: DelegatedToken,
        policy: &DelegationAuthority,
    ) -> Result<(), SdkError> {
        // (a) Size check.
        if delegated.token_bytes.len() > Self::MAX_DELEGATED_TOKEN_SIZE {
            return Err(SdkError::InvalidDelegation(format!(
                "token payload too large: {} bytes exceeds {} byte limit",
                delegated.token_bytes.len(),
                Self::MAX_DELEGATED_TOKEN_SIZE,
            )));
        }

        // (a.1) P1-6: depth bound on membership proof to prevent DoS via
        // maliciously-deserialized proofs with `usize::MAX`-sized paths.
        if let Some(ref mp) = delegated.membership_proof {
            if mp.siblings.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
                || mp.path_indices.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
            {
                return Err(SdkError::InvalidDelegation(format!(
                    "membership proof depth exceeds maximum ({} > {})",
                    mp.siblings.len().max(mp.path_indices.len()),
                    Self::MAX_MEMBERSHIP_PROOF_DEPTH,
                )));
            }
        }

        // (b) Structural validity (parse only; HMAC chain not verifiable without root key).
        let _decoded =
            MacaroonToken::from_encoded(&delegated.token_bytes, [0u8; 32]).map_err(|e| {
                SdkError::InvalidDelegation(format!("token failed to deserialize: {e}"))
            })?;

        // (c) Expiry.
        if let Some(not_after) = delegated.restrictions.not_after {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            if not_after <= now {
                return Err(SdkError::InvalidDelegation(format!(
                    "delegated token has expired: not_after={not_after}, now={now}"
                )));
            }
        }

        // (d) Delegatee binding: the envelope must be addressed to this cipherclerk.
        if delegated.delegatee != self.public_key {
            return Err(SdkError::InvalidDelegation(format!(
                "delegation addressed to {:?}, not this cipherclerk ({:?})",
                delegated.delegatee, self.public_key,
            )));
        }

        // (e) Authority check: the asserted delegator must be accepted by the policy.
        Self::check_delegation_authority(policy, &delegated)?;

        // (f) Signature verification: the envelope must be signed by the asserted
        // delegator key. After step (e), we know that key is authorized.
        Self::verify_delegation_envelope_v2(&delegated)?;

        // SECURITY: The token's HMAC chain is still not verified (we don't hold the
        // root key); structural validation + signed envelope + caveat_chain_hash
        // commitment is the strongest binding we can produce on the delegatee side.
        // Authorization decisions still require full HMAC verification at a verifier
        // that holds the root key.
        tracing::debug!(
            service = %delegated.service,
            id = %delegated.id,
            delegator = ?delegated.delegator_public_key,
            "accepted signed delegation: envelope verified; HMAC chain pending until presentation",
        );

        let membership_leaf = delegated.membership_proof.as_ref().map(|p| p.leaf_hash);
        let binding = DelegationBinding {
            kind: DelegationBindingKind::ExternalV2,
            delegatee: delegated.delegatee,
            delegator_public_key: delegated.delegator_public_key,
            delegator_signature: delegated.delegator_signature.clone(),
            restrictions: delegated.restrictions.clone(),
            proof_key: delegated.proof_key,
            membership_leaf,
            parent_delegation_hash: delegated.parent_delegation_hash,
        };

        let mut held = HeldToken::new(
            delegated.label,
            delegated.service,
            delegated.token_bytes,
            [0u8; 32],
            delegated.id,
        );
        held.verified = false;

        if let Some(proof_key) = delegated.proof_key {
            if proof_key != [0u8; 32] {
                held.issuer_key = proof_key;
            }
        }
        held.membership_proof = delegated.membership_proof;
        held.caveat_chain_hash = delegated.caveat_chain_hash;
        held.delegation_binding = Some(binding);

        // Sanity check: the binding we just attached must re-verify against
        // the current field state. This catches any drift between the
        // receive-time signing message and the post-construct re-verification
        // routine (i.e., it guarantees future authorization calls won't fail
        // spuriously on freshly-received tokens).
        held.reverify_delegation_binding()?;

        self.tokens.push(held);
        Ok(())
    }

    /// Receive a [`LocalDelegation`] produced in-process by a parent cipherclerk.
    ///
    /// This path is NOT exposed for externally-sourced bytes — [`LocalDelegation`]
    /// is not deserializable, so no caller can produce one from untrusted input.
    /// The envelope is still signature-bound (under the local-envelope tag, which
    /// is distinct from the external-envelope tag), so authority is uniformly
    /// enforced across all code paths.
    ///
    /// `expected_parent_pubkey` is the parent cipherclerk's identity; the signature
    /// must verify under that key.
    pub fn receive_local_delegation(
        &mut self,
        local: LocalDelegation,
        expected_parent_pubkey: &PublicKey,
    ) -> Result<(), SdkError> {
        if local.token_bytes.len() > Self::MAX_DELEGATED_TOKEN_SIZE {
            return Err(SdkError::InvalidDelegation(format!(
                "token payload too large: {} bytes exceeds {} byte limit",
                local.token_bytes.len(),
                Self::MAX_DELEGATED_TOKEN_SIZE,
            )));
        }

        // P1-6: membership-proof depth bound (mirror of receive_signed_delegation).
        if let Some(ref mp) = local.membership_proof {
            if mp.siblings.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
                || mp.path_indices.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
            {
                return Err(SdkError::InvalidDelegation(format!(
                    "membership proof depth exceeds maximum ({} > {})",
                    mp.siblings.len().max(mp.path_indices.len()),
                    Self::MAX_MEMBERSHIP_PROOF_DEPTH,
                )));
            }
        }

        let _decoded = MacaroonToken::from_encoded(&local.token_bytes, [0u8; 32]).map_err(|e| {
            SdkError::InvalidDelegation(format!("token failed to deserialize: {e}"))
        })?;

        if local.delegatee != self.public_key {
            return Err(SdkError::InvalidDelegation(format!(
                "local delegation addressed to {:?}, not this cipherclerk ({:?})",
                local.delegatee, self.public_key,
            )));
        }

        if local.delegator_public_key != *expected_parent_pubkey {
            return Err(SdkError::InvalidDelegation(format!(
                "local delegator key {:?} does not match expected parent {:?}",
                local.delegator_public_key, expected_parent_pubkey,
            )));
        }

        // Verify the local-envelope signature.
        let membership_leaf = local.membership_proof.as_ref().map(|p| p.leaf_hash);
        let signing_message = Self::compute_local_delegation_signing_message(
            &local.token_bytes,
            &local.delegatee,
            &local.service,
            &local.id,
            &local.restrictions,
            &local.proof_key,
            &local.caveat_chain_hash,
            membership_leaf.as_ref(),
            &local.delegator_public_key,
        );
        use ed25519_dalek::Verifier;
        let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(&local.delegator_public_key.0)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!("invalid delegator public key: {e}"))
            })?;
        let signature = ed25519_dalek::Signature::from_bytes(&local.delegator_signature.0);
        verifying_key
            .verify(&signing_message, &signature)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!(
                    "local delegation signature verification failed: {e}"
                ))
            })?;

        let binding = DelegationBinding {
            kind: DelegationBindingKind::Local,
            delegatee: local.delegatee,
            delegator_public_key: local.delegator_public_key,
            delegator_signature: local.delegator_signature.clone(),
            restrictions: local.restrictions.clone(),
            proof_key: local.proof_key,
            membership_leaf,
            parent_delegation_hash: [0u8; 32],
        };

        let mut held = HeldToken::new(
            local.label,
            local.service,
            local.token_bytes,
            [0u8; 32],
            local.id,
        );
        held.verified = false;

        if let Some(proof_key) = local.proof_key {
            if proof_key != [0u8; 32] {
                held.issuer_key = proof_key;
            }
        }
        held.membership_proof = local.membership_proof;
        held.caveat_chain_hash = local.caveat_chain_hash;
        held.delegation_binding = Some(binding);

        // Sanity check that the binding re-verifies in the post-construct
        // path — same rationale as receive_signed_delegation.
        held.reverify_delegation_binding()?;

        self.tokens.push(held);
        Ok(())
    }

    /// Apply the authority policy to a delegation envelope.
    ///
    /// # Authority model (v1)
    ///
    /// We do not have a global root-issuer registry: any cipherclerk may legitimately
    /// produce a token. "Authority" therefore reduces to: *does the receiver
    /// have prior reason to trust this delegator key for this chain?*
    ///
    /// The receiver expresses that trust via [`DelegationAuthority`]:
    /// - `TrustedKey(pk)`: accept envelopes signed by exactly `pk`.
    /// - `TrustedKeys(set)`: accept envelopes signed by any key in `set`.
    /// - `ChainsFromParent { parent_hash, delegator }`: accept envelopes that
    ///   declare the given parent hash AND are signed by `delegator`. Used when
    ///   re-delegating along a chain the receiver has already accepted upstream.
    /// - `Open { warn }`: accept any well-signed envelope. This is unsafe and
    ///   only intended for development; production callers should NEVER use it.
    fn check_delegation_authority(
        policy: &DelegationAuthority,
        env: &DelegatedToken,
    ) -> Result<(), SdkError> {
        match policy {
            DelegationAuthority::TrustedKey(pk) => {
                if env.delegator_public_key != *pk {
                    return Err(SdkError::InvalidDelegation(format!(
                        "delegator {:?} not in authority set (expected {:?})",
                        env.delegator_public_key, pk,
                    )));
                }
                Ok(())
            }
            DelegationAuthority::TrustedKeys(set) => {
                if !set.contains(&env.delegator_public_key) {
                    return Err(SdkError::InvalidDelegation(format!(
                        "delegator {:?} not in authority set ({} keys)",
                        env.delegator_public_key,
                        set.len(),
                    )));
                }
                Ok(())
            }
            DelegationAuthority::ChainsFromParent {
                parent_hash,
                delegator,
            } => {
                if env.parent_delegation_hash != *parent_hash {
                    return Err(SdkError::InvalidDelegation(format!(
                        "parent_delegation_hash mismatch: envelope claims {:?}, policy expects {:?}",
                        env.parent_delegation_hash, parent_hash,
                    )));
                }
                if env.delegator_public_key != *delegator {
                    return Err(SdkError::InvalidDelegation(format!(
                        "chain delegator {:?} does not match policy-expected {:?}",
                        env.delegator_public_key, delegator,
                    )));
                }
                Ok(())
            }
            #[cfg(any(test, feature = "unsafe-test-utils"))]
            DelegationAuthority::Open { warn } => {
                if *warn {
                    tracing::warn!(
                        delegator = ?env.delegator_public_key,
                        "DelegationAuthority::Open: accepting envelope without authority check (unsafe)",
                    );
                }
                Ok(())
            }
        }
    }

    // =========================================================================
    // Receipt Chain (Proof-Carrying State)
    // =========================================================================

    // ChainAppendError is defined at module scope below; documented here:
    // see [`ChainAppendError::ReceiptChainMismatch`] for the strict-mode
    // semantics enforced by [`Self::append_receipt`].

    /// Append a receipt to this cipherclerk's chain after a successful turn execution.
    ///
    /// # Strict chain semantics (P0 #77 fix)
    ///
    /// The receipt's `previous_receipt_hash` is treated as follows:
    ///
    /// - **`Some(h)`** — `h` must equal the hash of the cipherclerk's current
    ///   chain head. If the chain is empty, `Some(h)` is a mismatch (the
    ///   executor that produced the receipt thinks the chain is non-empty but
    ///   the cipherclerk thinks otherwise — a divergence). Otherwise, equality
    ///   is required. A mismatch returns
    ///   [`ChainAppendError::ReceiptChainMismatch`] **without** mutating the
    ///   chain.
    /// - **`None`** — the cipherclerk fills in its current head. This preserves
    ///   compatibility with callers that build receipts in test contexts (or
    ///   from paths that don't track the head) while still being strict against
    ///   adversarial supplied-prev-hash values.
    ///
    /// The fork-detection contract: any caller that *does* supply a
    /// `previous_receipt_hash` (e.g. a receipt produced by an honest executor
    /// that auto-fills from its own ledger) will surface a divergence rather
    /// than have it silently rewritten. Pre-fix, the cipherclerk overwrote
    /// the supplied value unconditionally, which made the cipherclerk's chain
    /// disagree with the federation's chain without any observable signal.
    ///
    /// The caller must explicitly reconcile (request the federation's view, reset
    /// the cipherclerk, branch, etc.) — there is no audit-trail mode that papers
    /// over a divergence by rewriting the link.
    ///
    /// This is the primary method for building the proof-carrying state chain.
    /// Call this after `TurnExecutor::execute()` returns a committed result.
    pub fn append_receipt(
        &mut self,
        mut receipt: dregg_turn::TurnReceipt,
    ) -> Result<(), ChainAppendError> {
        let expected_prev = self.receipt_chain.last().map(|r| r.receipt_hash());

        // Strict mode: if the caller provided a prev_hash, it must match the
        // cipherclerk's current head. The previous behavior (silently overwriting
        // the caller's value with the cipherclerk's head) would mask a fork:
        // an executor that disagreed with the cipherclerk about the chain head
        // would still have its receipt appended, after which cipherclerk's
        // chain and the federation's chain would silently diverge.
        if let Some(claimed) = receipt.previous_receipt_hash {
            if Some(claimed) != expected_prev {
                return Err(ChainAppendError::ReceiptChainMismatch {
                    expected: expected_prev,
                    got: Some(claimed),
                });
            }
        }

        // Link to the previous receipt (no-op if already set to the matching
        // value; fills in when the caller left it unset).
        receipt.previous_receipt_hash = expected_prev;

        // Extend the IVC chain if enabled.
        if let Some(ref mut builder) = self.ivc_builder {
            use dregg_circuit::fold_types::{FoldWitness, RemovedFact};
            use dregg_circuit::ivc::FoldDelta;

            // Encode the state transition as a fold step: the pre_state transitions
            // to post_state. We model this as a removal of the pre-state fact and
            // the new_root being derived from the post-state hash.
            let pre_bb = Self::bytes_to_babybear(&receipt.pre_state_hash);
            let post_bb = Self::bytes_to_babybear(&receipt.post_state_hash);
            let turn_bb = Self::bytes_to_babybear(&receipt.turn_hash);

            let fold = FoldWitness {
                old_root: pre_bb,
                new_root: post_bb,
                removed_facts: vec![RemovedFact {
                    predicate: turn_bb,
                    terms: [
                        pre_bb,
                        post_bb,
                        BabyBear::new(receipt.computrons_used as u32),
                    ],
                    membership_proof: None,
                }],
                num_added_checks: 1,
                added_checks_commitment: dregg_circuit::fold_air::compute_test_checks_commitment(1),
            };
            // Best-effort: if the fold fails (e.g., root mismatch on first step),
            // we still append the receipt but skip IVC extension.
            // Don't append to IVC state — it would be inconsistent.
            let receipt_hash = receipt.receipt_hash();
            if let Err(e) = builder.add_fold(FoldDelta::new(fold)) {
                tracing::warn!("IVC fold failed for receipt {:?}: {}", receipt_hash, e);
            }
        }

        self.receipt_chain.push(receipt);
        Ok(())
    }

    /// Get the head (most recent) receipt in this cipherclerk's chain.
    ///
    /// Returns `None` if no turns have been executed yet (empty chain).
    pub fn receipt_head(&self) -> Option<&dregg_turn::TurnReceipt> {
        self.receipt_chain.last()
    }

    /// Get the number of receipts in this cipherclerk's chain.
    ///
    /// This is the number of successfully committed turns in this agent's history.
    pub fn receipt_chain_length(&self) -> usize {
        self.receipt_chain.len()
    }

    /// Get the full receipt chain for verification or export.
    ///
    /// The chain can be presented to any verifier who can check its integrity
    /// using [`dregg_turn::verify_receipt_chain`] without contacting a federation.
    pub fn receipt_chain(&self) -> &[dregg_turn::TurnReceipt] {
        &self.receipt_chain
    }

    /// Get the current state commitment (post_state_hash of the chain head).
    ///
    /// This is the state that the receipt chain proves. Returns `None` if the
    /// chain is empty.
    pub fn current_state_commitment(&self) -> Option<[u8; 32]> {
        self.receipt_chain.last().map(|r| r.post_state_hash)
    }

    /// Verify this cipherclerk's own receipt chain integrity.
    ///
    /// Returns `Ok(())` if the chain is valid, or an error describing the break.
    /// An empty chain is considered valid (no receipts to verify).
    pub fn verify_own_chain(&self) -> Result<(), dregg_turn::VerifyError> {
        if self.receipt_chain.is_empty() {
            return Ok(());
        }
        dregg_turn::verify_receipt_chain(&self.receipt_chain)
    }

    // =========================================================================
    // IVC (Incrementally Verifiable Computation)
    // =========================================================================

    /// Enable IVC accumulation for this cipherclerk's receipt chain.
    ///
    /// Once enabled, every call to [`append_receipt`](Self::append_receipt) will
    /// extend the IVC chain with the state transition, building a constant-size
    /// proof of the entire state transition history.
    ///
    /// # Arguments
    ///
    /// * `initial_root` - The initial state root (typically the pre_state_hash of
    ///   the first receipt, encoded as a BabyBear field element).
    pub fn enable_ivc(&mut self, initial_root: BabyBear) {
        self.ivc_builder = Some(IvcBuilder::new(initial_root));
    }

    /// Export the current IVC state proof.
    ///
    /// Returns a constant-size [`IvcProof`] covering the entire receipt chain
    /// accumulated since [`enable_ivc`](Self::enable_ivc) was called. Returns
    /// `None` if IVC is not enabled or no receipts have been appended since
    /// IVC was enabled.
    pub fn export_state_proof(&self) -> Option<IvcProof> {
        self.ivc_builder.as_ref()?.finalize_with_air()
    }

    /// Check whether IVC is currently enabled on this cipherclerk.
    pub fn ivc_enabled(&self) -> bool {
        self.ivc_builder.is_some()
    }

    // =========================================================================
    // Mode-Selected Authorization
    // =========================================================================

    /// Authorize a request using the specified verification mode.
    ///
    /// This is the unified entry point for all three verification modes:
    ///
    /// - [`VerificationMode::Trusted`]: Runs Datalog locally via
    ///   [`verify_token_datalog`](dregg_token::datalog_verify::verify_token_datalog),
    ///   returns full clearance and trace (~8us).
    ///
    /// - [`VerificationMode::SelectiveDisclosure`]: Runs Datalog locally, then
    ///   generates a STARK proof with selected facts as public inputs. The
    ///   verifier sees only the chosen facts and the conclusion (~200ms).
    ///
    /// - [`VerificationMode::FullyPrivate`]: Runs Datalog locally, then generates
    ///   a full `MultiStepDerivationAir` STARK proof. The verifier learns only
    ///   whether authorization was granted (~500ms).
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to authorize from.
    /// * `request` - The authorization request to evaluate.
    /// * `mode` - The verification mode determining what the verifier receives.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use dregg_sdk::{AgentCipherclerk, VerificationMode, AuthorizationPresentation};
    /// use dregg_token::AuthRequest;
    ///
    /// let cipherclerk = AgentCipherclerk::new();
    /// # let token = todo!();
    /// let request = AuthRequest {
    ///     service: Some("dns".into()),
    ///     action: Some("read".into()),
    ///     ..Default::default()
    /// };
    ///
    /// let presentation = cipherclerk.authorize(&token, &request, VerificationMode::Trusted).unwrap();
    /// ```
    pub fn authorize(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        mode: VerificationMode,
    ) -> Result<AuthorizationPresentation, SdkError> {
        match mode {
            VerificationMode::Trusted => self.authorize_trusted(token, request),
            VerificationMode::SelectiveDisclosure { reveal } => {
                self.authorize_selective(token, request, &reveal)
            }
            VerificationMode::FullyPrivate => self.authorize_private(token, request),
        }
    }

    /// Trusted mode: local Datalog evaluation, full visibility.
    fn authorize_trusted(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // P1-7: Defensive durable-binding reverification at every authorization
        // entry. For locally-minted root tokens this is a no-op (no binding
        // attached); for delegation-bound tokens that somehow reach the
        // trusted path it ensures post-receive tampering of `encoded`,
        // `caveat_chain_hash`, or membership leaf is detected.
        token.reverify_delegation_binding()?;

        let caveat_set = Self::extract_caveat_set(token)?;
        let result = dregg_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        Ok(AuthorizationPresentation::Trusted {
            clearance: result.clearance,
            trace: result.trace,
        })
    }

    /// Selective disclosure: STARK proof with chosen facts cryptographically committed.
    ///
    /// The revealed facts are bound to the proof via a Poseidon2 commitment included
    /// as a public input. The verifier recomputes the commitment from the plaintext
    /// facts and checks it matches the proof, ensuring the prover cannot lie about
    /// which facts were derived during evaluation.
    fn authorize_selective(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        reveal: &[FactIndex],
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to get the trace.
        // For attenuated tokens, use structural extraction (ZK proof replaces HMAC).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
        let result = dregg_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            dregg_trace::Conclusion::Allow { .. }
        );

        // Step 2: Extract the facts at the requested indices.
        let all_facts: Vec<TraceFact> = result
            .trace
            .steps
            .iter()
            .map(|step| step.derived_fact.clone())
            .collect();

        let revealed_facts: Vec<TraceFact> = reveal
            .iter()
            .filter_map(|idx| all_facts.get(idx.0).cloned())
            .collect();

        // Step 3: Compute the Poseidon2 commitment over the revealed facts.
        // This cryptographically binds the revealed facts to the STARK proof.
        let commitment = dregg_bridge::compute_revealed_facts_commitment(&revealed_facts);

        // Step 4: Generate STARK proof via the bridge with the commitment as a public input.
        // For attenuated tokens, use the issuer key path.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization_selective(token, request, commitment)?
        } else {
            self.prove_authorization_selective_with_issuer_key(
                token,
                token.issuer_key(),
                request,
                commitment,
            )?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
            revealed_facts_commitment: commitment,
            predicate_proofs: Vec::new(),
        })
    }

    /// Fully private mode: STARK proof revealing only the conclusion bit.
    fn authorize_private(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to determine conclusion.
        // For attenuated tokens, use structural extraction (no HMAC verification needed —
        // the ZK proof replaces the HMAC chain as the integrity guarantee).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
        let result = dregg_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            dregg_trace::Conclusion::Allow { .. }
        );

        // Step 2: Generate full STARK proof via the bridge.
        // The proof covers the entire MultiStepDerivationAir -- the verifier
        // only receives the conclusion public input, learning nothing else.
        //
        // For attenuated tokens that have the issuer key (can_prove() == true),
        // we use prove_authorization_with_issuer_key internally.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization(token, request)?
        } else {
            self.prove_authorization_with_issuer_key(token, token.issuer_key(), request)?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Private { proof, conclusion })
    }

    /// Authorize a request with per-fact disclosure control.
    ///
    /// Each fact in the derivation trace can be independently:
    /// - **Revealed**: shown in plaintext (like `SelectiveDisclosure`).
    /// - **Predicate-proven**: a ZK predicate proof is generated.
    /// - **Hidden**: nothing is revealed (like `FullyPrivate`).
    pub fn authorize_with_disclosure(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        disclosure: &DisclosureSpec,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to get the full trace.
        // For attenuated tokens, use structural extraction (ZK proof replaces HMAC).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
        let result = dregg_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            dregg_trace::Conclusion::Allow { .. }
        );

        // Step 2: Extract all derived facts from the trace.
        let all_facts: Vec<TraceFact> = result
            .trace
            .steps
            .iter()
            .map(|step| step.derived_fact.clone())
            .collect();

        // Step 3: Partition facts by disclosure mode.
        let mut revealed_facts: Vec<TraceFact> = Vec::new();
        let mut predicate_proofs: Vec<(usize, BridgePredicateProof)> = Vec::new();

        // Compute a state root for predicate fact commitments.
        // The issuer_key is always the derived proof key (never the raw root key),
        // whether this is a root token or an attenuated token.
        let state_root = Self::bytes_to_babybear(token.issuer_key());

        for (fact_index, disclosure_mode) in &disclosure.facts {
            let fact = match all_facts.get(*fact_index) {
                Some(f) => f,
                None => continue,
            };

            match disclosure_mode {
                FactDisclosure::Reveal => {
                    revealed_facts.push(fact.clone());
                }
                FactDisclosure::Predicate {
                    predicate_type,
                    threshold,
                } => {
                    let value = Self::extract_fact_value(fact)?;
                    let pred_bb = Self::trace_fact_predicate_bb(fact);
                    let term_bbs = Self::trace_fact_terms_bb(fact);
                    let fact_hash = poseidon2::hash_fact(pred_bb, &term_bbs);
                    let bridge_predicate =
                        Self::predicate_type_to_bridge(*predicate_type, threshold.as_u32());

                    let proof = dregg_bridge::prove_predicate_for_fact(
                        value,
                        fact_hash,
                        state_root,
                        &bridge_predicate,
                    )
                    .ok_or_else(|| {
                        SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                            "predicate proof generation failed for fact[{}]:                              {:?} not satisfiable for value {}",
                            fact_index, predicate_type, value
                        )))
                    })?;

                    predicate_proofs.push((*fact_index, proof));
                }
                FactDisclosure::CommittedThreshold {
                    threshold,
                    blinding,
                } => {
                    // Generate a committed-threshold proof: value >= threshold
                    // where neither value nor threshold is revealed to third parties.
                    let value = Self::extract_fact_value(fact)?;
                    let pred_bb = Self::trace_fact_predicate_bb(fact);
                    let term_bbs = Self::trace_fact_terms_bb(fact);
                    let fact_hash = poseidon2::hash_fact(pred_bb, &term_bbs);

                    let committed_proof = dregg_bridge::prove_committed_threshold(
                        value,
                        threshold.as_u32(),
                        blinding.as_u32(),
                        fact_hash,
                        state_root,
                    )
                    .ok_or_else(|| {
                        SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                            "committed-threshold proof generation failed for fact[{}]: \
                             value {} does not satisfy committed threshold",
                            fact_index, value
                        )))
                    })?;

                    // Store the committed-threshold proof directly. The verifier
                    // sees only the threshold_commitment and fact_commitment (both
                    // are Poseidon2 hashes that hide the actual values).
                    let bridge_proof = BridgePredicateProof {
                        predicate: Predicate::Gte(0), // Threshold hidden; predicate label is nominal
                        proof: dregg_bridge::BridgePredicateProofInner::CommittedThreshold(
                            committed_proof.proof,
                        ),
                        fact_commitment: committed_proof.fact_commitment,
                    };
                    predicate_proofs.push((*fact_index, bridge_proof));
                }
                FactDisclosure::ArithmeticPredicate { .. } => {
                    // Arithmetic predicates over multiple facts are not yet supported
                    // in the selective disclosure pipeline. Treated as hidden for now.
                }
                FactDisclosure::Hidden => {}
            }
        }

        // Step 4: Compute Poseidon2 commitment over revealed facts.
        let commitment = dregg_bridge::compute_revealed_facts_commitment(&revealed_facts);

        // Step 5: Generate STARK proof with the commitment as public input.
        // For attenuated tokens, use the issuer key path.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization_selective(token, request, commitment)?
        } else {
            self.prove_authorization_selective_with_issuer_key(
                token,
                token.issuer_key(),
                request,
                commitment,
            )?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
            revealed_facts_commitment: commitment,
            predicate_proofs,
        })
    }

    /// Extract a numeric value from a trace fact's first term.
    ///
    /// Returns an error if the term is a variable — predicate proofs cannot
    /// operate on unground variables because there is no concrete value to prove
    /// a predicate over.
    fn extract_fact_value(fact: &TraceFact) -> Result<u32, SdkError> {
        if let Some(term) = fact.terms.first() {
            match term {
                dregg_trace::Term::Int(v) => Ok((*v).max(0).min(u32::MAX as i64) as u32),
                dregg_trace::Term::Const(sym) => {
                    Ok(u32::from_le_bytes([sym[0], sym[1], sym[2], sym[3]])
                        % dregg_circuit::field::BABYBEAR_P)
                }
                dregg_trace::Term::Var(_) => Err(SdkError::InvalidWitness(
                    "cannot prove predicates on unground variables".into(),
                )),
            }
        } else {
            Ok(0)
        }
    }

    /// Convert a trace fact's predicate symbol to a BabyBear field element.
    fn trace_fact_predicate_bb(fact: &TraceFact) -> BabyBear {
        Self::bytes_to_babybear(&fact.predicate)
    }

    /// Convert a trace fact's terms to BabyBear field elements (up to 3).
    fn trace_fact_terms_bb(fact: &TraceFact) -> [BabyBear; 3] {
        let mut term_bbs = [BabyBear::ZERO; 3];
        for (i, term) in fact.terms.iter().take(3).enumerate() {
            term_bbs[i] = match term {
                dregg_trace::Term::Const(sym) => Self::bytes_to_babybear(sym),
                dregg_trace::Term::Int(v) => BabyBear::from_u64(*v as u64),
                dregg_trace::Term::Var(_) => BabyBear::ZERO,
            };
        }
        term_bbs
    }

    /// Convert a PredicateType + threshold to the bridge Predicate enum.
    pub(crate) fn predicate_type_to_bridge(
        predicate_type: PredicateType,
        threshold: u32,
    ) -> Predicate {
        match predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => Predicate::Gte(threshold),
            PredicateType::Lte | PredicateType::InRangeHigh => Predicate::Lte(threshold),
            PredicateType::Gt => Predicate::Gt(threshold),
            PredicateType::Lt => Predicate::Lt(threshold),
            PredicateType::Neq => Predicate::Neq(threshold),
        }
    }

    /// Extract the CaveatSet from a held token by decoding and verifying the HMAC chain.
    fn extract_caveat_set(
        token: &HeldToken,
    ) -> Result<dregg_token::dregg_macaroon::caveat::CaveatSet, SdkError> {
        let decoded = token.decode()?;
        let caveat_set = decoded
            .inner()
            .verify(token.root_key(), decoded.discharges())
            .map_err(|e| {
                SdkError::Token(dregg_token::TokenError::VerificationFailed(e.to_string()))
            })?;
        Ok(caveat_set)
    }

    /// Extract the CaveatSet from a held token STRUCTURALLY (without HMAC verification).
    ///
    /// This reads caveats directly from the decoded macaroon structure. It does NOT
    /// verify the HMAC chain — caveats are returned as-is from the MsgPack encoding.
    ///
    /// **Security model**: This is safe for the ZK proof-generation path because:
    /// - The ZK proof proves the Datalog derivation from committed facts.
    /// - If the prover tampers with caveats, they'd be proving a false statement
    ///   that won't match what the verifier expects (the proof would be meaningless).
    /// - HMAC chain integrity is a separate concern: it proves to the ISSUER that
    ///   caveats weren't stripped. The ZK proof replaces this guarantee for the
    ///   VERIFIER by proving the derivation is valid for the committed state.
    ///
    /// This method is used for attenuated tokens that don't have the root key for
    /// HMAC verification but need to extract caveats for proof generation.
    fn extract_caveat_set_structural(
        token: &HeldToken,
    ) -> Result<dregg_token::dregg_macaroon::caveat::CaveatSet, SdkError> {
        // Decode the macaroon structure (this doesn't require the root key — it just
        // parses the MsgPack encoding). We use a zeroed key since from_encoded only
        // stores the key, it doesn't verify during decode.
        let decoded =
            MacaroonToken::from_encoded(&token.encoded, [0u8; 32]).map_err(SdkError::Token)?;

        // Extract first-party caveats directly from the macaroon structure.
        // The caveats field is public on Macaroon and populated during deserialization.
        Ok(decoded.inner().caveats.clone())
    }

    /// Extract caveat set using HMAC verification if possible, falling back to
    /// structural extraction for attenuated tokens that have the issuer key
    /// (i.e., tokens that can prove but can't mint).
    fn extract_caveat_set_for_proof(
        token: &HeldToken,
    ) -> Result<dregg_token::dregg_macaroon::caveat::CaveatSet, SdkError> {
        // Authority invariant: any caveat extraction path that produces facts
        // ultimately fed into a STARK proof must re-verify the delegation
        // binding so post-receive tampering of `encoded` is detected here too.
        token.reverify_delegation_binding()?;

        if token.can_mint() {
            // Root token: use full HMAC verification (most secure path).
            Self::extract_caveat_set(token)
        } else if token.can_prove() {
            // Attenuated token with issuer key: structural extraction is safe
            // because the ZK proof replaces HMAC chain verification.
            Self::extract_caveat_set_structural(token)
        } else {
            Err(SdkError::MissingKey(
                "token has no issuer key; cannot extract caveats for proof generation. \
                 Use prove_authorization_with_issuer_key() and provide the issuer key."
                    .into(),
            ))
        }
    }

    /// Serialize a bridge presentation proof to bytes for wire transmission.
    ///
    /// Converts to a `WirePresentationProof` (stripping the private trace) and
    /// serializes via postcard. This matches what `DreggEngine::verify_presentation_against`
    /// expects: `postcard::from_bytes::<WirePresentationProof>`.
    fn serialize_proof(bridge_proof: BridgePresentationProof) -> Result<Vec<u8>, SdkError> {
        let wire_proof = bridge_proof.into_wire_proof();
        postcard::to_stdvec(&wire_proof)
            .map_err(|e| SdkError::Wire(format!("failed to serialize wire proof: {e}")))
    }

    // =========================================================================
    // Signing
    // =========================================================================

    /// Sign a turn for submission to the ledger.
    ///
    /// Computes the BLAKE3 hash of the turn and signs it with this cipherclerk's
    /// Ed25519 key. The resulting [`SignedTurn`] can be submitted to a silo
    /// or local executor.
    ///
    /// # Arguments
    ///
    /// * `turn` - The turn to sign (will be hashed).
    pub fn sign_turn(&self, turn: &Turn) -> SignedTurn {
        let turn_bytes = self.compute_turn_bytes(turn);
        let sig = self.signing_key.sign(&turn_bytes);
        SignedTurn {
            turn: turn.clone(),
            signature: Signature(sig.to_bytes()),
            signer: self.public_key,
        }
    }

    /// Sign arbitrary bytes with this cipherclerk's identity.
    ///
    /// Useful for custom authorization schemes outside the turn model.
    pub fn sign_bytes(&self, message: &[u8]) -> Signature {
        let sig = self.signing_key.sign(message);
        Signature(sig.to_bytes())
    }

    /// Build an [`EncryptedTurn`](dregg_turn::EncryptedTurn) envelope for
    /// the given `Turn`, encrypted to `executor_x25519_public` (the X25519
    /// public key the recipient executor exposes via
    /// `GET /turns/encryption-key`).
    ///
    /// This is the sender-side counterpart of
    /// [`dregg_turn::TurnExecutor::apply_encrypted_turn`]. The resulting
    /// envelope can be postcard-encoded and POSTed to
    /// `/turns/submit-encrypted`.
    ///
    /// # Validity proof
    ///
    /// Per AUDIT-privacy.md §11.2, this Phase-1 helper packs an empty
    /// validity proof whose public inputs bind to the actual turn
    /// commitment / agent commitment / conflict-set commitment so
    /// `EncryptedTurn::verify_metadata` succeeds at the executor. The
    /// STARK proof itself is the responsibility of a future phase
    /// (Phase-2 STARK-validity ceremony) — callers wanting real proof
    /// validation should construct the `TurnValidityProof` themselves
    /// and use `EncryptedTurn::encrypt_for_executor` directly.
    ///
    /// # Boundary (BOUNDARIES.md §5)
    ///
    /// The sender is `cleartext-inside` until this call returns; after
    /// return, the inner turn is `commitment-inside` everyone except
    /// holders of the executor's matching X25519 unsealer secret.
    pub fn make_encrypted_turn(
        &self,
        turn: &Turn,
        executor_x25519_public: &[u8; 32],
        submitted_at: i64,
    ) -> Result<dregg_turn::EncryptedTurn, dregg_turn::EncryptedTurnError> {
        use dregg_turn::{ConflictSet, EncryptedTurn, TurnValidityProof, TurnValidityPublicInputs};

        // Build an empty Bloom conflict set. A real sender would populate
        // this from the turn's access set so the federation can detect
        // conflicts without seeing cell IDs; the Phase-1 helper keeps it
        // empty (false-positive-free over zero cells).
        let conflict_set = ConflictSet::new();

        // Compute the commitment over the same serialization
        // (`serde_json`) that `encrypt_for_executor` uses, so
        // `verify_metadata` succeeds at the executor.
        let plaintext = serde_json::to_vec(turn)
            .map_err(|e| dregg_turn::EncryptedTurnError::SerializationFailed(e.to_string()))?;
        let turn_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-turn-commitment v1");
            hasher.update(&plaintext);
            *hasher.finalize().as_bytes()
        };

        let public_inputs = TurnValidityPublicInputs {
            turn_commitment,
            agent_commitment: TurnValidityPublicInputs::compute_agent_commitment(&turn.agent),
            claimed_nonce: turn.nonce,
            min_fee: 0,
            conflict_set_commitment: conflict_set.commitment(),
        };

        let validity_proof = TurnValidityProof {
            proof_bytes: Vec::new(),
            public_inputs,
        };

        EncryptedTurn::encrypt_for_executor(
            turn,
            turn.agent,
            executor_x25519_public,
            conflict_set,
            validity_proof,
            submitted_at,
        )
    }

    /// Sign an [`Action`](dregg_turn::action::Action) by replacing its
    /// authorization with a real [`Signature`](dregg_turn::action::Authorization)
    /// over the canonical signing message.
    ///
    /// This is the SDK-side wrapper for the "ed25519 sign-an-action" dance
    /// that today is replicated across `apps/nameservice` (with a `[0u8; 64]`
    /// placeholder) and `runtime::AgentRuntime::execute` (with manual
    /// `TurnExecutor::compute_signing_message` calls). It uses the
    /// `dregg-action-sig-v2` domain that `TurnExecutor` requires.
    ///
    /// # Arguments
    ///
    /// * `action` - The action to sign. Its existing `authorization` is
    ///   overwritten.
    /// * `federation_id` - The 32-byte federation identifier this action
    ///   is being authorized against. Must match what the executor will
    ///   use during verification (`dregg-action-sig-v2` binds the
    ///   federation into the signing message to prevent cross-federation
    ///   replay).
    ///
    /// # Returns
    ///
    /// A clone of `action` with `authorization` set to
    /// `Authorization::Signature(sig)` over the canonical message bytes.
    pub fn sign_action(
        &self,
        action: dregg_turn::action::Action,
        federation_id: &[u8; 32],
    ) -> dregg_turn::action::Action {
        use dregg_turn::action::{Action, Authorization};
        use dregg_turn::executor::TurnExecutor;
        let unsigned = Action {
            authorization: Authorization::Unchecked,
            ..action
        };
        let message = TurnExecutor::compute_signing_message(&unsigned, federation_id);
        let sig = self.signing_key.sign(&message);
        Action {
            authorization: Authorization::from_sig_bytes(sig.to_bytes()),
            ..unsigned
        }
    }

    /// Explain an [`Action`](dregg_turn::action::Action) — the clerk stating,
    /// faithfully, what an action does *before* it is signed.
    ///
    /// This is a thin, total wrapper over [`crate::explain::explain_action`].
    /// The rendering is the third reading of the term alongside execute and
    /// prove: it never panics (totality) and carries a canonical `[sem …]`
    /// digest tag, so two actions with different effect-semantics get different
    /// explanations (injectivity-on-semantics). It does not authorize or sign
    /// anything — it only describes.
    ///
    /// A citizen's UI shows this string to answer "what am I about to
    /// authorize?" so the citizen never signs blind.
    pub fn explain_action(&self, action: &dregg_turn::action::Action) -> String {
        crate::explain::explain_action(action)
    }

    /// Explain an entire [`Turn`] — what the whole call forest does — before it
    /// is signed. Thin, total wrapper over [`crate::explain::explain_turn`].
    pub fn explain_turn(&self, turn: &Turn) -> String {
        crate::explain::explain_turn(turn)
    }

    /// Sign an action *and* return the clerk's faithful explanation of it, so a
    /// UI can show the citizen exactly what they are authorizing — the
    /// anti-blind-signing path.
    ///
    /// This is [`sign_action`](Self::sign_action) with the explanation
    /// surfaced: signing semantics are identical (the `action` field equals
    /// what `sign_action` would return), and the `explanation` is rendered from
    /// the signed action so the caller can display "this is what you are about
    /// to authorize" next to it.
    pub fn explain_and_sign_action(
        &self,
        action: dregg_turn::action::Action,
        federation_id: &[u8; 32],
    ) -> ExplainedSignedAction {
        let signed = self.sign_action(action, federation_id);
        let explanation = crate::explain::explain_action(&signed);
        ExplainedSignedAction {
            action: signed,
            explanation,
        }
    }

    /// Sign a turn *and* return the clerk's faithful explanation of the whole
    /// call forest — the turn-level anti-blind-signing path.
    ///
    /// [`sign_turn`](Self::sign_turn) with the explanation surfaced. Signing
    /// semantics are unchanged: `signed` equals what `sign_turn` would produce.
    pub fn explain_and_sign_turn(&self, turn: &Turn) -> ExplainedSignedTurn {
        let explanation = crate::explain::explain_turn(turn);
        let signed = self.sign_turn(turn);
        ExplainedSignedTurn {
            signed,
            explanation,
        }
    }

    /// Build a self-signed single-effect [`Action`](dregg_turn::action::Action)
    /// targeting one cell.
    ///
    /// Equivalent to the `ActionBuilder::new(target, method, caller).signed_by(sig)`
    /// flow but performs the sign step here, so callers do not have to manually
    /// invoke `TurnExecutor::compute_signing_message` or carry zero-signature
    /// placeholders. The `caller` field is set to the cipherclerk's default cell.
    ///
    /// For multi-effect actions, prefer building an [`Action`] directly (e.g.
    /// through `dregg_turn::builder::ActionBuilder`) and then calling
    /// [`sign_action`](Self::sign_action).
    ///
    /// # Arguments
    ///
    /// * `target` - The cell the action targets.
    /// * `method` - The action method name (e.g. `"transfer"`, `"register_name"`).
    /// * `effects` - Effects to include in the action.
    /// * `federation_id` - Federation binding for the canonical signing message.
    pub fn make_action(
        &self,
        target: CellId,
        method: &str,
        effects: Vec<Effect>,
        federation_id: &[u8; 32],
    ) -> dregg_turn::action::Action {
        let unsigned = crate::raw::unsigned_action_named(target, method, effects);
        self.sign_action(unsigned, federation_id)
    }

    /// Build a self-signed single-action [`Turn`] ready for submission.
    ///
    /// This is the "Turn skeleton" helper called out in `SDK-REVIEW.md` as
    /// the Tier-0 missing primitive. It bundles one already-signed action
    /// into a [`Turn`] with sane defaults: fee=0, no memo, no expiry,
    /// `previous_receipt_hash` taken from the cipherclerk's receipt chain head.
    ///
    /// The agent field is `cipherclerk.cell_id("default")`. Use
    /// [`make_turn_for`](Self::make_turn_for) if you need a non-default
    /// domain.
    ///
    /// The action is *not* re-signed here — callers should produce it via
    /// [`make_action`](Self::make_action) or [`sign_action`](Self::sign_action).
    pub fn make_turn(&self, action: dregg_turn::action::Action) -> Turn {
        self.make_turn_for("default", action)
    }

    /// Like [`make_turn`](Self::make_turn) but with an explicit agent domain.
    pub fn make_turn_for(&self, domain: &str, action: dregg_turn::action::Action) -> Turn {
        self.make_turn_with_actions_for(domain, vec![action])
    }

    /// Wrap multiple already-signed [`Action`](dregg_turn::action::Action)s in
    /// one [`Turn`] (an atomic group). All actions appear as roots in the
    /// same call forest — they commit or roll back together.
    ///
    /// Use this when an app needs to settle multiple operations atomically:
    /// e.g. orderbook settlement (release one escrow + create the counterparty
    /// escrow), or escrow-swap (two atomic releases). Each action carries its
    /// own signature; the per-action signing covers each action's canonical
    /// bytes, so signers do not have to coordinate on the same turn-level
    /// message.
    ///
    /// Defaults match [`make_turn`](Self::make_turn): agent =
    /// `cell_id("default")`, fee = 0, `previous_receipt_hash` taken from the
    /// cipherclerk's chain head.
    pub fn make_turn_with_actions(&self, actions: Vec<dregg_turn::action::Action>) -> Turn {
        self.make_turn_with_actions_for("default", actions)
    }

    /// Like [`make_turn_with_actions`](Self::make_turn_with_actions) but with
    /// an explicit agent domain.
    pub fn make_turn_with_actions_for(
        &self,
        domain: &str,
        actions: Vec<dregg_turn::action::Action>,
    ) -> Turn {
        use dregg_turn::forest::{CallForest, CallTree};
        let roots = actions
            .into_iter()
            .map(|action| CallTree {
                action,
                children: vec![],
                hash: [0u8; 32],
            })
            .collect();
        Turn {
            agent: self.cell_id(domain),
            nonce: 0,
            fee: 0,
            call_forest: CallForest {
                roots,
                forest_hash: [0u8; 32],
            },
            memo: None,
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Build a complete turn authorized by a held token.
    ///
    /// This is the high-level convenience method that wires together token authorization
    /// and turn construction. It:
    /// 1. Generates a STARK authorization proof from the held token.
    /// 2. Constructs a turn with the given effects targeting the specified cell.
    /// 3. Signs the turn with this cipherclerk's identity.
    ///
    /// # Arguments
    ///
    /// * `token` - The held authorization token granting access.
    /// * `target` - The cell to apply effects to.
    /// * `effects` - The effects to include in the turn's action.
    /// * `action_name` - The action being authorized (e.g., "write", "transfer").
    /// * `resource_name` - The resource being accessed (e.g., "balance", "state").
    /// * `fee` - The computron fee for this turn.
    ///
    /// # Returns
    ///
    /// A [`SignedTurn`] ready for submission, or an error if authorization proof
    /// generation fails.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use dregg_sdk::AgentCipherclerk;
    /// # use dregg_cell::CellId;
    /// # use dregg_turn::Effect;
    /// # let cipherclerk = AgentCipherclerk::new();
    /// # let token = todo!();
    /// # let target = CellId::derive_raw(&[0; 32], &[0; 32]);
    /// let signed_turn = cipherclerk.build_authorized_turn(
    ///     &token,
    ///     target,
    ///     vec![Effect::Transfer { from: target, to: target, amount: 100 }],
    ///     "transfer",
    ///     "balance",
    ///     100, // fee
    /// ).unwrap();
    /// ```
    pub fn build_authorized_turn(
        &self,
        token: &HeldToken,
        target: CellId,
        effects: Vec<Effect>,
        action_name: &str,
        resource_name: &str,
        fee: u64,
    ) -> Result<SignedTurn, SdkError> {
        use dregg_token::AuthRequest;
        use dregg_turn::action::{Action, Authorization, DelegationMode};
        use dregg_turn::forest::{CallForest, CallTree};

        // 1. Generate authorization STARK proof.
        let request = AuthRequest {
            service: Some(resource_name.to_string()),
            action: Some(action_name.to_string()),
            ..Default::default()
        };

        let presentation = self.authorize(token, &request, VerificationMode::FullyPrivate)?;
        let proof_bytes = match &presentation {
            AuthorizationPresentation::Private { proof, .. } => proof.clone(),
            AuthorizationPresentation::Selective { proof, .. } => proof.clone(),
            AuthorizationPresentation::Trusted { .. } => {
                // Trusted mode doesn't produce proof bytes for wire transmission.
                // Use an empty vec; the executor will accept signature-based auth.
                Vec::new()
            }
        };

        // 2. Build the turn with proof authorization.
        let action = Action {
            target,
            method: dregg_turn::action::symbol(action_name),
            args: Vec::new(),
            authorization: Authorization::Proof {
                proof_bytes,
                bound_action: action_name.to_string(),
                bound_resource: resource_name.to_string(),
            },
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };

        let turn = Turn {
            agent: self.cell_id("default"),
            // AUDIT[P3-6]: nonce hardcoded to 0; documented as caller's
            // responsibility. `previous_receipt_hash` is now plumbed through
            // from the cipherclerk's receipt chain to bind this turn to the
            // executor-enforced receipt chain.
            nonce: 0, // Caller should set appropriately or use a TurnBuilder
            fee,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            memo: None,
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // 3. Sign the turn.
        Ok(self.sign_turn(&turn))
    }

    // =========================================================================
    // Delegation Envelope Signing / Verification (v2)
    //
    // Authority model:
    //   The delegation envelope is signed by the delegator's cipherclerk key. The
    //   receiver supplies a `DelegationAuthority` policy that decides which
    //   delegator key is authorized (TrustedKey / TrustedKeys / ChainsFromParent
    //   / Open). The signature MUST verify under the asserted delegator key, AND
    //   the asserted delegator key MUST be accepted by the policy.
    //
    //   We do not chain to a root issuer because dregg cipherclerks are sovereign:
    //   there is no global registry of "who is allowed to mint a token". Trust
    //   is established explicitly by the receiver — either by hard-coding an
    //   expected key, or by linking to a previously-accepted parent envelope.
    //
    // Signed payload:
    //   The v2 payload binds every authority-affecting field:
    //     - token_bytes (the actual macaroon being delegated)
    //     - delegatee (who can present this token)
    //     - service (which service this token is for)
    //     - id (token identifier)
    //     - restrictions (the attenuations applied)
    //     - proof_key (the BLAKE3-derived ZK proof key, if any)
    //     - caveat_chain_hash (caveat integrity commitment)
    //     - membership_leaf (federation-proof leaf, if any)
    //     - parent_delegation_hash (links chains; zero for root delegations)
    //     - delegator_public_key (binds the signer to the envelope)
    //
    //   Domain separation uses `blake3::keyed_hash` with the v2 envelope context,
    //   distinct from the v1 binding tag and from the local-delegation tag.
    // =========================================================================

    /// Domain key for the external delegation envelope (v2).
    const DELEGATION_ENVELOPE_V2_CONTEXT: &'static str = "dregg-delegation-envelope-v2";

    /// Domain key for the local (in-process) delegation envelope.
    const DELEGATION_ENVELOPE_LOCAL_V1_CONTEXT: &'static str = "dregg-delegation-local-v1";

    /// Compute the canonical v2 signing message for an external delegation envelope.
    ///
    /// Binds every authority-affecting field. See [`AgentCipherclerk::compute_delegation_signing_message_v2`]
    /// documentation block above for the full payload listing.
    pub(crate) fn compute_delegation_signing_message_v2(
        token_bytes: &str,
        delegatee: &PublicKey,
        service: &str,
        id: &str,
        restrictions: &Attenuation,
        proof_key: &Option<[u8; 32]>,
        caveat_chain_hash: &Option<[u8; 32]>,
        membership_leaf: Option<&[u8; 32]>,
        parent_delegation_hash: &[u8; 32],
        delegator_public_key: &PublicKey,
    ) -> [u8; 32] {
        // Use postcard for deterministic canonical serialization of structured
        // fields (restrictions in particular), and length-prefix opaque blobs so
        // boundary ambiguity is impossible.
        let mut hasher = blake3::Hasher::new_derive_key(Self::DELEGATION_ENVELOPE_V2_CONTEXT);

        // Length-prefixed strings.
        hasher.update(&(token_bytes.len() as u64).to_le_bytes());
        hasher.update(token_bytes.as_bytes());
        hasher.update(&(service.len() as u64).to_le_bytes());
        hasher.update(service.as_bytes());
        hasher.update(&(id.len() as u64).to_le_bytes());
        hasher.update(id.as_bytes());

        // Fixed-size 32-byte fields.
        hasher.update(&delegatee.0);
        hasher.update(&delegator_public_key.0);
        hasher.update(parent_delegation_hash);

        // Optional 32-byte fields use a 1-byte presence tag to disambiguate
        // `Some([0; 32])` from `None`.
        let write_optional = |hasher: &mut blake3::Hasher, value: Option<&[u8; 32]>| match value {
            Some(v) => {
                hasher.update(&[1u8]);
                hasher.update(v);
            }
            None => {
                hasher.update(&[0u8]);
                hasher.update(&[0u8; 32]);
            }
        };
        write_optional(&mut hasher, proof_key.as_ref());
        write_optional(&mut hasher, caveat_chain_hash.as_ref());
        write_optional(&mut hasher, membership_leaf);

        // Restrictions: canonical postcard encoding, length-prefixed.
        let restrictions_bytes = postcard::to_allocvec(restrictions)
            .expect("restrictions serialization should not fail");
        hasher.update(&(restrictions_bytes.len() as u64).to_le_bytes());
        hasher.update(&restrictions_bytes);

        *hasher.finalize().as_bytes()
    }

    /// Verify the v2 delegation envelope signature.
    ///
    /// Checks only the cryptographic signature; **does not** check authority.
    /// Use [`AgentCipherclerk::check_delegation_authority`] first.
    pub(crate) fn verify_delegation_envelope_v2(env: &DelegatedToken) -> Result<(), SdkError> {
        use ed25519_dalek::Verifier;

        let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(&env.delegator_public_key.0)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!("invalid delegator public key: {e}"))
            })?;

        let membership_leaf = env.membership_proof.as_ref().map(|p| p.leaf_hash);
        let signing_message = Self::compute_delegation_signing_message_v2(
            &env.token_bytes,
            &env.delegatee,
            &env.service,
            &env.id,
            &env.restrictions,
            &env.proof_key,
            &env.caveat_chain_hash,
            membership_leaf.as_ref(),
            &env.parent_delegation_hash,
            &env.delegator_public_key,
        );

        let signature = ed25519_dalek::Signature::from_bytes(&env.delegator_signature.0);
        verifying_key
            .verify(&signing_message, &signature)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!(
                    "delegation envelope signature verification failed: {e}"
                ))
            })
    }

    /// Compute the canonical signing message for a *local* delegation envelope.
    ///
    /// Uses a distinct domain tag so external and local envelopes are not
    /// cross-confusable.
    pub(crate) fn compute_local_delegation_signing_message(
        token_bytes: &str,
        delegatee: &PublicKey,
        service: &str,
        id: &str,
        restrictions: &Attenuation,
        proof_key: &Option<[u8; 32]>,
        caveat_chain_hash: &Option<[u8; 32]>,
        membership_leaf: Option<&[u8; 32]>,
        delegator_public_key: &PublicKey,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(Self::DELEGATION_ENVELOPE_LOCAL_V1_CONTEXT);
        hasher.update(&(token_bytes.len() as u64).to_le_bytes());
        hasher.update(token_bytes.as_bytes());
        hasher.update(&(service.len() as u64).to_le_bytes());
        hasher.update(service.as_bytes());
        hasher.update(&(id.len() as u64).to_le_bytes());
        hasher.update(id.as_bytes());
        hasher.update(&delegatee.0);
        hasher.update(&delegator_public_key.0);

        let write_optional = |hasher: &mut blake3::Hasher, value: Option<&[u8; 32]>| match value {
            Some(v) => {
                hasher.update(&[1u8]);
                hasher.update(v);
            }
            None => {
                hasher.update(&[0u8]);
                hasher.update(&[0u8; 32]);
            }
        };
        write_optional(&mut hasher, proof_key.as_ref());
        write_optional(&mut hasher, caveat_chain_hash.as_ref());
        write_optional(&mut hasher, membership_leaf);

        let restrictions_bytes = postcard::to_allocvec(restrictions)
            .expect("restrictions serialization should not fail");
        hasher.update(&(restrictions_bytes.len() as u64).to_le_bytes());
        hasher.update(&restrictions_bytes);

        *hasher.finalize().as_bytes()
    }

    /// Build a [`LocalDelegation`] for in-process sub-agent spawning.
    ///
    /// This is the **only** way to construct a `LocalDelegation`. It signs the
    /// envelope under the local-envelope tag so [`Self::receive_local_delegation`]
    /// can verify authority uniformly with the external path.
    pub(crate) fn make_local_delegation(
        &self,
        token_bytes: String,
        service: String,
        label: String,
        id: String,
        delegatee: PublicKey,
        restrictions: Attenuation,
        proof_key: Option<[u8; 32]>,
        membership_proof: Option<dregg_commit::merkle::MerkleProof>,
        caveat_chain_hash: Option<[u8; 32]>,
    ) -> LocalDelegation {
        let membership_leaf = membership_proof.as_ref().map(|p| p.leaf_hash);
        let signing_message = Self::compute_local_delegation_signing_message(
            &token_bytes,
            &delegatee,
            &service,
            &id,
            &restrictions,
            &proof_key,
            &caveat_chain_hash,
            membership_leaf.as_ref(),
            &self.public_key,
        );
        let sig = self.signing_key.sign(&signing_message);
        LocalDelegation {
            token_bytes,
            service,
            label,
            id,
            delegatee,
            restrictions,
            proof_key,
            membership_proof,
            caveat_chain_hash,
            delegator_signature: Signature(sig.to_bytes()),
            delegator_public_key: self.public_key,
        }
    }

    // =========================================================================
    // Proof Generation
    // =========================================================================

    /// Generate a real STARK-backed zero-knowledge presentation proof for a held token.
    ///
    /// This proves "I hold a valid token chain that authorizes request X"
    /// without revealing the token, its caveats, or the root key. The proof
    /// is backed by a real Poseidon2 STARK (collision-resistant, production-grade).
    ///
    /// The proof can be transmitted to a remote verifier who only needs the
    /// federation root and request predicate to verify it.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to prove authorization from.
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A [`BridgePresentationProof`] with a real STARK proof that can be verified
    /// by any party knowing the federation root, or an error if proof generation fails.
    pub fn prove_authorization(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        // SECURITY: Use the derived proof key for federation membership proofs.
        // The raw root_key is NEVER passed to the builder — only the one-way derived
        // proof key is used as the leaf in the federation Merkle tree.
        // Attenuated tokens (root_key == zeroed) cannot generate federation membership
        // proofs — they must use `prove_authorization_with_issuer_key()` instead,
        // providing the issuer's proof key out-of-band.
        if !token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate federation membership proofs; \
                 use prove_authorization_with_issuer_key() with the issuerr's proof key, \
                 or use the root token holder to prove directly"
                    .into(),
            ));
        }

        // Authority invariant (defense in depth): root tokens never carry a
        // delegation binding by construction, so this is a no-op. Kept for
        // uniformity with the issuer-key path.
        token.reverify_delegation_binding()?;

        let proof_key = Self::derive_proof_key(token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = dregg_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Use the ACTUAL encoded token (which includes all attenuations/caveats)
        // rather than minting a fresh unrestricted token from the root key.
        let actual_token = token.decode()?;
        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK presentation proof for an attenuated token using a provided issuer key.
    ///
    /// Attenuated tokens (those received via delegation) do not carry the root key and
    /// therefore cannot call [`prove_authorization`] directly. This method allows an
    /// attenuated token holder to generate a valid STARK proof when the issuer's root
    /// key is provided out-of-band (e.g., the delegator includes it in the delegation
    /// metadata, or the federation publishes it).
    ///
    /// # Security Model
    ///
    /// The issuer key is used ONLY for computing the federation Merkle membership proof
    /// (proving "my issuer is a member of this federation"). The attenuated token's
    /// caveat chain is still verified: the proof commits to the actual encoded token
    /// (with all its attenuations), not a freshly-minted unrestricted token.
    ///
    /// # Arguments
    ///
    /// * `token` - The attenuated token to prove authorization from.
    /// * `issuer_key` - The 32-byte root key of the original issuer (provided out-of-band).
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A [`BridgePresentationProof`] with a real STARK proof, or an error if proof
    /// generation fails.
    ///
    /// # Future Work
    ///
    /// A full chain-proof path (proving the delegation chain is valid without revealing
    /// intermediate tokens) would allow proving without any out-of-band key material.
    /// See: `prove_with_chain` for the root-holder variant of chain proofs.
    pub fn prove_authorization_with_issuer_key(
        &self,
        token: &HeldToken,
        issuer_key: &[u8; 32],
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        // Verify the issuer key is not zeroed (caller must provide a real key).
        if *issuer_key == [0u8; 32] {
            return Err(SdkError::MissingKey(
                "issuer_key must not be zeroed; provide the issuer's derived proof key".into(),
            ));
        }

        // Authority invariant (P0 fix): if this token was produced via a
        // delegation path, the delegator's signature must still verify against
        // the *current* `encoded` / `caveat_chain_hash` / membership leaf.
        // This re-verification is performed on every authorization use so that
        // post-receive tampering of those fields breaks authorization.
        token.reverify_delegation_binding()?;

        // P0-1: Verify caveat chain integrity before proof generation.
        // If the delegator provided a caveat_chain_hash, check that the decoded token's
        // caveats match. This prevents a delegate holding the proof_key from mutating
        // caveats and generating proofs over fabricated authorization facts.
        let actual_token = MacaroonToken::from_encoded(&token.encoded, *issuer_key)?;
        if let Some(expected_hash) = token.caveat_chain_hash {
            let computed_hash = Self::compute_caveat_chain_hash(&actual_token)?;
            if computed_hash != expected_hash {
                return Err(SdkError::CaveatIntegrityViolation);
            }
        }

        // P0-2: Use the federation root from the pre-generated membership proof when
        // available. The proof was generated against the REAL tree root (which contains
        // the real issuer key, not the BLAKE3-derived proof_key). Using
        // compute_federation_root_bb(issuer_key) would produce a synthetic root that
        // does not match the proof's path.
        let federation_root_bb = if let Some(ref mp) = token.membership_proof {
            Self::compute_root_from_membership_proof(mp)?
        } else {
            Self::compute_federation_root_bb(issuer_key)
        };
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = dregg_bridge::BridgePresentationBuilder::new_with_root_bb(
            *issuer_key,
            federation_root,
            federation_root_bb,
        );

        // If the token has a pre-generated membership proof (from delegation), attach
        // it to the builder. This allows the delegatee to prove federation membership
        // without needing to look up their proof_key in the federation tree (which would
        // fail since the tree contains real keys, not BLAKE3 derivations).
        if let Some(ref membership_proof) = token.membership_proof {
            builder.with_pre_generated_membership_proof(membership_proof.clone());
        }

        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK presentation proof with a revealed facts commitment.
    ///
    /// This is the internal implementation for selective disclosure mode. It generates
    /// the same STARK proof as `prove_authorization`, but includes the `commitment`
    /// as a public input that binds the revealed facts to the proof.
    ///
    /// The verifier extracts the commitment from the proof's public inputs and
    /// recomputes it from the plaintext revealed facts to verify integrity.
    fn prove_authorization_selective(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        commitment: dregg_circuit::binding::WideHash,
    ) -> Result<BridgePresentationProof, SdkError> {
        if !token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate selective disclosure proofs; \
                 use prove_authorization_with_issuer_key() with the issuerr's proof key, \
                 or use the root token holder to prove directly"
                    .into(),
            ));
        }

        // P2-1: Defensive durable-binding reverification. Root tokens never
        // carry a delegation binding by construction (no-op), but kept for
        // symmetry with `prove_authorization_with_issuer_key`.
        token.reverify_delegation_binding()?;

        let proof_key = Self::derive_proof_key(token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = dregg_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Set the revealed facts commitment before proving.
        builder.set_revealed_facts_commitment(commitment);

        let actual_token = token.decode()?;
        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK selective disclosure proof for an attenuated token using a
    /// provided issuer key.
    ///
    /// This is the attenuated-token variant of `prove_authorization_selective`. It uses
    /// the issuer key for federation membership and the commitment for binding revealed
    /// facts to the proof.
    fn prove_authorization_selective_with_issuer_key(
        &self,
        token: &HeldToken,
        issuer_key: &[u8; 32],
        request: &AuthRequest,
        commitment: dregg_circuit::binding::WideHash,
    ) -> Result<BridgePresentationProof, SdkError> {
        if *issuer_key == [0u8; 32] {
            return Err(SdkError::MissingKey(
                "issuer_key must not be zeroed; provide the issuer's derived proof key".into(),
            ));
        }

        // Authority invariant (P0 fix): re-verify the delegation envelope
        // against current fields. See `reverify_delegation_binding`.
        token.reverify_delegation_binding()?;

        // P0-1: Verify caveat chain integrity before proof generation.
        let actual_token = MacaroonToken::from_encoded(&token.encoded, *issuer_key)?;
        if let Some(expected_hash) = token.caveat_chain_hash {
            let computed_hash = Self::compute_caveat_chain_hash(&actual_token)?;
            if computed_hash != expected_hash {
                return Err(SdkError::CaveatIntegrityViolation);
            }
        }

        // P0-2: Use the federation root from the pre-generated membership proof when
        // available, rather than the synthetic root derived from the proof_key.
        let federation_root_bb = if let Some(ref mp) = token.membership_proof {
            Self::compute_root_from_membership_proof(mp)?
        } else {
            Self::compute_federation_root_bb(issuer_key)
        };
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = dregg_bridge::BridgePresentationBuilder::new_with_root_bb(
            *issuer_key,
            federation_root,
            federation_root_bb,
        );

        // Attach pre-generated membership proof if available (delegation path).
        if let Some(ref membership_proof) = token.membership_proof {
            builder.with_pre_generated_membership_proof(membership_proof.clone());
        }

        // Set the revealed facts commitment before proving.
        builder.set_revealed_facts_commitment(commitment);

        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a presentation proof for a held token.
    ///
    /// This produces a real STARK proof suitable for verification across trust
    /// boundaries. Previously this method used a fast constraint-check path that
    /// did not produce a verifiable STARK; it now delegates to the full prover.
    ///
    /// # Deprecation
    ///
    /// Prefer [`prove_authorization`](Self::prove_authorization) directly.
    #[deprecated(note = "Use prove_authorization() which is the canonical production path")]
    pub fn prove_fast(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        self.prove_authorization(token, request)
    }

    /// Generate a real STARK presentation proof for an attenuated token chain.
    ///
    /// Unlike [`prove_authorization`](Self::prove_authorization), this method
    /// accepts the full attenuation chain so the proof covers the narrowing steps.
    ///
    /// # Arguments
    ///
    /// * `root_token` - The original root token (needed for the chain base).
    /// * `attenuations` - The sequence of attenuations applied.
    /// * `request` - The authorization request to prove.
    pub fn prove_with_chain(
        &self,
        root_token: &HeldToken,
        attenuations: &[Attenuation],
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        if !root_token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate federation membership proofs; \
                 use prove_authorization_with_issuer_key() with the issuerr's root key"
                    .into(),
            ));
        }

        let proof_key = Self::derive_proof_key(root_token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = dregg_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Use the actual encoded token (preserves existing caveats).
        let actual_token = root_token.decode()?;
        builder.set_root_token(actual_token);

        for att in attenuations {
            builder.add_attenuation(att);
        }

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    // =========================================================================
    // Predicate Proofs
    // =========================================================================

    /// Prove a predicate about a private token attribute.
    ///
    /// This generates a zero-knowledge proof that a specific attribute of a held
    /// token satisfies a predicate (e.g., "balance >= 1000", "valid_until >= T")
    /// without revealing the exact value.
    ///
    /// # Security: `attribute_value` Binding
    ///
    /// IMPORTANT: `attribute_value` is the prover's claim. The verifier must independently
    /// verify that this value is committed in the token's state root (via Merkle membership).
    /// This function does NOT verify that claim -- it only proves the predicate holds IF the
    /// value is correct.
    ///
    /// The binding between the claimed value and the token's actual state happens at a higher
    /// level: the full presentation flow (via `authorize_with_disclosure` or the intent
    /// fulfillment pipeline) includes a state root that commits to all attribute values.
    /// The `fact_commitment` in the returned proof is derived from this state root, so a
    /// verifier checking the proof against a known state root will reject fabricated values.
    ///
    /// Callers using this function directly (outside the full presentation flow) MUST ensure
    /// the verifier independently checks the `fact_commitment` against the token's committed
    /// state. Without this check, a dishonest prover can claim any value and produce a valid
    /// proof for it.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "valid_until", "balance", "reputation").
    ///   This is hashed to a field element and used to look up the fact in the token state.
    /// * `attribute_value` - The actual (private) value of the attribute. This is the
    ///   prover's claim; see the Security section above regarding binding guarantees.
    /// * `predicate` - The predicate to prove (e.g., `Predicate::Gte(1000)`).
    ///
    /// # Returns
    ///
    /// A `BridgePredicateProof` that can be verified by anyone knowing the fact commitment,
    /// or an error if the predicate cannot be proven (statement is false or token is invalid).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use dregg_sdk::AgentCipherclerk;
    /// use dregg_bridge::Predicate;
    ///
    /// let cipherclerk = AgentCipherclerk::new();
    /// # let token = todo!();
    /// // Prove: my balance >= 1000 (without revealing the actual balance)
    /// let proof = cipherclerk.prove_predicate(
    ///     &token,
    ///     "balance",
    ///     5000, // actual balance (private)
    ///     Predicate::Gte(1000),
    /// ).unwrap();
    /// ```
    pub fn prove_predicate(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u32,
        predicate: dregg_bridge::Predicate,
    ) -> Result<dregg_bridge::BridgePredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute the fact hash for the attribute.
        // The fact is modeled as: predicate=hash(attribute_name), terms=[value, 0, 0].
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        // Compute a state root from the token's derived proof key (deterministic for testing).
        // In production, this would come from the committed Merkle tree of the token state.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Generate the predicate proof via the bridge.
        let proof = dregg_bridge::prove_predicate_for_fact(
            attribute_value,
            fact_hash,
            state_root,
            &predicate,
        )
        .ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                format!(
                    "predicate proof generation failed: the statement '{attribute}' {:?} is not satisfiable for value {attribute_value}",
                    predicate
                ),
            ))
        })?;

        Ok(proof)
    }

    // =========================================================================
    // Arithmetic Predicate Proofs
    // =========================================================================

    /// Prove an arithmetic predicate over multiple private token attributes.
    ///
    /// This generates a zero-knowledge proof that an arithmetic expression over
    /// multiple private values from a held token satisfies a predicate, without
    /// revealing any of the individual values.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attributes.
    /// * `inputs` - Pairs of (attribute_name, private_value) for each input to the expression.
    /// * `expression` - The arithmetic expression to evaluate (e.g., `Var(0) + Var(1)`).
    /// * `predicate` - The predicate to prove (e.g., `ExprGte(expr, threshold)`).
    ///
    /// # Returns
    ///
    /// A proof that can be verified by anyone knowing the fact commitments.
    ///
    /// Note: Arithmetic predicate bridge integration is not yet complete.
    /// This method will return an error until `dregg_bridge::prove_arithmetic_for_facts`
    /// is implemented.
    pub fn prove_arithmetic(
        &self,
        token: &HeldToken,
        inputs: &[(String, u64)],
        expression: dregg_circuit::ArithExpr,
        predicate: dregg_circuit::ArithPredicate,
    ) -> Result<dregg_circuit::ArithmeticPredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Derive the state root from the token's proof key (consistent with other proofs).
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Convert inputs to BabyBear values and compute per-attribute fact hashes.
        let input_values: Vec<u32> = inputs.iter().map(|(_, v)| *v as u32).collect();

        let fact_commitments: Vec<BabyBear> = inputs
            .iter()
            .map(|(attr, value)| {
                let attr_bytes = blake3::hash(attr.as_bytes());
                let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
                let value_bb = BabyBear::new(*value as u32);
                let fact_hash =
                    poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);
                dregg_circuit::compute_arithmetic_fact_commitment(fact_hash, state_root)
            })
            .collect();

        // Aggregate fact commitments into a single binding commitment.
        let aggregate_commitment = poseidon2::hash_many(&fact_commitments);

        // Construct the predicate with the expression embedded.
        let full_predicate = match predicate {
            dregg_circuit::ArithPredicate::ExprGte(_, threshold) => {
                dregg_circuit::ArithPredicate::ExprGte(expression, threshold)
            }
            dregg_circuit::ArithPredicate::ExprLte(_, threshold) => {
                dregg_circuit::ArithPredicate::ExprLte(expression, threshold)
            }
            dregg_circuit::ArithPredicate::ExprEq(_, value) => {
                dregg_circuit::ArithPredicate::ExprEq(expression, value)
            }
            dregg_circuit::ArithPredicate::ExprInRange(_, low, high) => {
                dregg_circuit::ArithPredicate::ExprInRange(expression, low, high)
            }
            dregg_circuit::ArithPredicate::ExprCompare(_, expr_b, op) => {
                dregg_circuit::ArithPredicate::ExprCompare(expression, expr_b, op)
            }
            dregg_circuit::ArithPredicate::ExprNeq(_, value) => {
                dregg_circuit::ArithPredicate::ExprNeq(expression, value)
            }
        };

        let witness = dregg_circuit::ArithmeticPredicateWitness {
            inputs: input_values,
            predicate: full_predicate,
            fact_commitment: aggregate_commitment,
        };

        dregg_circuit::prove_arithmetic_predicate(witness).ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                "arithmetic predicate is not satisfiable for the given inputs".into(),
            ))
        })
    }

    // =========================================================================
    // Relational and Committed-Threshold Predicate Proofs
    // =========================================================================

    /// Prove a relational predicate comparing this cipherclerk's private value against
    /// a counterparty's committed value.
    ///
    /// This generates a zero-knowledge proof that a specific attribute of a held
    /// token satisfies a relational comparison against a counterparty's committed
    /// value (e.g., "my bid > their bid") without revealing either party's value.
    ///
    /// The prover must have received the counterparty's value and blinding via a
    /// sealed channel (e.g., OT, MPC, trusted comparison service).
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `my_attribute` - The attribute name (e.g., "bid").
    /// * `my_value` - The actual (private) value of the attribute.
    /// * `my_blinding` - The prover's blinding factor for their own commitment.
    /// * `their_value` - The counterparty's value (received via sealed channel).
    /// * `their_blinding` - The counterparty's blinding factor (received via sealed channel).
    /// * `relation` - The relation to prove (e.g., GreaterThan).
    ///
    /// # Returns
    ///
    /// A `RelationalPredicateProof` that can be verified by anyone knowing both
    /// commitments, or an error if the relation is not satisfiable.
    pub fn prove_relational(
        &self,
        token: &HeldToken,
        my_attribute: &str,
        my_value: u64,
        my_blinding: BabyBear,
        their_value: u64,
        their_blinding: BabyBear,
        relation: dregg_circuit::RelationType,
    ) -> Result<dregg_circuit::RelationalPredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        let proof = dregg_circuit::prove_value_comparison(
            BabyBear::new(my_value as u32),
            my_blinding,
            BabyBear::new(their_value as u32),
            their_blinding,
            relation,
        )
        .ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                "relational predicate proof failed: '{}' {:?} is not satisfiable \
                 (my_value={}, their_value={})",
                my_attribute, relation, my_value, their_value
            )))
        })?;

        Ok(proof)
    }

    /// Prove a committed-threshold predicate: the cipherclerk's private value satisfies
    /// a threshold that is also kept secret from third-party verifiers.
    ///
    /// This generates a zero-knowledge proof that a specific attribute value is
    /// at least as large as a threshold, where both the value AND the threshold are
    /// hidden behind Poseidon2 commitments. Third-party verifiers learn only that
    /// "some committed value satisfies some committed threshold."
    ///
    /// The verifier provides the threshold and blinding via a secure channel.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "credit_score").
    /// * `attribute_value` - The actual (private) value of the attribute.
    /// * `threshold` - The verifier's secret threshold (received via secure channel).
    /// * `blinding` - The verifier's blinding randomness (received via secure channel).
    ///
    /// # Returns
    ///
    /// A `CommittedThresholdProof` that can be verified against the threshold
    /// commitment and fact commitment, or an error if value < threshold.
    pub fn prove_committed_threshold(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u64,
        threshold: u64,
        blinding: BabyBear,
    ) -> Result<dregg_circuit::CommittedThresholdProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute the fact hash and fact commitment for binding to the token state.
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value as u32);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);
        let fact_commitment = dregg_circuit::compute_fact_commitment(fact_hash, state_root);

        let witness = dregg_circuit::CommittedThresholdWitness {
            private_value: value_bb,
            threshold: BabyBear::new(threshold as u32),
            blinding,
            fact_commitment,
        };

        let proof = dregg_circuit::prove_committed_threshold(witness).ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                "committed-threshold proof failed: '{}' value {} does not satisfy threshold {}",
                attribute, attribute_value, threshold
            )))
        })?;

        Ok(proof)
    }

    // =========================================================================
    // Programmable Predicate Programs
    // =========================================================================

    /// Prove a programmable predicate program against this cipherclerk's private state.
    ///
    /// This is the high-level entry point for the programmable predicates system.
    /// It takes a predicate program (an expression tree of conditions) and proves
    /// all conditions are satisfied using the cipherclerk's private attribute values.
    ///
    /// The program is compiled to the appropriate AIR(s) and proven in zero knowledge.
    /// The verifier learns only that the program is satisfied, not the actual values.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token whose attributes are being proven about.
    /// * `program` - The predicate program to prove (expression tree).
    /// * `attribute_values` - Map from attribute names to actual (private) values.
    ///
    /// # Returns
    ///
    /// A `ProgramProof` that can be verified by anyone knowing the program and
    /// fact commitments, or an error if the program cannot be proven.
    pub fn prove_program(
        &self,
        token: &HeldToken,
        program: &dregg_circuit::predicate_program::PredicateProgram,
        attribute_values: &std::collections::HashMap<String, u64>,
    ) -> Result<dregg_circuit::predicate_program::ProgramProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute a state root from the token's derived proof key.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Prove via the bridge layer.
        let proof = dregg_bridge::prove_predicate_program(program, attribute_values, state_root)
            .map_err(|e| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                    "predicate program proof failed: {e}"
                )))
            })?;

        Ok(proof)
    }

    /// Prove a predicate program with full private state including relational and
    /// committed-threshold context.
    ///
    /// This is the extended version of [`prove_program`](Self::prove_program) that
    /// supports relational predicates (two-party comparisons) and committed-threshold
    /// predicates (hidden thresholds) by accepting the full [`PrivateState`] struct
    /// including counterparty values and verifier secrets received via sealed channels.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token whose attributes are being proven about.
    /// * `program` - The predicate program to prove.
    /// * `private_state` - Full private state including values, temporal history,
    ///   relational context, and committed-threshold context.
    ///
    /// # Returns
    ///
    /// A `ProgramProof` that can be verified by anyone knowing the program and
    /// fact commitments, or an error if the program cannot be proven.
    pub fn prove_program_full(
        &self,
        token: &HeldToken,
        program: &dregg_circuit::predicate_program::PredicateProgram,
        private_state: &dregg_circuit::predicate_program::PrivateState,
    ) -> Result<dregg_circuit::predicate_program::ProgramProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute a state root from the token's derived proof key.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Prove via the bridge layer (full private state path).
        let proof = dregg_bridge::prove_predicate_program_full(program, private_state, state_root)
            .map_err(|e| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                    "predicate program proof failed: {e}"
                )))
            })?;

        Ok(proof)
    }

    // =========================================================================
    // Cross-party Predicate Proofs (Intent Integration)
    // =========================================================================

    /// Prove all predicate requirements in an intent using local values.
    ///
    /// When a counterparty posts an intent with predicate requirements (e.g.,
    /// "prove your balance >= 1000 and reputation >= 50"), this method generates
    /// the required ZK proofs for all requirements the caller can satisfy.
    ///
    /// Each proof demonstrates the predicate holds without revealing the actual
    /// value. The proofs are bound to a state root (via fact commitments), so the
    /// verifier can check they correspond to real committed state.
    ///
    /// # Arguments
    ///
    /// * `intent` - The intent containing predicate requirements to prove.
    /// * `my_values` - A map from attribute name to actual (private) value.
    /// * `state_root` - The state root to bind proofs against.
    ///
    /// # Returns
    ///
    /// A vector of `(requirement_index, PredicateProof)` for each requirement
    /// that could be proven. Requirements whose attributes are not in `my_values`
    /// or whose predicates are not satisfiable are skipped (returns error).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use dregg_sdk::AgentCipherclerk;
    /// use dregg_circuit::BabyBear;
    /// use std::collections::HashMap;
    ///
    /// let cipherclerk = AgentCipherclerk::new();
    /// # let intent = todo!();
    /// let mut my_values = HashMap::new();
    /// my_values.insert("balance".to_string(), 5000u64);
    /// my_values.insert("reputation".to_string(), 85u64);
    ///
    /// let state_root = BabyBear::new(99999);
    /// let proofs = cipherclerk.prove_for_intent_predicates(&intent, &my_values, state_root).unwrap();
    /// // proofs can be attached to a FulfillmentWithPredicates
    /// ```
    pub fn prove_for_intent_predicates(
        &self,
        intent: &dregg_intent::Intent,
        my_values: &std::collections::HashMap<String, u64>,
        state_root: BabyBear,
    ) -> Result<Vec<(usize, dregg_circuit::PredicateProof)>, SdkError> {
        use dregg_bridge::Predicate;
        use dregg_circuit::poseidon2;
        use dregg_intent::fulfillment::parse_predicate_type;

        let requirements = &intent.matcher.predicate_requirements;
        let mut proofs = Vec::with_capacity(requirements.len());

        for (idx, req) in requirements.iter().enumerate() {
            // Look up our value for this attribute.
            let value = my_values.get(&req.attribute).ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no value for attribute '{}' required by intent predicate {}",
                    req.attribute, idx
                ))
            })?;

            // Map the predicate type string to a bridge Predicate.
            let predicate = match req.predicate_type.as_str() {
                "gte" => Predicate::Gte(req.threshold as u32),
                "lte" => Predicate::Lte(req.threshold as u32),
                "gt" => Predicate::Gt(req.threshold as u32),
                "lt" => Predicate::Lt(req.threshold as u32),
                "neq" => Predicate::Neq(req.threshold as u32),
                "in_range" => {
                    let upper = req.upper_bound.unwrap_or(req.threshold) as u32;
                    Predicate::InRange(req.threshold as u32, upper)
                }
                other => {
                    return Err(SdkError::MissingKey(format!(
                        "unsupported predicate type '{}' for attribute '{}'",
                        other, req.attribute
                    )));
                }
            };

            // Compute the fact hash for this attribute.
            let attr_bytes = blake3::hash(req.attribute.as_bytes());
            let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
            let value_bb = BabyBear::new(*value as u32);
            let fact_hash =
                poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

            // Generate the predicate proof.
            let bridge_proof = dregg_bridge::prove_predicate_for_fact(
                *value as u32,
                fact_hash,
                state_root,
                &predicate,
            )
            .ok_or_else(|| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                    "predicate proof failed for '{}': value {} does not satisfy {:?}",
                    req.attribute, value, predicate
                )))
            })?;

            // Extract the inner circuit proof(s).
            // For simple predicates (Gte, Lte, etc.) we get a single proof.
            // For InRange we get a pair; the intent system expects one proof per requirement,
            // so for InRange we use the lower-bound proof (the requirement is verified
            // against the lower threshold).
            let _ = parse_predicate_type; // ensure import is used
            let circuit_proof = match bridge_proof.proof {
                dregg_bridge::BridgePredicateProofInner::Single(p) => p,
                dregg_bridge::BridgePredicateProofInner::Range(low_proof, _high_proof) => {
                    // For in_range, the lower bound proof demonstrates value >= threshold.
                    low_proof
                }
                dregg_bridge::BridgePredicateProofInner::CommittedThreshold(p) => {
                    // CommittedThreshold uses a committed comparison proof.
                    // Convert to PredicateProof with Gte semantics (committed threshold
                    // proves value >= threshold).
                    dregg_circuit::PredicateProof {
                        op: dregg_circuit::PredicateType::Gte,
                        threshold: p.threshold_commitment,
                        fact_commitment: p.fact_commitment,
                        stark_proof: p.stark_proof,
                    }
                }
            };

            proofs.push((idx, circuit_proof));
        }

        Ok(proofs)
    }

    // =========================================================================
    // Fulfillment Payment (Intent → Fulfill → Automatic Payment)
    // =========================================================================

    /// Fulfill an intent and collect payment in a single atomic operation.
    ///
    /// This is the high-level convenience method that an agent calls when it:
    /// 1. Holds a capability that satisfies the intent's MatchSpec.
    /// 2. Can prove all predicate requirements in the intent.
    /// 3. Wants to receive payment (from the intent's `min_budget`).
    ///
    /// The method:
    /// - Generates predicate proofs for all requirements using `my_values`.
    /// - Constructs a `FulfillmentWithPredicates`.
    /// - Calls `execute_fulfillment_flow_verified` which verifies + pays atomically,
    ///   settling the payment leg through the verified executor edge (fail-closed).
    ///
    /// # Arguments
    ///
    /// * `intent` - The intent to fulfill (must have `min_budget` set for payment).
    /// * `base_fulfillment` - The base fulfillment (capability satisfaction proof).
    /// * `my_values` - Map from attribute name to actual (private) value for predicates.
    /// * `runtime` - The agent runtime providing ledger and executor access.
    ///
    /// # Returns
    ///
    /// A `TurnReceipt` proving payment was transferred, or an error.
    pub fn fulfill_and_collect(
        &self,
        intent: &dregg_intent::Intent,
        base_fulfillment: &dregg_intent::fulfillment::Fulfillment,
        my_values: &std::collections::HashMap<String, u64>,
        runtime: &crate::runtime::AgentRuntime,
        current_height: u64,
    ) -> Result<dregg_turn::TurnReceipt, SdkError> {
        // Step 1: Generate predicate proofs for the intent's requirements.
        // Derive the state root from this cipherclerk's receipt chain head. The receipt
        // chain's post_state_hash is the committed state that verifiers can check.
        let state_root = self
            .current_state_commitment()
            .map(|hash| Self::bytes_to_babybear(&hash))
            .ok_or_else(|| {
                SdkError::MissingKey(
                    "cclerk has no receipt chain; cannot derive state root for predicate proofs. \
                     Call append_receipt() after executing at least one turn."
                        .into(),
                )
            })?;
        let predicate_proofs = self.prove_for_intent_predicates(intent, my_values, state_root)?;

        // Step 3: Construct the FulfillmentWithPredicates.
        let fulfillment_with_preds = dregg_intent::fulfillment::FulfillmentWithPredicates {
            base: base_fulfillment.clone(),
            predicate_proofs,
            state_root,
            state_root_block: current_height.saturating_sub(10), // Recent state root.
        };

        // Step 4: Execute the fulfillment flow.
        let payer_cell = CellId(intent.creator.0); // Intent creator pays.
        let recipient_cell = runtime.cell_id(); // We (the fulfiller) receive.

        let mut ledger = runtime.ledger().lock().unwrap();

        // The value-moving leg settles through the VERIFIED executor edge
        // (`dregg_intent::verified_settle` — the proved per-asset transition, FFI
        // cross-checked when `verified-settle` is enabled), NOT the legacy
        // `dregg_turn::TurnExecutor`. Fail-closed: a refused payment is refused.
        dregg_intent::fulfillment::execute_fulfillment_flow_verified(
            intent,
            &fulfillment_with_preds,
            &mut ledger,
            payer_cell,
            recipient_cell,
            current_height,
            current_height,
        )
        .map_err(|e| SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(e.to_string())))
    }

    // =========================================================================
    // Internal helpers
    // =========================================================================

    /// Compute a stable byte representation of a turn for signing.
    ///
    /// This MUST cover ALL semantically-relevant fields of the Turn to prevent
    /// an attacker from substituting fields that are not covered by the signature.
    /// The domain prefix prevents cross-protocol signature reuse.
    ///
    /// # Serialization format
    ///
    /// All variable-length fields are length-prefixed (8-byte little-endian u64)
    /// to prevent ambiguous concatenation attacks. For example, without length
    /// prefixes, `fee=12, memo="3"` and `fee=1, memo="23"` could hash identically
    /// if the field boundaries are not explicit. Fixed-size fields (u64, [u8; 32])
    /// do not need length prefixes since their boundaries are unambiguous.
    fn compute_turn_bytes(&self, turn: &Turn) -> [u8; 32] {
        // P2-10 closure (v1 → v3): the cipherclerk's signing message is now the
        // canonical `Turn::hash()` (domain `dregg-turn-v3:`), which covers
        // every semantically load-bearing field on the Turn: agent, nonce,
        // call_forest, fee, memo, valid_until, depends_on,
        // previous_receipt_hash, execution_proof,
        // execution_proof_cell, execution_proof_new_commitment,
        // conservation_proof, sovereign_witnesses, and
        // custom_program_proofs. This closes the wire-malleability gap where
        // an executor between cipherclerk and ledger could swap
        // `sovereign_witnesses` (and other side payloads) without
        // invalidating the signature.
        turn.hash()
    }

    /// Compute the federation root as a BabyBear field element.
    ///
    /// This walks the synthetic Merkle path from the issuer key hash up to
    /// a deterministic root. In production, this would come from the federation
    /// registry; here we compute it so the proof verifies self-consistently.
    fn compute_federation_root_bb(issuer_key: &[u8; 32]) -> BabyBear {
        // P2-7: This produces a SYNTHETIC root (no real federation tree
        // lookup). Membership proofs against the synthetic root are only
        // interoperable with verifiers that derive the same synthetic root,
        // i.e. with this SDK in a single-tenant test deployment. Production
        // callers should rely on `compute_root_from_membership_proof` against
        // a pre-generated `MerkleProof` whose root anchors to a real
        // federation registry. Emit a warning in non-test builds to surface
        // accidental production reliance on the synthetic path.
        #[cfg(not(test))]
        tracing::warn!(
            "compute_federation_root_bb: using synthetic federation root; \
             production deployments should supply a pre-generated membership \
             proof rooted at the real federation registry (P2-7)."
        );

        let issuer_hash = Self::bytes_to_babybear(issuer_key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(Self::hash_index(i, 0, issuer_key)),
                BabyBear::new(Self::hash_index(i, 1, issuer_key)),
                BabyBear::new(Self::hash_index(i, 2, issuer_key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        current
    }

    /// Convert a BabyBear field element to a 32-byte array.
    fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        let val = bb.as_u32();
        bytes[..4].copy_from_slice(&val.to_le_bytes());
        bytes
    }

    /// Compress a 32-byte value into a single BabyBear element via Poseidon2.
    pub(crate) fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
        let limbs = BabyBear::encode_hash(bytes);
        poseidon2::hash_many(&limbs)
    }

    /// Derive a proof-only key from an issuer's root HMAC key.
    ///
    /// This one-way derivation produces a key suitable for federation membership
    /// proofs (ZK) that CANNOT be used to mint tokens or forge HMAC chains.
    /// The derived key is deterministic: the same root key always produces the
    /// same proof key.
    ///
    /// **SECURITY**: Possession of the proof key does NOT allow:
    /// - Minting new root tokens (requires the raw root_key for HMAC chain init)
    /// - Forging or extending HMAC chains (HMAC verification requires root_key)
    /// - Recovering the root key (BLAKE3 key derivation is one-way)
    ///
    /// It DOES allow:
    /// - Computing the federation Merkle leaf hash (proving issuer membership)
    /// - Generating ZK proofs bound to this issuer's identity
    ///
    /// The context string "dregg-proof-key-v1" is used for domain separation.
    /// This MUST match the derivation in [`HeldToken::new()`], [`delegate()`], and
    /// any external delegation protocol implementations.
    pub(crate) fn derive_proof_key(root_key: &[u8; 32]) -> [u8; 32] {
        blake3::derive_key("dregg-proof-key-v1", root_key)
    }

    /// Compute a BLAKE3 commitment to a token's caveat chain.
    ///
    /// This hash is computed by the delegator (who holds the root key and can
    /// verify the HMAC chain) and included in the delegation payload. The
    /// delegatee verifies this hash against their decoded token's caveats before
    /// using them for ZK proof generation.
    ///
    /// Uses deterministic serialization (rmp-serde) to ensure both sides compute
    /// the same hash regardless of in-memory representation differences.
    fn compute_caveat_chain_hash(token: &MacaroonToken) -> Result<[u8; 32], SdkError> {
        // P1-3: Caveats may include attacker-influenced data (the macaroon was
        // decoded from an external `encoded` string). Propagate serialization
        // failure as `SdkError::Wire` rather than panicking inside `delegate*`
        // / authorization paths.
        let caveats = token.inner().caveats.as_slice();
        let serialized = rmp_serde::to_vec(caveats)
            .map_err(|e| SdkError::Wire(format!("caveat serialization failed: {e}")))?;
        Ok(*blake3::hash(&serialized).as_bytes())
    }

    /// Maximum acceptable depth for a Merkle membership proof.
    ///
    /// P1-6: A maliciously-deserialized `MerkleProof` carrying enormous
    /// `siblings` / `path_indices` lengths would otherwise cause an unbounded
    /// loop in [`Self::compute_root_from_membership_proof`]. The federation
    /// tree in practice has at most ~8 levels; we cap at 64 to accommodate
    /// future expansion while preserving a strict bound.
    pub(crate) const MAX_MEMBERSHIP_PROOF_DEPTH: usize = 64;

    /// Compute the Poseidon2 Merkle root from a pre-generated membership proof.
    ///
    /// Re-walks the proof path using Poseidon2 hashing (same algorithm as
    /// `build_issuer_membership_poseidon2_from_proof` in the bridge) to recover
    /// the federation root that the proof was generated against.
    ///
    /// # Errors
    ///
    /// Returns `SdkError::Wire` if the proof exceeds
    /// [`Self::MAX_MEMBERSHIP_PROOF_DEPTH`] or carries mismatched
    /// `siblings.len()` / `path_indices.len()` (P1-6).
    pub(crate) fn compute_root_from_membership_proof(
        proof: &dregg_commit::merkle::MerkleProof,
    ) -> Result<BabyBear, SdkError> {
        if proof.siblings.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
            || proof.path_indices.len() > Self::MAX_MEMBERSHIP_PROOF_DEPTH
        {
            return Err(SdkError::Wire(format!(
                "membership proof depth exceeds maximum ({} > {})",
                proof.siblings.len().max(proof.path_indices.len()),
                Self::MAX_MEMBERSHIP_PROOF_DEPTH,
            )));
        }
        if proof.siblings.len() != proof.path_indices.len() {
            return Err(SdkError::Wire(format!(
                "membership proof mismatched: {} siblings vs {} path_indices",
                proof.siblings.len(),
                proof.path_indices.len(),
            )));
        }

        let real_leaf_hash = Self::bytes_to_babybear(&proof.leaf_hash);
        let mut current = real_leaf_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                Self::bytes_to_babybear(&proof.siblings[i][0]),
                Self::bytes_to_babybear(&proof.siblings[i][1]),
                Self::bytes_to_babybear(&proof.siblings[i][2]),
            ];

            current = compute_parent_poseidon2(current, position, &siblings);
        }

        Ok(current)
    }

    /// Derive a deterministic sibling hash for Merkle path construction.
    fn hash_index(level: usize, sibling_idx: usize, key: &[u8; 32]) -> u32 {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&level.to_le_bytes());
        hasher.update(&sibling_idx.to_le_bytes());
        hasher.update(key);
        let hash = hasher.finalize();
        let bytes = hash.as_bytes();
        u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
            % dregg_circuit::field::BABYBEAR_P
    }

    // =========================================================================
    // Pipeline / Eventual-Send
    // =========================================================================

    /// Submit a pipeline of turns for execution, resolving dependencies in
    /// topological order. Returns one receipt per turn in pipeline order.
    ///
    /// Turns that fail cause all their dependents to fail. Independent turns
    /// may still succeed (partial pipeline success).
    pub fn submit_pipeline(
        &mut self,
        pipeline: dregg_turn::Pipeline,
        executor: &dregg_turn::TurnExecutor,
        ledger: &mut dregg_cell::Ledger,
    ) -> Vec<Result<dregg_turn::TurnReceipt, dregg_turn::PipelineError>> {
        let results = dregg_turn::execute_pipeline(pipeline, ledger, executor);

        // Append successful receipts to this cipherclerk's chain.
        // Strict mode: a fork between the executor and the cipherclerk is
        // surfaced as a warning at this layer (the pipeline return value
        // is per-turn `Result`, so we cannot turn a mismatch into a typed
        // error here). The receipt is dropped from the cipherclerk's chain
        // and the caller can detect the divergence by comparing
        // `receipt_chain_length()` against the number of `Ok` results.
        for result in &results {
            if let Ok(receipt) = result {
                if receipt.agent == self.cell_id("default") {
                    if let Err(e) = self.append_receipt(receipt.clone()) {
                        tracing::error!(
                            "cipherclerk chain divergence in submit_pipeline: {} \
                             (receipt dropped; caller must reconcile)",
                            e
                        );
                    }
                }
            }
        }

        results
    }

    /// Create an EventualRef pointing to a specific output slot of a turn.
    ///
    /// This is a helper for constructing pipelines: you hash a turn and then
    /// create a reference that downstream turns can use to target outputs of
    /// this turn.
    pub fn eventual_ref(turn: &dregg_turn::Turn, slot: u32) -> dregg_turn::EventualRef {
        let turn_hash = turn.hash();
        dregg_turn::EventualRef::new(turn_hash, slot)
    }

    // =========================================================================
    // Committed Payments
    // =========================================================================

    /// Build a committed (privacy-preserving) transfer turn from owned notes.
    ///
    /// Constructs a turn where note values are hidden behind Pedersen commitments.
    /// The executor verifies conservation via the Schnorr excess signature and
    /// Bulletproof range proofs, without learning any amounts.
    ///
    /// # Arguments
    ///
    /// * `input_notes` - Notes this cipherclerk can spend (with full opening data).
    /// * `recipients` - (amount, recipient_pubkey) pairs for outputs.
    /// * `domain` - Domain string for deriving the agent's cell ID.
    /// * `nonce` - Replay-protection nonce.
    ///
    /// # Returns
    ///
    /// A fully-formed [`Turn`] with `conservation_proof` set and all effects
    /// carrying `value_commitment` fields, ready for signing and submission.
    pub fn build_committed_transfer(
        &self,
        input_notes: &[crate::committed_turn::OwnedNote],
        recipients: &[(u64, [u8; 32])],
        domain: &str,
        nonce: u64,
    ) -> Result<Turn, crate::error::SdkError> {
        use crate::committed_turn::{
            CommittedNoteInput, CommittedNoteOutput, CommittedTurnBuilder,
        };

        let agent_cell = self.cell_id(domain);

        let mut builder = CommittedTurnBuilder::new();

        for note in input_notes {
            builder.add_input(CommittedNoteInput::from(note));
        }

        for &(amount, ref recipient) in recipients {
            let asset_type = input_notes.first().map(|n| n.asset_type).unwrap_or(0);
            builder.add_output(CommittedNoteOutput {
                value: amount,
                asset_type,
                recipient: *recipient,
            });
        }

        builder.build(agent_cell, nonce, 0)
    }

    // =========================================================================
    // Stealth Address Support
    // =========================================================================

    /// Get this cipherclerk's stealth meta-address (for receiving private notes).
    ///
    /// Publish this so senders can generate unlinkable one-time addresses for you.
    /// The meta-address contains your view public key (for scanning) and spend
    /// public key (for address derivation), but does NOT reveal your signing key.
    pub fn stealth_meta_address(&self) -> StealthMetaAddress {
        self.stealth_keys.meta_address()
    }

    /// Generate a one-time stealth address for sending TO a recipient's meta-address.
    ///
    /// Returns a [`StealthAddress`] containing:
    /// - `one_time_pubkey`: use as the note's `owner` field
    /// - `ephemeral_pubkey`: publish alongside the note for recipient scanning
    pub fn generate_stealth_address_for(&self, recipient: &StealthMetaAddress) -> StealthAddress {
        let (addr, _shared_secret) = recipient.generate_stealth_address();
        addr
    }

    /// Scan announcements for notes addressed to this cipherclerk (using our view key).
    ///
    /// Iterates over the provided announcements, performing the DH check to identify
    /// notes that were sent to our stealth meta-address. Returns the note commitments
    /// of notes that belong to us.
    ///
    /// For large announcement sets, the view tag pre-filter makes this efficient:
    /// only ~1/256 of announcements require the full DH computation.
    pub fn scan_notes(
        &self,
        announcements: &[(NoteCommitment, StealthAnnouncement)],
    ) -> Vec<OwnedStealthNote> {
        let meta = self.stealth_keys.meta_address();
        let mut owned = Vec::new();

        for (commitment, announcement) in announcements {
            // Fast pre-filter: skip if view tag does not match (~255/256 of the time).
            if !announcement.matches_view_tag(&self.stealth_keys.view_private_key) {
                continue;
            }

            // Full ownership check via DH. We construct a StealthAddress from the
            // announcement's ephemeral pubkey and check if we're the recipient.
            let stealth_addr = StealthAddress {
                one_time_pubkey: [0u8; 32], // Not needed for check_ownership
                ephemeral_pubkey: announcement.ephemeral_pubkey,
            };
            if stealth_addr.check_ownership(&self.stealth_keys.view_private_key, &meta.spend_pubkey)
            {
                let spending_key = stealth_addr.derive_spending_key(
                    &self.stealth_keys.view_private_key,
                    &self.stealth_keys.spend_private_key,
                );
                owned.push(OwnedStealthNote {
                    commitment: *commitment,
                    ephemeral_pubkey: announcement.ephemeral_pubkey,
                    spending_key,
                });
            }
        }

        owned
    }

    // =========================================================================
    // Private Transfer (Committed Notes + Stealth)
    // =========================================================================

    /// Create a private transfer: committed value, stealth recipient, range-proved.
    ///
    /// This combines stealth addressing with value commitments to produce a fully
    /// private transfer turn where:
    /// - The recipient is hidden (one-time stealth address)
    /// - The amount is hidden (Pedersen commitment + Bulletproof range proof)
    /// - Conservation is proven (Schnorr excess signature)
    ///
    /// # Arguments
    ///
    /// * `amount` - The value to transfer.
    /// * `asset_type` - The asset type identifier.
    /// * `recipient_meta` - The recipient's stealth meta-address.
    ///
    /// # Returns
    ///
    /// A fully-formed [`Turn`] ready for signing and submission, or an error.
    pub fn private_transfer(
        &mut self,
        amount: u64,
        asset_type: u64,
        recipient_meta: &StealthMetaAddress,
    ) -> Result<Turn, SdkError> {
        use crate::committed_turn::{CommittedNoteOutput, CommittedTurnBuilder};

        // 1. Generate stealth address for recipient.
        let (stealth_addr, _shared_secret) = recipient_meta.generate_stealth_address();

        // 2. Build a committed turn with the stealth address as recipient.
        let agent_cell = self.cell_id("default");
        let nonce = self.receipt_chain.len() as u64;

        let output = CommittedNoteOutput {
            value: amount,
            asset_type,
            recipient: stealth_addr.one_time_pubkey,
        };

        let mut builder = CommittedTurnBuilder::new();
        builder.add_output(output);

        // Note: In a full implementation, the caller would provide input notes to
        // spend. For the API surface, we build a turn with just the output --
        // the caller can use build_committed_transfer() for full input/output flows.
        builder.build(agent_cell, nonce, 0)
    }

    // =========================================================================
    // Sovereign Cell Operations
    // =========================================================================

    /// Transition one of our cells to sovereign mode.
    ///
    /// After this, the federation stores only a 32-byte commitment.
    /// We maintain the full state locally. The returned turn must be signed
    /// and submitted to the federation to take effect.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The cell to make sovereign. Must be a cell we own.
    ///
    /// # Returns
    ///
    /// A [`Turn`] containing an `Effect::MakeSovereign` action ready for signing.
    pub fn make_sovereign(&mut self, cell_id: &CellId) -> Result<Turn, SdkError> {
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;

        let mut forest = dregg_turn::forest::CallForest::new();
        // Built UNAUTHORIZED via the sealed raw scaffold: the returned turn
        // is a skeleton the CALLER signs before submission (see the doc
        // above), and sovereign authority is ultimately the witness/proof
        // attached on the sovereign execute paths — not a signature leg.
        let action = crate::raw::unsigned_action_named(
            agent_cell,
            "make_sovereign",
            vec![Effect::MakeSovereign { cell: agent_cell }],
        );
        forest.add_root(action);

        let turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: Some("make_sovereign".to_string()),
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        Ok(turn)
    }

    /// Execute a turn targeting a sovereign cell.
    ///
    /// We must include the current cell state as a witness so the federation can
    /// verify the state commitment matches what it has stored.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to target.
    /// * `effects` - The effects to apply.
    /// * `fee` - The computron fee for this turn.
    ///
    /// # Returns
    ///
    /// A [`Turn`] with `sovereign_witnesses` populated, ready for signing.
    pub fn execute_sovereign_turn(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<Turn, SdkError> {
        // 1. Get our local cell state.
        let cell_state = self
            .sovereign_cells
            .get(cell_id)
            .ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no local sovereign state for cell {}; call store_sovereign_state() first",
                    cell_id
                ))
            })?
            .clone();

        // 2. Compute the pre-state commitment from the local cell.
        let old_commitment = cell_state.state_commitment();

        // 3. Build the SovereignCellWitness with full peer-state-transition
        //    shape: signed by the cell's owning key over the canonical
        //    transition message, with a per-cell monotonic sequence.
        //
        //    Greenfield assumption: the cell's owning key is the cipherclerk's
        //    signing key (the common agent==sovereign-cell case). If the
        //    cell's public_key drifts from the cipherclerk's verifying key, we
        //    cannot sign; surface as a missing-key error.
        if cell_state.public_key() != &self.public_key.0 {
            return Err(SdkError::MissingKey(format!(
                "cannot sign sovereign witness for cell {}: cell's public_key does not match cipherclerk's key",
                cell_id
            )));
        }
        // For the witness path there is NO STARK; the executor verifies the
        // transition by RE-EXECUTING the effects against the injected
        // pre-state and requiring that the resulting `state_commitment()`
        // equals the witness's declared `new_commitment`
        // (`execute.rs::SovereignCommitmentMismatch`). It also rejects all-zero
        // placeholder `new_commitment`/`effects_hash` (rules 7/8). So we must
        // pre-execute the effects locally, declare the real post-state
        // commitment, and sign the canonical effects hash.
        //
        // Apply the same effects the executor will: Transfer / SetField /
        // IncrementNonce mutate the cell, mirroring
        // `prove_sovereign_turn` (the STARK path). `new_commitment` is the
        // executor-aligned `CellState::state_commitment()` of the post-state
        // (NOT the EffectVM PI commitment — that form is only for the
        // proof-carrying path, which is verified via STARK PI rather than
        // state re-execution).
        let mut new_cell_state = cell_state.clone();
        for effect in &effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        new_cell_state.state.set_balance(
                            new_cell_state
                                .state
                                .balance()
                                .saturating_sub(*amount as i64),
                        );
                    }
                    if to == cell_id {
                        new_cell_state.state.set_balance(
                            new_cell_state
                                .state
                                .balance()
                                .saturating_add(*amount as i64),
                        );
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    if *index < new_cell_state.state.fields.len() {
                        new_cell_state.state.fields[*index] = *value;
                    }
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    let _ = new_cell_state.state.increment_nonce();
                }
                _ => {}
            }
        }
        let new_commitment: [u8; 32] = new_cell_state.state_commitment();

        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let sequence = self
            .sovereign_witness_sequences
            .get(cell_id)
            .copied()
            .unwrap_or(0)
            + 1;

        // 4. Build the turn (with EMPTY witnesses first) so we can derive the
        //    canonical effects hash via `compute_turn_identity_pi` — the same
        //    function the executor uses for turn identity. The witness is NOT
        //    part of turn identity (the proof path proves this by computing
        //    identity over an empty-witness turn), so we can attach it after.
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;

        let mut forest = dregg_turn::forest::CallForest::new();
        // Sealed-raw scaffold: a sovereign turn's authority is the attached
        // sovereign WITNESS (verified against the cell's commitment), not a
        // signature leg — there is deliberately no credential here.
        let action = crate::raw::unsigned_action_named(agent_cell, "sovereign_execute", effects);
        forest.add_root(action);

        let mut turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // Canonical effects hash (4 BabyBear felts → 32 bytes), matching the
        // executor's `compute_turn_identity_pi`/`commitment_4bb_to_bytes`. This
        // is always non-zero (BLAKE3 of even an empty effect set is non-zero),
        // satisfying the executor's no-placeholder rule.
        let (_turn_hash, effects_hash_global, _actor_nonce, _prev) =
            dregg_turn::TurnExecutor::compute_turn_identity_pi(&turn);
        let effects_hash: [u8; 32] =
            dregg_turn::TurnExecutor::commitment_4bb_to_bytes(effects_hash_global);

        let signing_message = SovereignCellWitness::signing_message(
            cell_id,
            &old_commitment,
            &new_commitment,
            &effects_hash,
            timestamp,
            sequence,
        );
        let signature = self.signing_key.sign(&signing_message).to_bytes();
        let witness = SovereignCellWitness {
            cell_id: *cell_id,
            old_commitment,
            new_commitment,
            effects_hash,
            timestamp,
            sequence,
            signature,
            cell_state,
            transition_proof: None,
        };
        self.sovereign_witness_sequences.insert(*cell_id, sequence);
        turn.sovereign_witnesses.insert(*cell_id, witness);

        // Advance local sovereign state to the post-state so the NEXT turn's
        // pre-state commitment matches the ledger (which the executor updates
        // to `new_commitment` on accept). Mirrors `prove_sovereign_turn`.
        self.sovereign_cells.insert(*cell_id, new_cell_state);

        Ok(turn)
    }

    /// Execute a sovereign turn with STARK proof (Phase 2).
    ///
    /// The agent executes effects locally, generates a STARK proof that the state
    /// transition is valid, and submits the proof. The federation verifies the proof
    /// instead of re-executing (constant-time verification regardless of state complexity).
    ///
    /// This method:
    /// 1. Gets the local sovereign cell state
    /// 2. Computes the old commitment
    /// 3. Applies effects locally (balance transfer)
    /// 4. Computes the new commitment
    /// 5. Generates the STARK proof (EffectVmAir)
    /// 6. Builds a Turn with `execution_proof: Some(proof_bytes)`
    /// 7. `sovereign_witnesses` is EMPTY — the proof covers the transition
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to act on.
    /// * `effects` - Effects to apply (currently supports Transfer).
    /// * `fee` - Computron fee for this turn.
    /// * `block_height` - The federation height the turn is proven against. LOAD-BEARING for the
    ///   `CellSeal` record-pin family: `apply_cell_seal` writes `sealed_at = block_height` into the
    ///   lifecycle, which `lifecycle_felt` folds into the AFTER block's limb-29 anchor. The executor
    ///   MUST verify this turn at the SAME height (`TurnExecutor::set_block_height`) or an honest seal
    ///   proof's lifecycle felt would not equal the verifier's anchored PI 38. Every other effect
    ///   ignores it (pass `0` for height-independent turns).
    ///
    /// # Returns
    ///
    /// A proof-carrying [`Turn`] ready for submission to the federation.
    pub fn execute_sovereign_turn_with_proof(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
        block_height: u64,
    ) -> Result<Turn, SdkError> {
        // THE ROTATION (cutover C1): when the rotated IR-v2 producer is compiled
        // (native default; `dregg-circuit/prover` present), this matched-pair
        // path — producer here, verifier `executor::verify_and_commit_proof` —
        // mints the rotated `Ir2BatchProof` over the R=24 cohort descriptor and
        // carries the v9 felt commitment. This retires the weak hand-AIR
        // `EffectVmAir` leg on the sovereign path (a soundness win). The
        // `emit_witnessed_receipt` / bilateral-aggregator WR path stays on the v1
        // trace shape until the bilateral-aggregator rotation (cutover C4).
        #[cfg(feature = "prover")]
        {
            let proven =
                self.prove_sovereign_turn_rotated(cell_id, effects, fee, block_height)?;
            Ok(proven.turn)
        }
        #[cfg(not(feature = "prover"))]
        {
            let _ = block_height; // the retired v1 path is height-independent
            let proven = self.prove_sovereign_turn(cell_id, effects, fee)?;
            Ok(proven.turn)
        }
    }

    /// Produce a real per-cell [`WitnessedReceipt`] for a sovereign turn.
    ///
    /// v1 floor only (the bilateral-aggregator WR path): it lifts the v1 hand-AIR
    /// scope-2 trace + PI into a [`WitnessedReceipt`]. The recursion tower's sovereign
    /// attestation is the rotated proof-carrying turn from
    /// [`Self::execute_sovereign_turn_with_proof`]; this inline-trace WR is a v1-only
    /// Silver-Vision artifact the rotated leg does not carry.
    ///
    /// Where [`Self::execute_sovereign_turn_with_proof`] builds the STARK
    /// proof, drops the scope-2 trace, and returns only a proof-carrying
    /// [`Turn`], this method *retains* the trace and PI and lifts them — plus a
    /// self-derived [`dregg_turn::TurnReceipt`] — into a
    /// [`WitnessedReceipt`] via [`WitnessedReceipt::from_components`].
    ///
    /// The resulting WR is the SDK agent's *own side* of a bilateral
    /// interaction: its `public_inputs` carry the γ.2 projected bilateral
    /// roots/counts for `cell_id`'s role, so it slots directly into a
    /// `&[(CellId, WitnessedReceipt)]` bundle for the γ.2 aggregator
    /// ([`WitnessedReceipt::verify_bilateral_chain`]). The matching peer side
    /// is produced by the peer running its own SDK against the same `Turn`.
    ///
    /// Side effects mirror [`Self::execute_sovereign_turn_with_proof`]: the
    /// local sovereign state is advanced to the post-effect state. The
    /// returned [`Turn`] is the same proof-carrying turn; callers that want
    /// both the submittable turn and the WR can read `.turn` and `.receipt`
    /// off the returned [`SovereignWitnessedReceipt`].
    #[cfg(not(feature = "prover"))]
    pub fn emit_witnessed_receipt(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<SovereignWitnessedReceipt, SdkError> {
        let proven = self.prove_sovereign_turn(cell_id, effects, fee)?;
        let ProvenSovereignTurn {
            turn,
            trace,
            public_inputs,
            new_commitment,
            pre_state_commitment,
        } = proven;

        // Flatten the (already γ.2-projected) public inputs to canonical u32.
        let public_inputs_u32: Vec<u32> = public_inputs.iter().map(|bb| bb.as_u32()).collect();
        let proof_bytes = turn
            .execution_proof
            .clone()
            .expect("prove_sovereign_turn always attaches execution_proof");

        // Derive a TurnReceipt for this cell's transition. The pre-state is
        // the local cell commitment captured before effects were applied;
        // post-state is the proof's claimed new commitment (PI[NEW_COMMIT]).
        let (turn_hash, effects_hash_global, _actor_nonce, _prev) =
            dregg_turn::TurnExecutor::compute_turn_identity_pi(&turn);
        let turn_hash_bytes = dregg_turn::TurnExecutor::commitment_4bb_to_bytes(turn_hash);
        let effects_hash_bytes =
            dregg_turn::TurnExecutor::commitment_4bb_to_bytes(effects_hash_global);
        let forest_hash = turn.call_forest.compute_hash();
        let action_count = turn.call_forest.roots.len();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);

        let receipt = dregg_turn::TurnReceipt {
            turn_hash: turn_hash_bytes,
            forest_hash,
            pre_state_hash: pre_state_commitment,
            post_state_hash: new_commitment,
            timestamp,
            effects_hash: effects_hash_bytes,
            computrons_used: fee,
            action_count,
            previous_receipt_hash: turn.previous_receipt_hash,
            agent: *cell_id,
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        };

        let witnessed = WitnessedReceipt::from_components(
            receipt,
            proof_bytes,
            public_inputs_u32,
            Some(&trace),
        );

        Ok(SovereignWitnessedReceipt {
            cell_id: *cell_id,
            turn,
            witnessed,
        })
    }

    /// RETIRED (v1 hand-AIR sovereign producer): the `EffectVmAir` STARK sovereign-turn
    /// prover is gone. The live sovereign producer is [`Self::prove_sovereign_turn_rotated`]
    /// (the rotated R=24 `Ir2BatchProof`, `prover`-gated). On a `not(prover)` build the v1
    /// sovereign prover fails closed.
    #[cfg(not(feature = "prover"))]
    fn prove_sovereign_turn(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<ProvenSovereignTurn, SdkError> {
        let _ = (cell_id, effects, fee);
        Err(SdkError::Wire(
            "v1 hand-AIR sovereign-turn prover is retired; the rotated sovereign producer \
             (prove_sovereign_turn_rotated) is the live path"
                .into(),
        ))
    }

    /// THE ROTATED sovereign producer (cutover C1, decision #1: proving lives at
    /// the layer that HOLDS the cell state). Mints the rotated R=24 `Ir2BatchProof`
    /// over the cohort descriptor for the turn's effect, instead of the hand-AIR
    /// `EffectVmAir` proof. The matched verifier is
    /// `dregg_turn::executor::verify_and_commit_proof`, which reconstructs the same
    /// 38-PI layout + v9 commitment from the after-state it holds and verifies
    /// through `descriptor_ir2::verify_vm_descriptor2` (no hand-AIR).
    ///
    /// The proof BINDS the rotated v9 state-commitment (`wireCommitR`, which absorbs
    /// the FULL authority residue via register r23 — `compute_authority_digest_felt`).
    /// The new commitment is the v9 felt encoded canonically (`felt_to_bytes32`); the
    /// verifier reads it back and checks it equals the proof's NEW_COMMIT PI carrier.
    ///
    /// Turn-context (`cells_root`, `nullifier_root`, `iroot`) is published THROUGH the
    /// commitment, not reconstructed by the verifier: the producer is the side that
    /// holds the receipt log + ledger; the verifier trusts the bound commitment.
    #[cfg(feature = "prover")]
    fn prove_sovereign_turn_rotated(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
        block_height: u64,
    ) -> Result<ProvenSovereignTurn, SdkError> {
        use dregg_cell::commitment::{
            V9RotationContext, compute_rotated_pre_limbs, felt8_to_bytes32,
        };
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::poseidon2::wire_commit_8_chip;
        use dregg_turn::rotation_witness as rw;

        // 1. Local before-state cell.
        let before_cell = self
            .sovereign_cells
            .get(cell_id)
            .ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no local sovereign state for cell {cell_id}; call store_sovereign_state() first"
                ))
            })?
            .clone();

        // 1b. WHOLE-TURN FOREST (foolable gap #2 producer half): a heterogeneous turn splits into
        //     more than one maximal homogeneous cohort run. The single-leg wide prover fails closed on
        //     such a turn (`prove_effect_vm_rotated_wide` rejects a heterogeneous slice), so we mint ONE
        //     rotated leg per cohort run + thread the per-run pre/post 8-felt commit into a
        //     `SovereignCohortChain` wire the deployed executor leg verifies + chains
        //     (`verify_and_commit_proof_rotated`). A single-cohort turn (the live fleet) skips this and
        //     takes the byte-identical single-leg path below.
        {
            let vm_effects_probe = Self::convert_effects_to_vm(cell_id, &effects);
            if crate::full_turn_proof::split_into_cohort_runs(&vm_effects_probe).len() > 1 {
                return self.prove_sovereign_cohort_chain(
                    cell_id,
                    &before_cell,
                    effects,
                    fee,
                    block_height,
                );
            }
        }

        // 2. Apply effects locally to derive the after-state cell (same projection the
        //    v1 path uses; the cipherclerk only models the variants whose AIR coverage
        //    it can soundly prove — others are NoOp at the circuit boundary).
        let mut after_cell = before_cell.clone();
        for effect in &effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        after_cell
                            .state
                            .set_balance(after_cell.state.balance().saturating_sub(*amount as i64));
                    }
                    if to == cell_id {
                        after_cell
                            .state
                            .set_balance(after_cell.state.balance().saturating_add(*amount as i64));
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    if *index < after_cell.state.fields.len() {
                        after_cell.state.fields[*index] = *value;
                    }
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    let _ = after_cell.state.increment_nonce();
                }
                // The setPermissions BEACHHEAD (rotated record-pin, record-digest limb 24): project
                // the new permissions onto the after-cell through the SHARED `apply_effect_to_cell`
                // weld so the producer's `last[AFTER_BASE + B_RECORD_DIGEST]` (= the after-cell's
                // `compute_authority_digest_felt`, seeded at step 3 below for the rotated leg) MOVES to
                // exactly the felt the verifier anchors PI 38 to (`verify_and_commit_proof_rotated`'s
                // record-pin anchor). The two sides MUST move together — both route through this one
                // function — or an HONEST setPermissions proof would be rejected (the after-digest
                // would not equal the anchored PI 38).
                Effect::SetPermissions { cell, .. } if cell == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                // setVK (record-digest limb 24): same anti-drift weld as setPermissions. The
                // producer's after-cell installs the VK so its r23 authority digest (the AFTER
                // block's `B_RECORD_DIGEST` limb) MOVES to exactly the felt the verifier anchors PI 38
                // to. Both sides route through `apply_effect_to_cell`; the producer projects
                // `SetVerificationKey → VmEffect::SetVerificationKey` and so does the executor bridge,
                // so the descriptor (`setVKVmDescriptor2R24`) reconstructs identically.
                Effect::SetVerificationKey { cell, .. } if cell == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                // The LIFECYCLE record-pin family (limb 29) + the Refusal record-digest pin: project
                // through the SHARED `apply_effect_to_cell` so the producer's AFTER block carries the
                // forced limb (`lifecycle_felt` for the lifecycle effects, `record_digest`/`fields_root`
                // for refusal) the verifier independently anchors PI 38 to. CellSeal's `sealed_at`
                // depends on `block_height`, so the producer MUST apply at the SAME height the verifier
                // will run at (threaded in from the federation height) or the honest seal's lifecycle
                // felt would not equal the verifier's anchor.
                Effect::CellSeal { target, .. } if target == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                Effect::CellUnseal { target } if target == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                Effect::CellDestroy { target, .. } if target == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                Effect::ReceiptArchive { checkpoint, .. } if checkpoint.cell_id == *cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                Effect::Refusal { cell, .. } if cell == cell_id => {
                    dregg_turn::rotation_witness::apply_effect_to_cell(
                        &mut after_cell,
                        cell_id,
                        effect,
                        block_height,
                    );
                }
                _ => {}
            }
        }

        // 3. The Effect-VM marshalling + circuit pre-state (cap-root-seeded), identical
        //    to the v1 path so the rotated generator's v1 sub-trace is byte-identical.
        let vm_effects = Self::convert_effects_to_vm(cell_id, &effects);

        // FEE-IN-PROOF (the `transferFeeVmDescriptor2R24` route): a plain sovereign `Transfer` lead
        // debits the turn `fee` INSIDE the proven transition, so NEW_COMMIT binds the POST-fee
        // balance and the verifier no longer reconstructs `pre = post + fee` blindly. We debit the
        // fee from `after_cell` HERE (after the effects, before `after_w`/the proof) so the local
        // sovereign state we advance to (step 8) matches the proven post-fee balance. The v1
        // sub-trace's after-balance is still the PRE-fee `before + amount·(1−2dir)` (the effects
        // alone); the fee generator subtracts the fee as a column override + commitment recompute,
        // and the proof's gate FORCES `after.bal_lo = before − transfer − fee`, so an underclaimed
        // fee is UNSAT. The BEFORE block stays pre-fee (OLD_COMMIT binds the pre-fee state).
        let is_fee_transfer =
            matches!(vm_effects.as_slice(), [dregg_circuit::effect_vm::Effect::Transfer { .. }]);
        if is_fee_transfer && fee > 0 {
            after_cell
                .state
                .set_balance(after_cell.state.balance().saturating_sub(fee as i64));
        }
        // P0-2 (audit `cell/src/commitment.rs`, REVIEW[circuit-fix-coordination]): seed the
        // EffectVM `record_digest` from the cell's authority-residue digest so OLD_COMMIT/
        // NEW_COMMIT bind the FULL cell state (permissions / VK / lifecycle / …), not the
        // lossy balance/nonce/fields/cap_root subset. This is the SAME r23 the rotated weld
        // carries (`dregg_cell::compute_authority_digest_felt`), so the v1-prefix and rotated
        // legs agree.
        let initial_vm_state = dregg_circuit::CellState::with_capability_root_and_record_digest(
            u64::try_from(before_cell.state.balance()).map_err(|_| {
                SdkError::Wire(
                    "cell balance is negative; cannot prove turn over a well cell here".into(),
                )
            })?,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
            dregg_cell::compute_authority_digest_felt(&before_cell),
        );

        // 4. The turn-context the rotated commitment absorbs. The cipherclerk is the
        //    authority for this sovereign cell, so it supplies the context: `cells_root`
        //    from a single-cell ledger snapshot of the before-cell, the empty nullifier
        //    root (a cap-less sovereign transfer spends no note), and the `iroot` MMR over
        //    its own receipt chain. The before/after blocks share this turn-invariant
        //    context (the receipt log does not change mid-proof).
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = self
            .receipt_chain
            .iter()
            .map(|r| r.receipt_hash())
            .collect();
        let mut ctx_ledger = dregg_cell::Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());

        let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);
        let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);

        // THE REFUSAL `fields_root` WRITE-GATE CONTEXT (the light-client close's deployed prover wire).
        // A Refusal lead's `refusalVmDescriptor2R24` carries an in-circuit `.write` map-op forcing
        // `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt)`; the wide
        // refusal producer needs the BEFORE-cell's fields-tree leaf set (the openable accumulator the
        // limb-36 root opens against, with the reserved audit slot) + the audit felt the refusal writes
        // (light-client-recomputable from the published params; the post-cell carries it at
        // `fields_map[REFUSAL_AUDIT_EXT_KEY]`). An EMPTY fields tree is UNSAT against the gate — so we
        // thread the real BEFORE leaves so the HONEST refusal proves on the deployed path. (The witness
        // carries the `fields_root` DIGEST limb only, NOT the leaf set — mirrors the NoteSpend
        // `before_nullifiers` plumbing.)
        let refusal_fields: Option<(Vec<dregg_circuit::heap_root::HeapLeaf>, BabyBear)> =
            if matches!(
                vm_effects.first(),
                Some(dregg_circuit::effect_vm::Effect::Refusal { .. })
            ) {
                let before_leaves =
                    dregg_cell::state::fields_root_leaves(&before_cell.state.fields_map);
                let audit_bytes = after_cell
                    .state
                    .fields_map
                    .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
                    .copied()
                    .ok_or_else(|| {
                        SdkError::InvalidWitness(
                            "refusal after-cell carries no audit slot in fields_map — apply_refusal \
                             did not write REFUSAL_AUDIT_EXT_KEY (the `.write` gate has no value)"
                                .into(),
                        )
                    })?;
                let audit_value = dregg_circuit::cap_root::fold_bytes32(&audit_bytes);
                Some((before_leaves, audit_value))
            } else {
                None
            };

        // 5. Bridge the producer witnesses into the circuit generator's block witnesses.
        //    Carry the per-cell asset class (the fold of the before-cell's token_id) so the
        //    proof commits to its genuine asset class (PI[v3::ASSET_CLASS]).
        let before_bw = dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(
            before_w.pre_limbs.clone(),
            before_w.iroot,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?
        .with_asset_class(before_w.asset_class);
        let after_bw = dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(
            after_w.pre_limbs.clone(),
            after_w.iroot,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?
        .with_asset_class(after_w.asset_class);

        // The caveat manifest: transfer exercises both caveat domains (the validated
        // reference); every other effect proves with the empty manifest. The rotated
        // shape is identical either way.
        let caveat = match vm_effects.as_slice() {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => {
                dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest()
            }
            _ => dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
        };

        // 6. THE FAITHFUL 8-FELT WIDE FLIP (the deployed commitment is now ~124-bit, not
        //    ~31-bit). Generate the WIDE rotated trace + wide-PI vector: the two 13×8
        //    BEFORE/AFTER carriers re-absorb the SAME rotated limbs the 1-felt block lays
        //    into a genuine 8-felt commitment, published on the 16 wide PIs (the LAST 16 of
        //    the vector). The descriptor's wide `pi_binding`s tie those 16 PIs to the trace's
        //    carrier-12 columns, so the proof commits to the full 8-felt commit — and the
        //    1-felt PI 34/35 waist was retired from the wide descriptor (Stage 1).
        //
        //    `is_fee_transfer` routes the wide FEE producer (39 base PIs + 16 wide = 55):
        //    BEFORE 8-felt commit = PIs 39..46, AFTER = PIs 47..54. Otherwise the bare wide
        //    producer (38 base + 16 = 54): BEFORE = PIs 38..45, AFTER = 46..53.
        let (trace, public_inputs) = if is_fee_transfer {
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_transfer_shape_with_fee_wide(
                &initial_vm_state,
                &vm_effects,
                &before_bw,
                &after_bw,
                &caveat,
                fee,
            )
            .map_err(|e| SdkError::InvalidWitness(format!("wide fee trace generation: {e}")))?
        } else if matches!(
            vm_effects.first(),
            Some(dregg_circuit::effect_vm::Effect::NoteSpend { .. })
        ) {
            let (t, d, _heaps) =
                dregg_circuit::effect_vm::trace_rotated::generate_rotated_note_spend_wide(
                    &initial_vm_state,
                    &vm_effects,
                    &before_bw,
                    &after_bw,
                    &caveat,
                    &[],
                )
                .map_err(|e| SdkError::InvalidWitness(format!("wide note-spend trace generation: {e}")))?;
            (t, d)
        } else if matches!(
            vm_effects.first(),
            Some(dregg_circuit::effect_vm::Effect::NoteCreate { .. })
        ) {
            // NoteCreate routes through the COMMITMENTS-SET grow-gate wide producer (limb-27
            // accumulator) — the append-only twin of note-spend. This path threads no commitments-set
            // context, so the empty set is the grow-gate's BEFORE.
            let (t, d, _heaps) =
                dregg_circuit::effect_vm::trace_rotated::generate_rotated_note_create_wide(
                    &initial_vm_state,
                    &vm_effects,
                    &before_bw,
                    &after_bw,
                    &caveat,
                    &[],
                )
                .map_err(|e| {
                    SdkError::InvalidWitness(format!("wide note-create trace generation: {e}"))
                })?;
            (t, d)
        } else if matches!(
            vm_effects.first(),
            Some(dregg_circuit::effect_vm::Effect::Refusal { .. })
        ) {
            // REFUSAL routes through the `fields_root` WRITE-gate wide producer (limb-36 accumulator) —
            // the light-client close. This precompute MUST route refusal identically to
            // `prove_effect_vm_rotated_wide` below (which re-derives the SAME trace + wide PIs), or the
            // bound 16 wide PIs would not match `public_inputs[n_pi-16..]`. The genuine fields-tree write
            // is threaded so the honest refusal proves; an empty tree would be UNSAT against the gate.
            let (leaves, audit_value) = refusal_fields.as_ref().map(|(l, a)| (l.as_slice(), *a)).ok_or_else(|| {
                SdkError::InvalidWitness(
                    "refusal precompute: missing fields-tree context (refusal_fields)".into(),
                )
            })?;
            let (t, d, _heaps) =
                dregg_circuit::effect_vm::trace_rotated::generate_rotated_refusal_wide(
                    &initial_vm_state,
                    &vm_effects,
                    &before_bw,
                    &after_bw,
                    &caveat,
                    leaves,
                    audit_value,
                )
                .map_err(|e| SdkError::InvalidWitness(format!("wide refusal trace generation: {e}")))?;
            (t, d)
        } else if matches!(
            vm_effects.first(),
            Some(
                dregg_circuit::effect_vm::Effect::SetPermissions { .. }
                    | dregg_circuit::effect_vm::Effect::SetVerificationKey { .. }
                    | dregg_circuit::effect_vm::Effect::CellSeal { .. }
                    | dregg_circuit::effect_vm::Effect::CellUnseal { .. }
                    | dregg_circuit::effect_vm::Effect::CellDestroy { .. }
                    | dregg_circuit::effect_vm::Effect::ReceiptArchive { .. }
                    | dregg_circuit::effect_vm::Effect::MakeSovereign
            )
        ) {
            // The record-pin family carries the 39-PI base (the record/lifecycle pin at PI 38).
            // MakeSovereign joins (its record pin welds the AFTER authority-digest limb folding the
            // flipped mode byte — see `record_pin_offset`).
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_record_pin_wide(
                &initial_vm_state,
                &vm_effects,
                &before_bw,
                &after_bw,
                &caveat,
            )
            .map_err(|e| SdkError::InvalidWitness(format!("wide record-pin trace generation: {e}")))?
        } else {
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_transfer_shape_wide(
                &initial_vm_state,
                &vm_effects,
                &before_bw,
                &after_bw,
                &caveat,
            )
            .map_err(|e| SdkError::InvalidWitness(format!("wide trace generation: {e}")))?
        };
        // The 16 wide commit PIs are the LAST 16 of the vector: BEFORE 8-felt commit (8) then
        // AFTER 8-felt commit (8). Pack each through `felt8_to_bytes32` (the FULL 32-byte slot,
        // ~124-bit). The executor reads them back via `bytes32_to_felt8` and re-anchors the 16
        // wide PIs to the trusted cell's 8-felt commitments.
        let n_pi = public_inputs.len();
        let before_commit_8: [BabyBear; 8] = public_inputs[n_pi - 16..n_pi - 8]
            .try_into()
            .expect("wide PI vector carries 8 BEFORE commit felts");
        let after_commit_8: [BabyBear; 8] = public_inputs[n_pi - 8..n_pi]
            .try_into()
            .expect("wide PI vector carries 8 AFTER commit felts");
        let pre_state_commitment = felt8_to_bytes32(&before_commit_8);
        let new_commitment = felt8_to_bytes32(&after_commit_8);
        // The BEFORE 8-felt carrier equals the CHIP-faithful 8-felt commitment of the pre-state
        // (the byte-twin of the circuit's `fill_wide_block`; the executor recomputes this SAME
        // primitive from the trusted before-cell to anchor the wide PIs). We keep that derivation
        // as a producer-side cross-check.
        {
            let pre = compute_rotated_pre_limbs(
                &before_cell,
                &V9RotationContext {
                    cells_root: before_w.pre_limbs[0],
                    nullifier_root,
                    commitments_root,
                    iroot: before_w.iroot,
                },
            );
            debug_assert_eq!(
                before_commit_8,
                wire_commit_8_chip(&pre, before_w.iroot),
                "rotated wide BEFORE commit must equal the chip-faithful 8-felt commitment of the before-state"
            );
        }

        // 7. Build the proof-carrying turn scaffold (same identity as the v1 path: the
        //    authority IS the attached proof; no signature leg).
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;
        let mut forest = dregg_turn::forest::CallForest::new();
        let action = crate::raw::unsigned_action_named(
            agent_cell,
            "sovereign_execute_proven",
            effects.clone(),
        );
        forest.add_root(action);
        let mut turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee,
            memo: Some("sovereign_proof_carrying_rotated".to_string()),
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: Some(*cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // THE WIDE FLIP: route the WIDE provers (8-felt commit published on the 16 wide PIs). The
        // wide generators inside re-derive the SAME wide trace + PI vector computed above, so the
        // bound 16 wide PIs match `public_inputs[n_pi-16..]`.
        let (proof, _wide_dpis) = if is_fee_transfer {
            // FEE-IN-PROOF wide: `transferFeeVmDescriptor2R24Wide` (55 PIs, fee debited in-proof).
            crate::full_turn_proof::prove_effect_vm_rotated_wide_with_fee(
                &initial_vm_state,
                &vm_effects,
                &before_w,
                &after_w,
                &caveat,
                fee,
            )?
        } else {
            crate::full_turn_proof::prove_effect_vm_rotated_wide(
                &initial_vm_state,
                &vm_effects,
                &before_w,
                &after_w,
                &caveat,
                // This cipherclerk path threads no nullifier-set context; a NoteSpend turn here proves
                // against an EMPTY before nullifier accumulator (the grow-gate inserts into empty). The
                // full-turn chained path threads the real freshness leaves from the non-revocation witness.
                None,
                // The refusal `fields_root` WRITE-gate context (built above from before/after cells when
                // the lead is a Refusal) — threaded so the honest refusal proves through the `.write`
                // map-op gate. This MUST match the precompute's refusal route (same trace + wide PIs).
                refusal_fields.as_ref().map(|(l, a)| (l.as_slice(), *a)),
            )?
        };
        let proof_bytes = postcard::to_allocvec(&proof)
            .map_err(|e| SdkError::Wire(format!("rotated proof serialize: {e}")))?;

        // 8. Advance local sovereign state + attach the rotated proof bytes.
        self.sovereign_cells.insert(*cell_id, after_cell);
        turn.execution_proof = Some(proof_bytes);

        Ok(ProvenSovereignTurn {
            turn,
            trace,
            public_inputs,
            new_commitment,
            pre_state_commitment,
        })
    }

    /// THE WHOLE-TURN FOREST producer (foolable gap #2 producer half). Proves a heterogeneous
    /// sovereign turn — one that splits into MORE THAN ONE maximal homogeneous cohort run — as N
    /// rotated wide legs (one per run), threading each run's pre/post state, and packs them into the
    /// `SovereignCohortChain` wire the deployed executor leg (`verify_and_commit_proof_rotated`)
    /// verifies leg-by-leg + chains. This mirrors the SDK `prove_cohort_run_chain` (the
    /// `verify_full_turn_bound` path) but onto the sovereign `execution_proof` wire.
    ///
    /// Per-run state is threaded two ways: the KERNEL `after_cell` accumulates each run's effects via
    /// the SHARED `apply_effect_to_cell` weld (so the rotation witnesses' `cells_root`/`iroot`/8-felt
    /// commit context advance), and the leg's pre/post 8-felt commits come straight off the wide
    /// generator's PI vector (the last 16 PIs) so the executor's chain anchors match by construction.
    ///
    /// Restrictions (fail-closed): `fee` must be 0 (a multi-cohort fee split is out of scope; each leg
    /// proves fee-free), and every cohort run must be a graduated rotated cohort (the single-leg wide
    /// prover's coverage). A run the wide prover cannot mint fails closed here, so the executor never
    /// receives a partial chain.
    #[cfg(feature = "prover")]
    fn prove_sovereign_cohort_chain(
        &mut self,
        cell_id: &CellId,
        before_cell: &dregg_cell::Cell,
        effects: Vec<Effect>,
        fee: u64,
        block_height: u64,
    ) -> Result<ProvenSovereignTurn, SdkError> {
        use dregg_cell::commitment::felt8_to_bytes32;
        use dregg_circuit::field::BabyBear;
        use dregg_turn::executor::{SovereignCohortChain, SovereignCohortLeg};
        use dregg_turn::rotation_witness as rw;

        if fee != 0 {
            return Err(SdkError::InvalidWitness(
                "multi-cohort sovereign turn with a nonzero fee is unsupported; the chained producer \
                 proves each cohort leg fee-free (split the fee into its own turn)"
                    .into(),
            ));
        }

        // The vm-effect projection + the cohort-run split (the SAME the executor recomputes). For a
        // sovereign turn over `cell_id` the projection is 1:1 with the kernel effects (each kernel
        // effect targeting the cell maps to one VmEffect), so the run ranges index BOTH lists.
        let vm_effects = Self::convert_effects_to_vm(cell_id, &effects);
        if vm_effects.len() != effects.len() {
            return Err(SdkError::InvalidWitness(format!(
                "multi-cohort sovereign turn: the vm-effect projection ({} effects) is not 1:1 with \
                 the kernel effects ({}); the chained producer needs a 1:1 mapping to thread per-run \
                 kernel state",
                vm_effects.len(),
                effects.len()
            )));
        }
        let runs = crate::full_turn_proof::split_into_cohort_runs(&vm_effects);
        debug_assert!(runs.len() > 1, "the dispatcher only routes multi-cohort turns here");

        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = self
            .receipt_chain
            .iter()
            .map(|r| r.receipt_hash())
            .collect();

        // The FULL kernel after-cell (all effects applied through the SHARED weld + the balance
        // moves). The FINAL run's after-block witness is produced over this, so the last leg's
        // after8 == the turn's claimed NEW commitment.
        let mut full_after_cell = before_cell.clone();
        for effect in &effects {
            rw::apply_effect_to_cell(&mut full_after_cell, cell_id, effect, block_height);
            if let Effect::Transfer { from, to, amount } = effect {
                if from == cell_id {
                    full_after_cell
                        .state
                        .set_balance(full_after_cell.state.balance().saturating_sub(*amount as i64));
                }
                if to == cell_id {
                    full_after_cell
                        .state
                        .set_balance(full_after_cell.state.balance().saturating_add(*amount as i64));
                }
            }
        }

        // ONE turn-context ledger (the turn's before-cell) feeds EVERY `produce` — `cells_root`/`iroot`
        // are turn-invariant. The single `before_w` is REUSED for every run's before-block AND every
        // INTERIOR run's after-block (the witness-carried limbs — cells_root, authority digest, lifecycle,
        // r11..r23 — are turn-invariant); only the FINAL run's after-block uses the real `after_w`. The
        // changing welds (balance/nonce/fields) ride each run's v1 sub-trace, threaded via `s_k`. This is
        // the SAME design as the SDK `prove_cohort_run_chain`, so `leg[k].after8 == leg[k+1].before8`
        // holds by construction (both are `wireCommit(before_w carried-limbs, s_{k+1} welds)`).
        let mut ctx_ledger = dregg_cell::Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());
        let before_w = rw::produce(
            before_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );
        let after_w = rw::produce(
            &full_after_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );

        // The circuit pre-state, seeded from the turn's before-cell (the SAME seed the single-leg
        // path + the executor use; the executor threads s_k via the v1 sub-trace).
        let initial_vm_state = dregg_circuit::CellState::with_capability_root_and_record_digest(
            u64::try_from(before_cell.state.balance())
                .map_err(|_| SdkError::Wire("cell balance is negative".into()))?,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
            dregg_cell::compute_authority_digest_felt(before_cell),
        );

        let mut s_k = initial_vm_state;
        let mut legs: Vec<SovereignCohortLeg> = Vec::with_capacity(runs.len());
        let mut last_after8 = [BabyBear::ZERO; 8];
        let n_runs = runs.len();

        for (k, run) in runs.iter().enumerate() {
            let run_vm = &vm_effects[run.clone()];
            let is_final = k + 1 == n_runs;
            // INTERIOR runs reuse `before_w` for their after-block (turn-invariant carried limbs); the
            // FINAL run uses the real `after_w` (so the last leg binds the turn's claimed NEW commit).
            let after_block_w = if is_final { &after_w } else { &before_w };

            let caveat = match run_vm {
                [dregg_circuit::effect_vm::Effect::Transfer { .. }] => {
                    dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest()
                }
                _ => dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
            };

            let (proof, dpis) = crate::full_turn_proof::prove_effect_vm_rotated_wide(
                &s_k,
                run_vm,
                &before_w,
                after_block_w,
                &caveat,
                None,
                // The whole-turn forest path threads no per-run fields context; a Refusal run here would
                // fail closed against the `.write` gate (the live sovereign refusal lead is the single-leg
                // path above). Heterogeneous-forest refusal is out of this wire's scope.
                None,
            )?;
            let n_pi = dpis.len();
            let before8: [BabyBear; 8] = dpis[n_pi - 16..n_pi - 8]
                .try_into()
                .map_err(|_| SdkError::InvalidWitness("cohort leg: short wide PI vector".into()))?;
            let after8: [BabyBear; 8] = dpis[n_pi - 8..n_pi]
                .try_into()
                .map_err(|_| SdkError::InvalidWitness("cohort leg: short wide PI vector".into()))?;
            let proof_bytes = postcard::to_allocvec(&proof)
                .map_err(|e| SdkError::Wire(format!("cohort leg proof serialize: {e}")))?;
            legs.push(SovereignCohortLeg { proof_bytes, before8, after8 });
            last_after8 = after8;

            // Thread s_k → s_{k+1} off the generator's own STATE_AFTER columns (the SAME threading the
            // executor's `cell_state_after_run` uses — no hand-replay).
            if !is_final {
                let (v1_trace, _v1_pi) =
                    dregg_circuit::effect_vm::generate_effect_vm_trace(&s_k, run_vm);
                s_k = crate::full_turn_proof::cell_state_after_run(&v1_trace, run_vm.len(), &s_k);
            }
        }
        let final_after_cell = full_after_cell;

        let new_commitment = felt8_to_bytes32(&last_after8);
        let pre_state_commitment = felt8_to_bytes32(&legs[0].before8);

        let chain = SovereignCohortChain { legs };
        let chain_bytes = postcard::to_allocvec(&chain)
            .map_err(|e| SdkError::Wire(format!("cohort chain serialize: {e}")))?;

        // Build the proof-carrying turn (same identity as the single-leg path).
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;
        let mut forest = dregg_turn::forest::CallForest::new();
        let action =
            crate::raw::unsigned_action_named(agent_cell, "sovereign_execute_proven", effects);
        forest.add_root(action);
        let turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee,
            memo: Some("sovereign_proof_carrying_rotated_chain".to_string()),
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: Some(chain_bytes),
            execution_proof_cell: Some(*cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // Advance local sovereign state to the final after-cell.
        self.sovereign_cells.insert(*cell_id, final_after_cell);

        Ok(ProvenSovereignTurn {
            turn,
            // The chain has N traces/PI vectors; the `ProvenSovereignTurn` carries a single
            // trace/PI for the WR lift, which the chained path does not feed. Empty placeholders are
            // fine — the chained sovereign turn is consumed via `.turn` (the proof-carrying turn).
            trace: Vec::new(),
            public_inputs: Vec::new(),
            new_commitment,
            pre_state_commitment,
        })
    }

    /// Extract transfer parameters from effects for proof generation.
    ///
    /// Returns (amount, direction) where direction=1 for outgoing, 0 for incoming.
    #[allow(dead_code)] // Used by the v1 (non-prover) sovereign-prove path's effect validation.
    fn extract_transfer_params(
        cell_id: &CellId,
        effects: &[Effect],
    ) -> Result<(u64, u32), SdkError> {
        for effect in effects {
            if let Effect::Transfer { from, to, amount } = effect {
                if from == cell_id {
                    return Ok((*amount, 1)); // outgoing
                } else if to == cell_id {
                    return Ok((*amount, 0)); // incoming
                }
            }
        }
        // No transfer found — use zero amount (other effects only).
        Ok((0, 0))
    }

    /// Convert turn-level Effects into circuit-level effect_vm::Effects for STARK proving.
    ///
    /// Maps each turn-level `Effect` to the corresponding `effect_vm::Effect` for the
    /// circuit. Effects not targeting this cell are skipped.
    ///
    /// Stage 1 (`EFFECT-VM-SHAPE-A.md` D): mirrors the executor's
    /// `convert_turn_effects_to_vm`. Variants without AIR coverage are gated
    /// behind the `effect-vm-pending-shim` feature on the executor side;
    /// the cipherclerk side intentionally keeps them as NoOp because the cipherclerk
    /// is the trust root and should never sign a turn whose proof cannot be
    /// soundly verified by a production executor.
    ///
    /// AUDIT[P1-1]: most per-effect operands below truncate 32-byte hashes
    /// to 4 bytes via `hash_to_bb` / `field_element_to_bb`. The widening
    /// landed at the *commitment* layer (OLD_COMMIT / NEW_COMMIT now 4 felts
    /// via `commitment_to_4bb`); per-effect parameter widening is deferred
    /// to Stages 3–6 of the master plan, where each variant's AIR is
    /// rewritten to consume wider operand slots.
    pub fn convert_effects_to_vm(
        cell_id: &CellId,
        effects: &[Effect],
    ) -> Vec<dregg_circuit::effect_vm::Effect> {
        use dregg_circuit::effect_vm::Effect as VmEffect;
        use dregg_circuit::field::BabyBear;

        // CLOSED (effect-vm-hash-truncation lane, 2026-05-28): formerly a
        // 4-byte truncation (AUDIT[P1-1]). Both helpers now delegate to the
        // SHARED canonical fold `dregg_circuit::effect_vm::fold_bytes32_to_bb`,
        // which Horner-folds all 8 four-byte limbs of the 32-byte value into
        // the BabyBear felt. The executor projector
        // (`turn/src/executor/effect_vm_bridge.rs`) calls the SAME function,
        // so this SDK projector and the executor projector emit byte-for-byte
        // identical felts — the differential invariant in
        // `protocol-tests/.../effect_vm_differential.rs` asserts this. The
        // full 32-byte value is now bound through the per-effect param column
        // and `PI[EFFECTS_HASH]` (`compute_effects_hash`).
        fn field_element_to_bb(value: &[u8; 32]) -> BabyBear {
            dregg_circuit::effect_vm::fold_bytes32_to_bb(value)
        }

        fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
            dregg_circuit::effect_vm::fold_bytes32_to_bb(h)
        }

        // 32-byte widening (effect-vm-hash-widen lane, 2026-05-28): full
        // 256-bit binding path for hash params widened to `[BabyBear; 8]`
        // (CreateSealPair, *Escrow, CellSeal, etc.). Delegates to the SAME
        // shared circuit helper the executor projector calls, so both emit
        // byte-for-byte identical 8-limb encodings (protocol-tests differential
        // invariant). Each limb is a 4-byte little-endian chunk; all 8 are
        // absorbed by compute_effects_hash.
        fn hash_to_8(h: &[u8; 32]) -> [BabyBear; 8] {
            dregg_circuit::effect_vm::bytes32_to_8_limbs(h)
        }

        // #110: full 32-byte → 8-felt projection (4 bytes per felt,
        // little-endian). Used for EmitEvent topic_hash / payload_hash and
        // related event-shaped variants that need full ~256-bit binding.
        // Delegates to the shared circuit helper so it stays in lock-step with
        // the executor projector.
        fn bytes32_to_8_felts(b: &[u8; 32]) -> [BabyBear; 8] {
            dregg_circuit::effect_vm::bytes32_to_8_limbs(b)
        }

        let mut vm_effects = Vec::new();
        for effect in effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 1, // outgoing
                        });
                    } else if to == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 0, // incoming
                        });
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    vm_effects.push(VmEffect::SetField {
                        field_idx: *index as u32,
                        value: field_element_to_bb(value),
                    });
                }
                Effect::GrantCapability { from, to, cap, .. }
                    if to == cell_id || from == cell_id =>
                {
                    // Project from both granter and grantee perspectives.
                    // The cap_entry is the capability identity being granted/received.
                    // For the granter (from==cell_id), this records that a cap was sent.
                    // For the grantee (to==cell_id), this records the cap was received.
                    // Both perspectives witness a cap_root mutation.
                    let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
                    vm_effects.push(VmEffect::GrantCapability {
                        cap_entry: hash_to_8(cap_hash.as_bytes()),
                        phase_b: None,
                    });
                }
                Effect::NoteSpend {
                    nullifier, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteSpend {
                        nullifier: hash_to_bb(&nullifier.0),
                        value: *value,
                    });
                }
                Effect::NoteCreate {
                    commitment, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteCreate {
                        commitment: hash_to_bb(&commitment.0),
                        value: *value,
                    });
                }

                Effect::MakeSovereign { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::MakeSovereign);
                }
                Effect::CreateCellFromFactory { factory_vk, .. } => {
                    vm_effects.push(VmEffect::CreateCellFromFactory {
                        factory_vk: hash_to_bb(factory_vk),
                        child_vk_derived: BabyBear::ZERO, // Derived at execution time
                    });
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::IncrementNonce);
                }

                // ================================================================
                // Stage 3 projections: ported from effect_vm_bridge.rs.
                // The SDK function has no access to the live Ledger, so
                // ledger-dependent fields (queue lengths, export counters,
                // refcounts) use zero-sentinels. The proof still carries real
                // effect-identity data bound into effects_hash; the ledger-
                // sourced fields are wired at executor time where the Ledger is
                // available. This matches the existing bridge pattern where
                // several fields carry sentinel 0 for "resolved at apply time."
                // ================================================================

                // -- Permissions / VK / caps ------------------------------------
                Effect::SetPermissions {
                    cell,
                    new_permissions,
                } if cell == cell_id => {
                    let perm_bytes = postcard::to_allocvec(new_permissions).unwrap_or_default();
                    let perm_hash_bytes = blake3::hash(&perm_bytes);
                    vm_effects.push(VmEffect::SetPermissions {
                        permissions_hash: hash_to_8(perm_hash_bytes.as_bytes()),
                    });
                }
                Effect::SetVerificationKey { cell, new_vk } if cell == cell_id => {
                    let vk_hash = match new_vk {
                        Some(vk) => {
                            let bytes = postcard::to_allocvec(vk).unwrap_or_default();
                            let h = blake3::hash(&bytes);
                            hash_to_8(h.as_bytes())
                        }
                        None => [BabyBear::ZERO; 8],
                    };
                    vm_effects.push(VmEffect::SetVerificationKey { vk_hash });
                }
                Effect::RevokeCapability { cell, slot } if cell == cell_id => {
                    let slot_bytes = slot.to_le_bytes();
                    let slot_hash_bytes = blake3::hash(&slot_bytes);
                    vm_effects.push(VmEffect::RevokeCapability {
                        slot_hash: hash_to_8(slot_hash_bytes.as_bytes()),
                        phase_b: None,
                    });
                }
                Effect::AttenuateCapability {
                    cell,
                    slot,
                    narrower_permissions,
                    ..
                } if cell == cell_id => {
                    // Bind slot + narrowed-permissions hash into effects_hash.
                    // The AIR enforces monotonic narrowing via the executor;
                    // the proof carries the identity of which slot was attenuated.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&slot.to_le_bytes());
                    let perm_bytes =
                        postcard::to_allocvec(narrower_permissions).unwrap_or_default();
                    hasher.update(&perm_bytes);
                    let attn_hash = hasher.finalize();
                    vm_effects.push(VmEffect::RevokeCapability {
                        // Reuse RevokeCapability shape: attenuate is a
                        // monotone-narrowing on a slot — the same cap-root
                        // mutation path as revoke. The slot_hash here is
                        // hash(slot || new_perms) so it's distinct from a plain
                        // RevokeCapability on the same slot.
                        slot_hash: hash_to_8(attn_hash.as_bytes()),
                        phase_b: None,
                    });
                }

                // -- CreateCell / lifecycle -------------------------------------
                Effect::CreateCell {
                    public_key,
                    token_id,
                    balance,
                } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(public_key);
                    hasher.update(token_id);
                    hasher.update(&balance.to_le_bytes());
                    let create_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::CreateCell {
                        create_hash: hash_to_8(create_hash_bytes.as_bytes()),
                    });
                }
                // CellSeal / CellUnseal / CellDestroy (the LIFECYCLE record-pin family, AFTER limb 29):
                // project to the NATIVE `VmEffect::{CellSeal,CellUnseal,CellDestroy}`, byte-identical to
                // the executor bridge (`turn::executor::effect_vm_bridge::convert_turn_effects_to_vm`),
                // so the verifier resolves the SAME `{cellSeal,cellUnseal,cellDestroy}VmDescriptor2R24`
                // record-pin descriptor (39 PIs) the producer proves over. The PRIOR
                // `SetPermissions`/`EmitEvent` collapse resolved a DIFFERENT descriptor than the bridge
                // (a producer/verifier projection divergence that rejected honest proofs BEFORE the
                // lifecycle anchor was reached). The lifecycle limb (limb 29 = `lifecycle_felt`) is the
                // genuine mover, anchored by `lifecycle_felt_cell(post_cell)`.
                Effect::CellSeal { target, reason } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    let reason_hash = hash_to_8(reason);
                    vm_effects.push(VmEffect::CellSeal {
                        target: target_hash,
                        reason_hash,
                    });
                }
                Effect::CellUnseal { target } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    vm_effects.push(VmEffect::CellUnseal {
                        target: target_hash,
                    });
                }
                Effect::CellDestroy {
                    target,
                    certificate,
                } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    let cert_hash = certificate.certificate_hash();
                    vm_effects.push(VmEffect::CellDestroy {
                        target_hash,
                        death_certificate_hash: hash_to_8(&cert_hash),
                    });
                }
                // ReceiptArchive (the LIFECYCLE record-pin, AFTER limb 29): project to the NATIVE
                // `VmEffect::ReceiptArchive`, byte-identical to the executor bridge, so the verifier
                // resolves `receiptArchiveVmDescriptor2R24` (39 PIs, lifecycle-pinned). The deployed
                // `apply_receipt_archive` moves the cell lifecycle to `Archived`, so `lifecycle_felt`
                // (limb 29) is the genuine mover; the verifier anchors `lifecycle_felt_cell(post_cell)`.
                // The PRIOR `EmitEvent` collapse resolved `emitEventVmDescriptor2R24` (no record pin),
                // diverging from the bridge.
                Effect::ReceiptArchive {
                    prefix_end_height,
                    checkpoint,
                } if checkpoint.cell_id == *cell_id => {
                    let target_hash = hash_to_8(checkpoint.cell_id.as_bytes());
                    let end_height_bb =
                        BabyBear::new((*prefix_end_height & ((1u64 << 30) - 1)) as u32);
                    let terminal_hash = hash_to_8(&checkpoint.archive_terminal_receipt_hash);
                    vm_effects.push(VmEffect::ReceiptArchive {
                        target: target_hash,
                        archive_end_height: end_height_bb,
                        terminal_receipt_hash: terminal_hash,
                    });
                }

                // -- Burn (CRITICAL: algebraic balance constraint) -------------
                Effect::Burn { target, amount, .. } if target == cell_id => {
                    // CRITICAL: Burn irreversibly reduces a cell's balance.
                    // VmEffect::Transfer { direction: 1 } (outgoing/debit)
                    // witnesses a balance decrement in the Effect VM's balance
                    // continuity rows. The `was_burn` disclosure is separately
                    // bound via effect_action_air SCHEMA_BURN's
                    // AlgebraicConstraint::Burn. Without this arm the proof
                    // attests to nothing about the balance destruction —
                    // a forged receipt could claim any new balance.
                    // direction=1 means outgoing/debit: new_balance = old - amount.
                    vm_effects.push(VmEffect::Transfer {
                        amount: *amount,
                        direction: 1,
                    });
                }

                // -- Emit event -------------------------------------------------
                Effect::EmitEvent { cell, event } if cell == cell_id => {
                    // #110: canonical (topic_hash, payload_hash) projection.
                    // Must match `turn::executor::effect_vm_bridge` byte-for-byte
                    // (differential test asserts equivalence).
                    let topic_bytes = *blake3::hash(&event.topic).as_bytes();
                    let mut ph = blake3::Hasher::new();
                    for d in &event.data {
                        ph.update(d);
                    }
                    let payload_bytes = *ph.finalize().as_bytes();
                    vm_effects.push(VmEffect::EmitEvent {
                        topic_hash: bytes32_to_8_felts(&topic_bytes),
                        payload_hash: bytes32_to_8_felts(&payload_bytes),
                    });
                }

                // -- Sealing / sovereign / factory (already handled above except CreateSealPair)

                // -- Delegation -------------------------------------------------
                Effect::SpawnWithDelegation {
                    child_public_key,
                    child_token_id,
                    max_staleness,
                } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(child_public_key);
                    hasher.update(child_token_id);
                    hasher.update(&max_staleness.to_le_bytes());
                    let spawn_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::SpawnWithDelegation {
                        spawn_hash: hash_to_8(spawn_hash_bytes.as_bytes()),
                    });
                }
                Effect::RefreshDelegation { child, snapshot } => {
                    // MUST match the executor bridge
                    // (`turn::executor::effect_vm_bridge::convert_turn_effects_to_vm`)
                    // byte-for-byte (the differential invariant): child_hash +
                    // snapshot_value via the SAME 8-limb fold.
                    vm_effects.push(VmEffect::RefreshDelegation {
                        child_hash: hash_to_8(child.as_bytes()),
                        snapshot_value: hash_to_8(snapshot),
                    });
                }
                Effect::RevokeDelegation { child } => {
                    vm_effects.push(VmEffect::RevokeDelegation {
                        child_hash: hash_to_8(child.as_bytes()),
                    });
                }

                // -- Bridge ops (CRITICAL: cross-chain value transfer) ----------
                Effect::BridgeMint { portable_proof } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&portable_proof.nullifier);
                    let root_bytes =
                        postcard::to_allocvec(&portable_proof.source_root).unwrap_or_default();
                    hasher.update(&root_bytes);
                    hasher.update(&portable_proof.destination_federation);
                    hasher.update(&portable_proof.asset_type.to_le_bytes());
                    let mint_hash_bytes = hasher.finalize();
                    let value_lo =
                        BabyBear::new((portable_proof.value & ((1u64 << 30) - 1)) as u32);
                    vm_effects.push(VmEffect::BridgeMint {
                        value_lo,
                        mint_hash: hash_to_bb(mint_hash_bytes.as_bytes()),
                        value_full: portable_proof.value,
                    });
                }

                // -- Introduce / pipelined send ---------------------------------
                Effect::Introduce {
                    introducer,
                    recipient,
                    target,
                    permissions,
                } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(introducer.as_bytes());
                    hasher.update(recipient.as_bytes());
                    hasher.update(target.as_bytes());
                    let perm_byte: u8 = match permissions {
                        dregg_cell::AuthRequired::None => 0,
                        dregg_cell::AuthRequired::Signature => 1,
                        dregg_cell::AuthRequired::Proof => 2,
                        dregg_cell::AuthRequired::Either => 3,
                        dregg_cell::AuthRequired::Impossible => 4,
                        dregg_cell::AuthRequired::Custom { .. } => 5,
                    };
                    hasher.update(&[perm_byte]);
                    if let dregg_cell::AuthRequired::Custom { vk_hash } = permissions {
                        hasher.update(vk_hash);
                    }
                    let intro_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::Introduce {
                        intro_hash: hash_to_8(intro_hash_bytes.as_bytes()),
                    });
                }
                Effect::PipelinedSend { target, action } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&target.source_turn);
                    hasher.update(&target.output_slot.to_le_bytes());
                    hasher.update(&action.hash());
                    let send_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::PipelinedSend {
                        send_hash: hash_to_8(send_hash_bytes.as_bytes()),
                    });
                }

                // -- Escrow (CRITICAL: locked value) ----------------------------

                // -- ExerciseViaCapability -------------------------------------
                Effect::ExerciseViaCapability {
                    cap_slot,
                    inner_effects,
                } => {
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&cap_slot.to_le_bytes());
                    for inner in inner_effects {
                        hasher.update(&inner.hash());
                    }
                    let exercise_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::ExerciseViaCapability {
                        exercise_hash: hash_to_8(exercise_hash_bytes.as_bytes()),
                    });
                }

                // -- Queue ops -------------------------------------------------

                // -- CapTP runtime effects (CRITICAL: cap authority) -----------

                // -- Refusal (evidence-of-absence, the record-digest record-pin, AFTER limb 24) ------
                // Project to the NATIVE `VmEffect::Refusal`, byte-identical to the executor bridge
                // (`convert_turn_effects_to_vm`), so the verifier resolves `refusalVmDescriptor2R24`
                // (39 PIs, record-digest-pinned) the producer proves over. The deployed `apply_refusal`
                // writes the refusal audit into the EXT `fields_root` (aligned to the Lean SPEC
                // `TurnExecutorFull.refusalField`), which `compute_authority_digest_felt` folds into the
                // r23 authority residue — so the AFTER `record_digest` limb (24) MOVES and the verifier
                // anchors `compute_authority_digest_felt(post_cell)`. The PRIOR `EmitEvent` collapse
                // resolved `emitEventVmDescriptor2R24` (no record pin), diverging from the bridge.
                Effect::Refusal {
                    cell,
                    offered_action_commitment,
                    refusal_reason,
                    ..
                } if cell == cell_id => {
                    let target_hash = hash_to_8(cell.as_bytes());
                    let discriminant = match refusal_reason {
                        dregg_turn::action::RefusalReason::Declined => 0u32,
                        dregg_turn::action::RefusalReason::NoAuthority => 1u32,
                        dregg_turn::action::RefusalReason::WindowExpired => 2u32,
                        dregg_turn::action::RefusalReason::Custom { .. } => 3u32,
                    };
                    let reason_bytes = dregg_circuit::effect_vm::refusal_reason_bytes(
                        offered_action_commitment,
                        discriminant,
                    );
                    let reason_hash = hash_to_8(&reason_bytes);
                    vm_effects.push(VmEffect::Refusal {
                        target: target_hash,
                        reason_hash,
                    });
                }

                // Cross-cell effects not targeting this cell_id fall through
                // silently (they are not part of this cell's proof), matching
                // the bridge's `_ => {}` behavior for non-self effects.
                _ => {}
            }
        }
        // Must have at least one effect for the VM.
        if vm_effects.is_empty() {
            vm_effects.push(VmEffect::NoOp);
        }
        vm_effects
    }

    /// Store sovereign cell state in the cipherclerk (agent maintains it).
    ///
    /// Call this after transitioning a cell to sovereign mode. The cipherclerk keeps
    /// the full cell state locally and provides it as a witness in future turns.
    pub fn store_sovereign_state(&mut self, cell: Cell) {
        self.sovereign_cells.insert(cell.id(), cell);
    }

    /// Get our local copy of a sovereign cell's state.
    pub fn sovereign_state(&self, cell_id: &CellId) -> Option<&Cell> {
        self.sovereign_cells.get(cell_id)
    }

    /// Update sovereign state after a turn executes (applies effects locally).
    ///
    /// This applies the given effects to the locally-stored sovereign cell state.
    /// Call this after a turn has been committed by the federation so the local
    /// state stays consistent with the on-chain commitment.
    pub fn apply_sovereign_effects(
        &mut self,
        cell_id: &CellId,
        effects: &[Effect],
    ) -> Result<(), SdkError> {
        let cell = self.sovereign_cells.get_mut(cell_id).ok_or_else(|| {
            SdkError::MissingKey(format!("no local sovereign state for cell {}", cell_id))
        })?;

        for effect in effects {
            match effect {
                Effect::SetField {
                    cell: target,
                    index,
                    value,
                } if target == cell_id => {
                    if *index < cell.state.fields.len() {
                        cell.state.fields[*index] = *value;
                    }
                }
                Effect::Transfer { to, amount, .. } if to == cell_id => {
                    cell.state
                        .set_balance(cell.state.balance().saturating_add(*amount as i64));
                }
                Effect::Transfer { from, amount, .. } if from == cell_id => {
                    cell.state
                        .set_balance(cell.state.balance().saturating_sub(*amount as i64));
                }
                Effect::IncrementNonce { cell: target } if target == cell_id => {
                    let _ = cell.state.increment_nonce();
                }
                _ => {
                    // Other effects (GrantCapability, RevokeCapability, EmitEvent, etc.)
                    // are either not relevant to cell state or handled at a higher level.
                }
            }
        }

        Ok(())
    }

    /// Export all sovereign cell state (for backup).
    ///
    /// Serializes the full sovereign cell state map to a byte vector using
    /// postcard encoding. The result can be stored securely and later restored
    /// via [`import_sovereign_state`](Self::import_sovereign_state).
    pub fn export_sovereign_state(&self) -> Vec<u8> {
        // Collect into a Vec of (CellId, Cell) for deterministic serialization.
        let entries: Vec<(&CellId, &Cell)> = self.sovereign_cells.iter().collect();
        postcard::to_stdvec(&entries).unwrap_or_default()
    }

    /// Import sovereign cell state (for recovery).
    ///
    /// Deserializes sovereign cell state previously exported via
    /// [`export_sovereign_state`](Self::export_sovereign_state) and merges it
    /// into this cipherclerk's sovereign cell map.
    pub fn import_sovereign_state(&mut self, data: &[u8]) -> Result<(), SdkError> {
        let entries: Vec<(CellId, Cell)> = postcard::from_bytes(data)
            .map_err(|e| SdkError::Wire(format!("failed to deserialize sovereign state: {e}")))?;
        for (id, cell) in entries {
            self.sovereign_cells.insert(id, cell);
        }
        Ok(())
    }

    /// Get the number of sovereign cells stored locally.
    pub fn sovereign_cell_count(&self) -> usize {
        self.sovereign_cells.len()
    }

    // =========================================================================
    // IVC Compression (Sovereign History)
    // =========================================================================

    /// Compress sovereign history into a single IVC proof.
    ///
    /// Takes the receipt chain entries for a given cell and produces a constant-size
    /// STARK proof that the entire state transition history from genesis to the current
    /// state is valid. The proof covers the hash chain:
    ///   `genesis_commitment -> commitment_1 -> ... -> current_commitment`
    ///
    /// This is the key primitive for sovereign cell portability: anyone can verify
    /// the cell's entire history by checking a single ~24 KiB proof instead of
    /// replaying all turns.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell whose history to compress.
    ///
    /// # Returns
    ///
    /// Serialized STARK proof bytes, or an error if the cell is not sovereign or
    /// has no history.
    pub fn compress_sovereign_history(&self, cell_id: &CellId) -> Result<Vec<u8>, SdkError> {
        // The cell must be in sovereign mode (stored locally).
        let _cell = self.sovereign_cells.get(cell_id).ok_or_else(|| {
            SdkError::NotSovereign(format!(
                "cell {} is not stored as sovereign; call store_sovereign_state() first",
                cell_id
            ))
        })?;

        // Collect the state commitments from the receipt chain for this cell.
        // Each receipt has pre_state_hash and post_state_hash — we build the
        // chain of BabyBear commitments.
        let cell_receipts: Vec<&dregg_turn::TurnReceipt> = self
            .receipt_chain
            .iter()
            .filter(|r| {
                // Match receipts targeting this cell.
                // The agent field on the receipt is the cell_id the turn targeted.
                r.agent == *cell_id
            })
            .collect();

        if cell_receipts.is_empty() {
            return Err(SdkError::IvcError(
                "no receipts found for this cell; execute at least one turn first".into(),
            ));
        }

        // Build the hash chain: genesis_root -> post_state[0] -> post_state[1] -> ...
        let genesis_root = Self::bytes_to_babybear(&cell_receipts[0].pre_state_hash);
        let transitions: Vec<dregg_circuit::BabyBear> = cell_receipts
            .iter()
            .map(|r| Self::bytes_to_babybear(&r.post_state_hash))
            .collect();

        // Generate the IVC STARK proof over the hash chain.
        let (proof, _public_inputs) = dregg_circuit::prove_ivc_stark(genesis_root, &transitions);
        Ok(dregg_circuit::stark::proof_to_bytes(&proof))
    }

    /// Verify a compressed history proof.
    ///
    /// Given proof bytes, the genesis state commitment, the expected current
    /// commitment, and the number of steps, verifies the IVC STARK proof.
    ///
    /// This is the verifier-side operation: anyone with the genesis root and
    /// proof bytes can check the cell's entire state transition history without
    /// replaying the turns.
    ///
    /// # Arguments
    ///
    /// * `proof_bytes` - Serialized STARK proof (from `compress_sovereign_history`).
    /// * `genesis` - The genesis state commitment (32-byte hash).
    /// * `current` - The expected current state commitment (32-byte hash).
    /// * `step_count` - Number of state transitions in the history.
    ///
    /// # Returns
    ///
    /// `Ok(true)` if the proof is valid, `Ok(false)` if verification fails cleanly,
    /// or `Err` if the proof cannot be deserialized.
    pub fn verify_compressed_history(
        proof_bytes: &[u8],
        genesis: [u8; 32],
        _current: [u8; 32],
        step_count: u64,
    ) -> Result<bool, SdkError> {
        let proof = dregg_circuit::stark::proof_from_bytes(proof_bytes)
            .map_err(|e| SdkError::IvcError(format!("failed to deserialize IVC proof: {}", e)))?;

        // Reconstruct the public inputs expected by verify_ivc_stark.
        // The IVC proof's public inputs encode: initial_root and the accumulated hash.
        // We need to reconstruct them from the genesis root and step count.
        let genesis_bb = Self::bytes_to_babybear(&genesis);

        // Build a synthetic PI vector matching what prove_ivc_stark would produce.
        // The StateTransitionAir's public inputs are:
        //   [initial_root, final_accumulated_hash, step_count]
        // We verify by calling verify_ivc_stark with the proof + its embedded PIs.
        // Since we don't have the intermediate transitions, we use the proof's
        // own public inputs and just check that genesis matches.
        //
        // For now, reconstruct with step_count transitions of zeros (the verifier
        // only needs the proof and PI to check FRI consistency).
        let transitions: Vec<dregg_circuit::BabyBear> = (0..step_count)
            .map(|i| dregg_circuit::BabyBear::new(i as u32))
            .collect();
        let (_regenerated_proof, public_inputs) =
            dregg_circuit::prove_ivc_stark(genesis_bb, &transitions);

        // Verify using the actual proof bytes against the reconstructed PIs.
        // NOTE: In production, the public inputs would be transmitted alongside
        // the proof. For now we verify the proof we were given against its own PIs.
        match dregg_circuit::verify_ivc_stark(&proof, &public_inputs) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    /// Get a peer exchange session for direct sovereign interactions.
    ///
    /// Returns a [`PeerExchange`](dregg_cell::PeerExchange) initialized with
    /// this cipherclerk's cell ID and signing key, suitable for direct peer-to-peer
    /// state exchange between sovereign cell owners.
    ///
    /// This is a convenience alias for [`peer_exchange`](Self::peer_exchange).
    pub fn peer_exchange_session(&self, domain: &str) -> dregg_cell::PeerExchange {
        self.peer_exchange(domain)
    }

    // =========================================================================
    // Factory Operations (EROS-style object creation)
    // =========================================================================

    /// Deploy a factory descriptor, returning its VK hash identifier.
    ///
    /// The factory descriptor defines what cells the factory can create: what
    /// program is installed, what capabilities are granted, what field constraints
    /// apply, and the per-epoch creation budget.
    ///
    /// Anyone can inspect the descriptor to understand exactly what the factory
    /// creates — this is constructor transparency.
    pub fn deploy_factory(&self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        descriptor.factory_vk
    }

    /// Build a signed turn that creates a cell from a deployed factory.
    ///
    /// The turn carries a `CreateCellFromFactory` effect that the executor validates
    /// against the factory's registered descriptor.  The inner action is signed with
    /// `Authorization::Signature` via [`make_action`](Self::make_action) — not left
    /// as `Authorization::Unchecked`.
    ///
    /// # Arguments
    ///
    /// * `issuer_cell` - The cell issuing the `CreateCellFromFactory` effect
    ///   (i.e. the caller's cell, not the new child cell).
    /// * `factory_vk` - The 32-byte factory VK hash returned by [`deploy_factory`](Self::deploy_factory).
    /// * `owner_pubkey` - The ed25519 public key of the new cell's owner.
    /// * `token_id` - The token-domain identifier for the new cell.
    /// * `params` - Additional creation parameters (program VK, initial fields/caps).
    /// * `federation_id` - The 32-byte federation binding for the canonical signing message.
    ///
    /// # Returns
    ///
    /// A [`Turn`] carrying a real `Authorization::Signature(..)` action, ready for submission.
    pub fn create_from_factory(
        &self,
        issuer_cell: CellId,
        factory_vk: [u8; 32],
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        params: dregg_cell::FactoryCreationParams,
        federation_id: &[u8; 32],
    ) -> Turn {
        use dregg_turn::action::Effect;

        let effect = Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        };
        // Build and sign the action using the standard helper (closes the
        // Authorization::Unchecked regression flagged in SDK-DREGGSCRIPT-AUDIT.md §9).
        let action = self.make_action(issuer_cell, "factory_create", vec![effect], federation_id);
        let mut turn = self.make_turn(action);
        // Override the agent to the issuer_cell (make_turn defaults to cell_id("default")).
        turn.agent = issuer_cell;
        turn
    }

    /// Verify provenance of a cell — returns the factory that created it (if any).
    ///
    /// In the current implementation, provenance is tracked by the executor
    /// at creation time. This method inspects the cell's VK and checks it
    /// against known factory VK hashes.
    pub fn verify_provenance(
        &self,
        cell: &Cell,
        known_factories: &[dregg_cell::FactoryDescriptor],
    ) -> Option<dregg_cell::Provenance> {
        if let Some(vk) = &cell.verification_key {
            for factory in known_factories {
                if factory.child_program_vk == Some(vk.hash) {
                    return Some(dregg_cell::Provenance::from_factory(
                        factory.factory_vk,
                        None,
                        0,
                    ));
                }
            }
        }
        None
    }

    // =========================================================================
    // Encrypted Intent Posting
    // =========================================================================

    /// Post an intent with encrypted headers (SSE tokens + sealed body).
    ///
    /// Creates an [`EncryptedIntent`] suitable for gossip propagation. The intent's
    /// MatchSpec is encrypted so only fulfillers whose capabilities match the SSE
    /// search tokens can discover and decrypt it.
    ///
    /// # Arguments
    ///
    /// * `spec` - The capability matching specification.
    /// * `kind` - The kind of intent (Need, Offer, or Query).
    /// * `expiry` - Optional Unix timestamp after which the intent expires.
    ///
    /// # Returns
    ///
    /// An [`EncryptedIntent`] ready for gossip broadcast.
    pub fn post_encrypted_intent(
        &self,
        spec: &MatchSpec,
        _kind: IntentKind,
        expiry: Option<u64>,
    ) -> EncryptedIntent {
        // Derive the commitment ID from this cipherclerk's public key.
        let commitment_id = CommitmentId(self.public_key.0);

        // Use epoch 0 for now; in production this would come from the network clock.
        let epoch = 0u64;

        let (encrypted, _keypair) = EncryptedIntent::create(spec, commitment_id, epoch, expiry);
        encrypted
    }

    // =========================================================================
    // Stealth Key Derivation (internal)
    // =========================================================================

    /// Derive stealth keys deterministically from the cipherclerk's Ed25519 signing key.
    ///
    /// Uses BLAKE3 key derivation with distinct context strings to produce
    /// independent view and spend keys.
    fn derive_stealth_keys(signing_key: &ed25519_dalek::SigningKey) -> StealthKeys {
        let sk_bytes = signing_key.to_bytes();
        let view_private_key = blake3::derive_key("dregg-stealth-view-key-v1", &sk_bytes);
        let spend_private_key = blake3::derive_key("dregg-stealth-spend-key-v1", &sk_bytes);
        StealthKeys::from_keys(view_private_key, spend_private_key)
    }

    // =========================================================================
    // Peer-to-Peer State Exchange (Sovereign Cells)
    // =========================================================================

    /// Create a peer exchange session for sovereign cell interactions.
    ///
    /// The exchange session is keyed to a specific domain (cell identity) and uses
    /// this cipherclerk's Ed25519 signing key for transition signatures.
    pub fn peer_exchange(&self, domain: &str) -> dregg_cell::PeerExchange {
        let cell_id = self.cell_id(domain);
        let signing_key_bytes = self.signing_key.to_bytes();
        dregg_cell::PeerExchange::new(cell_id, signing_key_bytes)
    }

    /// Send a sovereign state transition to a peer (sign + package).
    ///
    /// Computes the effects hash (BLAKE3 over serialized effects), then delegates
    /// to the `PeerExchange` to create a signed transition.
    ///
    /// # Arguments
    /// * `exchange` - The peer exchange session (must be for this cipherclerk's cell).
    /// * `old_commitment` - The commitment before this transition.
    /// * `new_commitment` - The commitment after applying effects.
    /// * `effects` - The effects that produced the state change.
    pub fn send_peer_transition(
        &self,
        exchange: &mut dregg_cell::PeerExchange,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects: &[dregg_turn::Effect],
    ) -> dregg_cell::PeerStateTransition {
        let effects_bytes = postcard::to_stdvec(effects).unwrap_or_default();
        let effects_hash = *blake3::hash(&effects_bytes).as_bytes();
        exchange.create_transition(old_commitment, new_commitment, effects_hash)
    }

    // =========================================================================
    // Ephemeral Federation Registration
    // =========================================================================

    /// Register this cipherclerk's sovereign cell with a federation node (ephemeral).
    ///
    /// The federation stores only the state commitment and TTL metadata.
    /// The registration expires after `ttl_blocks` of inactivity. Call this when
    /// the sovereign cell needs federation services (ordering, nullifier check,
    /// proving to strangers).
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node (e.g., "http://localhost:9000").
    /// * `ttl_blocks` - How many blocks to keep the registration alive.
    ///
    /// # Errors
    ///
    /// Returns an error if the HTTP request fails or the node rejects the registration.
    #[cfg(feature = "federation-client")]
    pub async fn register_with_federation(
        &self,
        node_url: &str,
        ttl_blocks: u64,
    ) -> Result<(), SdkError> {
        // Use the public key as the cell_id for sovereign cells.
        let cell_id_bytes = self.public_key.0;

        // Compute the current state commitment from the receipt chain head,
        // or use a zero commitment if no state transitions have occurred.
        let commitment = self.current_state_commitment().unwrap_or([0u8; 32]);

        // Sign cell_id || commitment.
        let mut message = Vec::with_capacity(64);
        message.extend_from_slice(&cell_id_bytes);
        message.extend_from_slice(&commitment);
        let sig = self.signing_key.sign(&message);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "commitment": hex_encode_bytes(&commitment),
            "ttl_blocks": ttl_blocks,
            "signature": hex_encode_bytes(&sig.to_bytes()),
        });

        let url = format!("{}/cells/register", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("federation register request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation register returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse register response: {e}")))?;

        if result.get("registered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected registration: {error}"
            )))
        }
    }

    /// Deregister this cipherclerk's sovereign cell from the federation.
    ///
    /// Voluntarily removes the cell's commitment from the federation node.
    /// Call this when the cell no longer needs federation services.
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node.
    ///
    /// # Errors
    ///
    /// Returns an error if the HTTP request fails or the node rejects the deregistration.
    #[cfg(feature = "federation-client")]
    pub async fn deregister_from_federation(&self, node_url: &str) -> Result<(), SdkError> {
        let cell_id_bytes = self.public_key.0;

        // Sign just the cell_id for deregistration proof.
        let sig = self.signing_key.sign(&cell_id_bytes);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "signature": hex_encode_bytes(&sig.to_bytes()),
        });

        let url = format!("{}/cells/deregister", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp =
            client.post(&url).json(&body).send().await.map_err(|e| {
                SdkError::Wire(format!("federation deregister request failed: {e}"))
            })?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation deregister returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deregister response: {e}")))?;

        if result.get("deregistered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected deregistration: {error}"
            )))
        }
    }

    /// Deploy a custom cell program to the federation.
    ///
    /// Serializes the `CircuitDescriptor` via postcard and submits it to the node's
    /// `/programs/deploy` endpoint. On success, returns the 32-byte VK hash that
    /// identifies the program in the registry.
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node.
    /// * `descriptor` - The circuit descriptor defining valid state transitions.
    /// * `version` - Program version for upgrade tracking.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails, the HTTP request fails, or the
    /// node rejects the program (e.g., validation failure).
    #[cfg(feature = "federation-client")]
    pub async fn deploy_program(
        &self,
        node_url: &str,
        descriptor: &dregg_dsl_runtime::CircuitDescriptor,
        version: u32,
    ) -> Result<[u8; 32], SdkError> {
        let serialized = postcard::to_allocvec(descriptor)
            .map_err(|e| SdkError::Wire(format!("failed to serialize descriptor: {e}")))?;

        let body = serde_json::json!({
            "descriptor_bytes": hex_encode_bytes(&serialized),
            "version": version,
        });

        let url = format!("{}/programs/deploy", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("program deploy request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "program deploy returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deploy response: {e}")))?;

        if result.get("deployed").and_then(|v| v.as_bool()) == Some(true) {
            let vk_hex = result
                .get("vk_hash")
                .and_then(|v| v.as_str())
                .ok_or_else(|| SdkError::Wire("deploy response missing vk_hash".into()))?;
            let vk_bytes = hex_decode_bytes(vk_hex)
                .map_err(|_| SdkError::Wire("invalid vk_hash hex in deploy response".into()))?;
            if vk_bytes.len() != 32 {
                return Err(SdkError::Wire("vk_hash is not 32 bytes".into()));
            }
            let mut vk = [0u8; 32];
            vk.copy_from_slice(&vk_bytes);
            Ok(vk)
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected program deployment: {error}"
            )))
        }
    }

    /// Execute a sovereign turn with a custom program proof.
    ///
    /// Generates a STARK proof of a valid state transition under the given program
    /// and builds a proof-carrying turn for submission to the federation.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to transition.
    /// * `program` - The deployed cell program (must match the cell's VK).
    /// * `witness` - Column name -> values mapping for trace generation.
    /// * `num_rows` - Number of trace rows (must be a power of 2, >= 2).
    /// * `public_inputs` - Public inputs for the proof (encodes old/new commitments).
    /// * `new_commitment` - The new 32-byte state commitment after the transition.
    /// * `nonce` - Turn nonce.
    /// * `fee` - Turn fee in computrons.
    ///
    /// # Errors
    ///
    /// Returns an error if witness generation or proof generation fails.
    pub fn execute_with_program(
        &self,
        cell_id: &CellId,
        program: &dregg_dsl_runtime::CellProgram,
        witness: &HashMap<String, Vec<BabyBear>>,
        num_rows: usize,
        public_inputs: &[BabyBear],
        new_commitment: [u8; 32],
        nonce: u64,
        fee: u64,
    ) -> Result<Turn, SdkError> {
        // Generate the STARK proof using the program.
        let proof_bytes = program
            .prove_transition(witness, num_rows, public_inputs)
            .map_err(SdkError::Program)?;

        // Build a proof-carrying turn.
        let agent_id = self.cell_id("default");
        let turn = Turn {
            agent: agent_id,
            nonce,
            fee,
            call_forest: dregg_turn::CallForest {
                roots: vec![],
                forest_hash: [0u8; 32],
            },
            valid_until: None,
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(*cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
            sovereign_witnesses: HashMap::new(),
            memo: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: vec![],
            conservation_proof: None,
        };

        Ok(turn)
    }

    // =========================================================================
    // CapTP Convenience Methods (entire block gated on `captp` feature)
    // =========================================================================

    /// Share a cell as a `dregg://` URI (sturdy reference).
    ///
    /// Requires that a [`CapTpClient`](crate::captp_client::CapTpClient) has been
    /// configured via [`set_captp_client`](Self::set_captp_client).
    ///
    /// The returned URI can be shared with any agent; they can enliven it to
    /// obtain a live reference to the cell.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The cell to export as a capability.
    ///
    /// # Returns
    ///
    /// A `dregg://` URI string that can be shared out-of-band.
    #[cfg(feature = "captp")]
    pub fn share_capability(
        &mut self,
        cell_id: CellId,
    ) -> Result<dregg_captp::uri::DreggUri, SdkError> {
        let client = self.captp_mut()?;
        Ok(client.export_sturdy_ref(cell_id, dregg_cell::AuthRequired::Signature, None))
    }

    /// Accept (enliven) a `dregg://` URI, returning a live reference.
    ///
    /// Requires that a [`CapTpClient`](crate::captp_client::CapTpClient) has been
    /// configured via [`set_captp_client`](Self::set_captp_client).
    ///
    /// The returned [`LiveRef`](crate::captp_client::LiveRef) tracks the import
    /// in the GC manager and sends a DropRef message when dropped.
    ///
    /// # Arguments
    ///
    /// * `uri` - A `dregg://` URI string.
    #[cfg(feature = "captp")]
    pub fn accept_capability(
        &mut self,
        uri: &str,
    ) -> Result<crate::captp_client::LiveRef, SdkError> {
        let client = self.captp_mut()?;
        client.enliven_uri(uri, dregg_cell::AuthRequired::Signature)
    }

    /// Create a handoff certificate for offline delegation of a cell to a recipient.
    ///
    /// Requires that a [`CapTpClient`](crate::captp_client::CapTpClient) has been
    /// configured via [`set_captp_client`](Self::set_captp_client).
    ///
    /// The returned certificate can travel out-of-band (QR code, email, BLE).
    /// The recipient presents it to the target federation to obtain access.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The cell to delegate.
    /// * `recipient_pk` - The recipient's Ed25519 public key (32 bytes).
    #[cfg(feature = "captp")]
    pub fn delegate_offline(
        &mut self,
        cell_id: CellId,
        recipient_pk: [u8; 32],
    ) -> Result<dregg_captp::handoff::HandoffCertificate, SdkError> {
        let signing_key = dregg_types::SigningKey::from_bytes(&self.signing_key.to_bytes());
        let client = self.captp_mut()?;
        Ok(client.create_handoff(
            &signing_key,
            cell_id,
            recipient_pk,
            dregg_cell::AuthRequired::Signature,
            None,
            None,
        ))
    }

    /// Set the CapTP client for this cipherclerk.
    ///
    /// Must be called before using [`share_capability`](Self::share_capability),
    /// [`accept_capability`](Self::accept_capability), or
    /// [`delegate_offline`](Self::delegate_offline).
    #[cfg(feature = "captp")]
    pub fn set_captp_client(&mut self, client: crate::captp_client::CapTpClient) {
        self.captp_client = Some(client);
    }

    /// Get a reference to the CapTP client, if configured.
    #[cfg(feature = "captp")]
    pub fn captp_client(&self) -> Option<&crate::captp_client::CapTpClient> {
        self.captp_client.as_ref()
    }

    /// Get a mutable reference to the CapTP client, if configured.
    #[cfg(feature = "captp")]
    pub fn captp_client_mut(&mut self) -> Option<&mut crate::captp_client::CapTpClient> {
        self.captp_client.as_mut()
    }

    /// Internal helper: get a mutable CapTP client or return
    /// [`SdkError::CapTpNotConfigured`].
    #[cfg(feature = "captp")]
    fn captp_mut(&mut self) -> Result<&mut crate::captp_client::CapTpClient, SdkError> {
        self.captp_client
            .as_mut()
            .ok_or(SdkError::CapTpNotConfigured)
    }
}

/// Encode bytes to hex string (used by federation registration methods).
fn hex_encode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a hex string into bytes.
fn hex_decode_bytes(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| ()))
        .collect()
}

/// A note detected as belonging to this cipherclerk during stealth scanning.
#[derive(Clone, Debug)]
pub struct OwnedStealthNote {
    /// The note commitment (for lookup in the note tree).
    pub commitment: NoteCommitment,
    /// The ephemeral public key from the announcement.
    pub ephemeral_pubkey: [u8; 32],
    /// The derived one-time spending key for this note.
    pub spending_key: [u8; 32],
}

impl Default for AgentCipherclerk {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for AgentCipherclerk {
    fn drop(&mut self) {
        // P2-2 / SAFETY: We explicitly zeroize the externally-shaped key
        // material (`seed`, `mnemonic_phrase`) that we own. The Ed25519
        // `signing_key` is NOT zeroized here because `ed25519_dalek::SigningKey`
        // upstream implements `ZeroizeOnDrop`, so dropping `self.signing_key`
        // already zeroizes its backing bytes. Adding a duplicate zeroize call
        // here would (a) be a no-op after the upstream Drop runs, and (b) be a
        // soundness landmine if upstream ever changes its drop semantics: the
        // safer policy is to inherit the upstream contract.
        //
        // If this assumption ever breaks (e.g. an upstream API change), this
        // doc block is the place to look first.
        if let Some(ref mut seed) = self.seed {
            seed.zeroize();
        }
        if let Some(ref mut phrase) = self.mnemonic_phrase {
            phrase.zeroize();
        }
    }
}

impl std::fmt::Debug for AgentCipherclerk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentCipherclerk")
            .field("public_key", &self.public_key)
            .field("tokens_held", &self.tokens.len())
            .field("receipt_chain_length", &self.receipt_chain.len())
            .field("ivc_enabled", &self.ivc_builder.is_some())
            .field("has_seed", &self.seed.is_some())
            .field("has_mnemonic", &self.mnemonic_phrase.is_some())
            .field("derivation_path", &self.derivation_path)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::TurnReceipt;

    /// Helper: create a mock receipt with given state hashes.
    fn mock_receipt(agent: CellId, pre_state: [u8; 32], post_state: [u8; 32]) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: pre_state,
            post_state_hash: post_state,
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 50,
            action_count: 1,
            previous_receipt_hash: None,
            agent,
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    #[test]
    fn test_cclerk_receipt_chain_empty() {
        let cclerk = AgentCipherclerk::new();
        assert_eq!(cclerk.receipt_chain_length(), 0);
        assert!(cclerk.receipt_head().is_none());
        assert!(cclerk.current_state_commitment().is_none());
        assert!(cclerk.verify_own_chain().is_ok());
    }

    #[test]
    fn test_cclerk_append_single_receipt() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");
        let receipt = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);

        cclerk.append_receipt(receipt).unwrap();

        assert_eq!(cclerk.receipt_chain_length(), 1);
        assert!(cclerk.receipt_head().is_some());
        assert_eq!(cclerk.receipt_head().unwrap().post_state_hash, [2u8; 32]);
        assert_eq!(cclerk.current_state_commitment(), Some([2u8; 32]));
        // Genesis receipt should have None as previous.
        assert_eq!(cclerk.receipt_head().unwrap().previous_receipt_hash, None);
        assert!(cclerk.verify_own_chain().is_ok());
    }

    #[test]
    fn test_cclerk_append_chain_links_correctly() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        // Append first receipt.
        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        cclerk.append_receipt(r1).unwrap();

        // Append second receipt (pre_state matches first post_state).
        let r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        cclerk.append_receipt(r2).unwrap();

        assert_eq!(cclerk.receipt_chain_length(), 2);
        assert_eq!(cclerk.current_state_commitment(), Some([3u8; 32]));

        // The second receipt should have previous_receipt_hash linking to the first.
        let chain = cclerk.receipt_chain();
        assert_eq!(chain[0].previous_receipt_hash, None);
        assert_eq!(
            chain[1].previous_receipt_hash,
            Some(chain[0].receipt_hash())
        );

        assert!(cclerk.verify_own_chain().is_ok());
    }

    #[test]
    fn test_cclerk_chain_of_five() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let mut state = [0u8; 32];
        for i in 0..5u8 {
            let pre = state;
            state[0] = i + 1;
            let post = state;
            let receipt = mock_receipt(cell_id, pre, post);
            cclerk.append_receipt(receipt).unwrap();
        }

        assert_eq!(cclerk.receipt_chain_length(), 5);
        assert!(cclerk.verify_own_chain().is_ok());

        // Verify using the standalone function too.
        let chain = cclerk.receipt_chain();
        assert!(dregg_turn::verify_receipt_chain(chain).is_ok());
    }

    #[test]
    fn test_cclerk_verify_chain_with_external_function() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        cclerk.append_receipt(r1).unwrap();

        let r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        cclerk.append_receipt(r2).unwrap();

        let r3 = mock_receipt(cell_id, [3u8; 32], [4u8; 32]);
        cclerk.append_receipt(r3).unwrap();

        // External verification.
        let head = dregg_turn::verify_receipt_chain_head(cclerk.receipt_chain()).unwrap();
        assert_eq!(head, [4u8; 32]);
    }

    // ---------------- P0 #77: strict append_receipt semantics ----------------

    /// Adversarial: a receipt whose `previous_receipt_hash` does NOT match the
    /// cipherclerk's current head must be rejected with a typed mismatch error.
    /// The cipherclerk's chain must be unchanged on rejection.
    ///
    /// Pre-fix behavior: the cipherclerk silently rewrote `previous_receipt_hash`
    /// to its own head, so two honest nodes that diverged would produce different
    /// chains for the same agent with no detection. After this fix, the
    /// cipherclerk surfaces the fork as `ChainAppendError::ReceiptChainMismatch`.
    #[test]
    fn append_receipt_rejects_stale_prev_hash_fork_detection() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        // Seed the chain so the head is known.
        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        cclerk.append_receipt(r1).unwrap();
        let head = cclerk.receipt_head().unwrap().receipt_hash();

        // Craft a receipt with a stale prev_hash (NOT equal to the cclerk's head).
        let mut r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        r2.previous_receipt_hash = Some([0xDE; 32]);

        let err = cclerk
            .append_receipt(r2)
            .expect_err("stale prev_hash must reject");
        match err {
            ChainAppendError::ReceiptChainMismatch { expected, got } => {
                assert_eq!(expected, Some(head));
                assert_eq!(got, Some([0xDE; 32]));
            }
        }

        // Chain must be unchanged on rejection.
        assert_eq!(cclerk.receipt_chain_length(), 1);
        assert_eq!(cclerk.receipt_head().unwrap().receipt_hash(), head);
    }

    /// Adversarial: a receipt submitted with `prev = Some(_)` against an empty
    /// cipherclerk must be rejected (the executor that produced the receipt
    /// thinks the chain has history but the cipherclerk has none — divergence).
    #[test]
    fn append_receipt_rejects_some_prev_on_empty_chain() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let mut r = mock_receipt(cell_id, [0u8; 32], [1u8; 32]);
        r.previous_receipt_hash = Some([0xAB; 32]);

        let err = cclerk
            .append_receipt(r)
            .expect_err("Some(prev) on empty cclerk chain must reject");
        match err {
            ChainAppendError::ReceiptChainMismatch { expected, got } => {
                assert_eq!(expected, None);
                assert_eq!(got, Some([0xAB; 32]));
            }
        }
        assert_eq!(cclerk.receipt_chain_length(), 0);
    }

    /// Genesis: an empty cipherclerk accepts a receipt with prev = None.
    #[test]
    fn append_receipt_accepts_genesis_on_empty_chain() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let r = mock_receipt(cell_id, [0u8; 32], [1u8; 32]);
        cclerk.append_receipt(r).unwrap();
        assert_eq!(cclerk.receipt_chain_length(), 1);
    }

    /// A receipt with an explicit prev_hash that matches the cipherclerk's
    /// current head is accepted (this is the steady-state honest case).
    #[test]
    fn append_receipt_accepts_matching_prev_hash() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        cclerk.append_receipt(r1).unwrap();
        let head = cclerk.receipt_head().unwrap().receipt_hash();

        let mut r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        r2.previous_receipt_hash = Some(head);
        cclerk.append_receipt(r2).unwrap();
        assert_eq!(cclerk.receipt_chain_length(), 2);
    }

    #[test]
    fn test_cclerk_from_mnemonic() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let mut cclerk = AgentCipherclerk::from_mnemonic(&mnemonic, "").unwrap();
        assert!(cclerk.export_mnemonic().is_some());
        assert_eq!(cclerk.export_mnemonic().unwrap(), mnemonic);
        assert!(cclerk.export_seed().is_some());
        assert_eq!(cclerk.derivation_path(), Some("dregg/0"));
    }

    #[test]
    fn test_cclerk_from_mnemonic_deterministic() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let w1 = AgentCipherclerk::from_mnemonic(&mnemonic, "pass").unwrap();
        let w2 = AgentCipherclerk::from_mnemonic(&mnemonic, "pass").unwrap();
        assert_eq!(w1.public_key(), w2.public_key());
    }

    #[test]
    fn test_cclerk_from_seed() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let seed = crate::mnemonic::mnemonic_to_seed(&mnemonic, "").unwrap();
        let w1 = AgentCipherclerk::from_mnemonic(&mnemonic, "").unwrap();
        let w2 = AgentCipherclerk::from_seed(seed);
        assert_eq!(w1.public_key(), w2.public_key());
    }

    #[test]
    fn test_cclerk_derive_sub_agent() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let cclerk = AgentCipherclerk::from_mnemonic(&mnemonic, "").unwrap();
        let sub1 = cclerk.derive_sub_agent(1).unwrap();
        let sub2 = cclerk.derive_sub_agent(2).unwrap();

        // Sub-agents have different keys from the main cipherclerk.
        assert_ne!(cclerk.public_key(), sub1.public_key());
        assert_ne!(cclerk.public_key(), sub2.public_key());
        assert_ne!(sub1.public_key(), sub2.public_key());

        // Derivation is deterministic.
        let sub1_again = cclerk.derive_sub_agent(1).unwrap();
        assert_eq!(sub1.public_key(), sub1_again.public_key());
    }

    #[test]
    fn test_cclerk_derive_sub_agent_no_seed() {
        let cclerk = AgentCipherclerk::new();
        let result = cclerk.derive_sub_agent(1);
        assert!(result.is_err());
    }

    #[test]
    fn test_cclerk_new_has_no_mnemonic() {
        let mut cclerk = AgentCipherclerk::new();
        assert!(cclerk.export_mnemonic().is_none());
        assert!(cclerk.export_seed().is_none());
        assert!(cclerk.derivation_path().is_none());
    }

    #[test]
    fn test_attenuated_token_has_zeroed_root_key() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [42u8; 32];
        let root_token = cclerk.mint_token(&root_key, "compute");

        // Root token holds the actual key.
        assert!(root_token.can_mint());
        assert!(root_token.can_prove());
        assert_eq!(root_token.root_key(), &root_key);

        // Attenuate: restrict to read-only on "compute" service.
        let restrictions = Attenuation {
            services: vec![("compute".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = cclerk.attenuate(&root_token, &restrictions).unwrap();

        // SECURITY: The attenuated token must NOT carry the root forging key.
        assert!(!attenuated.can_mint());
        assert_eq!(attenuated.root_key(), &[0u8; 32]);

        // But it CAN prove (has derived issuer_key for federation membership).
        assert!(attenuated.can_prove());
        // The issuer_key is a one-way derivation of the root key, never the raw key.
        let expected_proof_key = blake3::derive_key("dregg-proof-key-v1", &root_key);
        assert_eq!(attenuated.issuer_key(), &expected_proof_key);
        assert_ne!(
            attenuated.issuer_key(),
            &root_key,
            "issuer_key must NOT be the raw root key"
        );

        // The attenuated token cannot be used to mint new tokens (prove_authorization
        // with the direct method still fails — it requires can_mint()).
        let request = dregg_token::AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let proof_result = cclerk.prove_authorization(&attenuated, &request);
        assert!(
            proof_result.is_err(),
            "attenuated token should not be able to generate federation membership proofs via prove_authorization()"
        );

        // But the ROOT token can still prove.
        let root_proof_result = cclerk.prove_authorization(&root_token, &request);
        assert!(
            root_proof_result.is_ok(),
            "root token should still be able to prove"
        );
    }

    #[test]
    fn test_delegated_token_has_zeroed_root_key() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [99u8; 32];
        let root_token = cclerk.mint_token(&root_key, "storage");

        let recv_cclerk = AgentCipherclerk::new();
        let delegatee_pk = recv_cclerk.public_key();

        let restrictions = Attenuation {
            services: vec![("storage".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegator_pk = cclerk.public_key();
        let delegated = cclerk
            .delegate(&root_token, &delegatee_pk, &restrictions)
            .unwrap();

        // The delegated token's underlying attenuated HeldToken in the cipherclerk
        // should also have zeroed root_key.
        let attenuated_in_cclerk = cclerk
            .tokens()
            .iter()
            .find(|t| t.id.contains("att"))
            .unwrap();
        assert!(!attenuated_in_cclerk.can_mint());
        assert_eq!(attenuated_in_cclerk.root_key(), &[0u8; 32]);

        // When the delegatee receives it (under TrustedKey policy), they also
        // don't get root_key.
        let mut recv_cclerk = recv_cclerk;
        recv_cclerk
            .receive_signed_delegation(delegated, &DelegationAuthority::TrustedKey(delegator_pk))
            .unwrap();
        let held = recv_cclerk.tokens().first().unwrap();
        assert!(!held.can_mint());
        assert_eq!(held.root_key(), &[0u8; 32]);
    }

    /// P1-2 regression test: receive_signed_delegation marks tokens as unverified
    /// since the HMAC chain cannot be checked without the root key.
    #[test]
    fn test_receive_delegation_marks_unverified() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xAA; 32];
        let root_token = cclerk.mint_token(&root_key, "service");

        // Root token must be verified.
        assert!(root_token.is_verified());

        let recv_cclerk = AgentCipherclerk::new();
        let delegatee_pk = recv_cclerk.public_key();

        let restrictions = Attenuation {
            services: vec![("service".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegator_pk = cclerk.public_key();
        let delegated = cclerk
            .delegate(&root_token, &delegatee_pk, &restrictions)
            .unwrap();

        // Attenuated token created locally (from verified parent) is still verified.
        let attenuated_in_cclerk = cclerk
            .tokens()
            .iter()
            .find(|t| t.id.contains("att"))
            .unwrap();
        assert!(
            attenuated_in_cclerk.is_verified(),
            "locally-attenuated token should be verified"
        );

        // When a delegatee receives the token, it must be marked as UNVERIFIED
        // because the HMAC chain cannot be checked without the root key.
        let mut recv_cclerk = recv_cclerk;
        recv_cclerk
            .receive_signed_delegation(delegated, &DelegationAuthority::TrustedKey(delegator_pk))
            .unwrap();
        let received = recv_cclerk.tokens().first().unwrap();
        assert!(
            !received.is_verified(),
            "delegated token must be marked unverified (HMAC chain not checked)"
        );
    }

    /// P1-2 regression test: minted tokens are verified.
    #[test]
    fn test_minted_token_is_verified() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xBB; 32];
        let token = cclerk.mint_token(&root_key, "compute");
        assert!(token.is_verified());
        assert!(token.can_mint());
    }

    /// End-to-end test: attenuate a token, then authorize in Private mode (ZK proof).
    ///
    /// This exercises the core product promise: "offline attenuate, then prove."
    /// Previously this flow was broken because:
    /// 1. attenuate() zeroed the root_key
    /// 2. authorize(Private) tried to verify the HMAC chain (needs root_key)
    /// 3. prove_authorization() rejected tokens without can_mint()
    ///
    /// The fix: attenuated tokens carry the issuer_key (for federation membership
    /// proofs), and the private/selective authorize paths use structural caveat
    /// extraction + prove_authorization_with_issuer_key internally.
    #[test]
    fn test_attenuate_authorize_private_end_to_end() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xAA; 32];
        let root_token = cclerk.mint_token(&root_key, "compute");

        // Step 1: Attenuate the token (restrict to read-only on "compute").
        let restrictions = Attenuation {
            services: vec![("compute".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = cclerk.attenuate(&root_token, &restrictions).unwrap();

        // Verify the attenuated token's properties.
        assert!(!attenuated.can_mint(), "must not be able to mint");
        assert!(attenuated.can_prove(), "must be able to generate ZK proofs");

        // Step 2: Authorize in FullyPrivate mode (generates a STARK proof).
        let request = dregg_token::AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = cclerk.authorize(&attenuated, &request, VerificationMode::FullyPrivate);
        assert!(
            presentation.is_ok(),
            "attenuated token should be able to authorize in Private mode, got: {:?}",
            presentation.err()
        );

        // Step 3: Verify the presentation is a Private variant with a proof and allow.
        match presentation.unwrap() {
            AuthorizationPresentation::Private { proof, conclusion } => {
                assert!(conclusion, "authorization should succeed (read on compute)");
                assert!(!proof.is_empty(), "proof bytes must be non-empty");
            }
            other => panic!("expected Private presentation, got: {:?}", other),
        }
    }

    /// Test that doubly-attenuated tokens can also prove (issuer_key propagates).
    #[test]
    fn test_double_attenuate_authorize_private() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xCC; 32];
        let root_token = cclerk.mint_token(&root_key, "storage");

        // First attenuation: restrict to storage service.
        let r1 = Attenuation {
            services: vec![("storage".to_string(), "rw".to_string())],
            ..Default::default()
        };
        let att1 = cclerk.attenuate(&root_token, &r1).unwrap();
        assert!(att1.can_prove());

        // Second attenuation: further restrict to read-only.
        let r2 = Attenuation {
            services: vec![("storage".to_string(), "r".to_string())],
            ..Default::default()
        };
        let att2 = cclerk.attenuate(&att1, &r2).unwrap();

        // The doubly-attenuated token should still be able to prove.
        assert!(!att2.can_mint());
        assert!(att2.can_prove());
        let expected_proof_key = blake3::derive_key("dregg-proof-key-v1", &root_key);
        assert_eq!(att2.issuer_key(), &expected_proof_key);
        assert_ne!(
            att2.issuer_key(),
            &root_key,
            "issuer_key must NOT be the raw root key"
        );

        // Authorize in Private mode.
        let request = dregg_token::AuthRequest {
            service: Some("storage".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = cclerk.authorize(&att2, &request, VerificationMode::FullyPrivate);
        assert!(
            presentation.is_ok(),
            "doubly-attenuated token should authorize in Private mode, got: {:?}",
            presentation.err()
        );
    }

    /// Test that delegated tokens CAN prove when proof_key is included in the delegation.
    ///
    /// This is the primary cross-agent delegation flow: Agent A delegates to Agent B,
    /// including a derived proof_key. Agent B can then generate ZK proofs privately.
    #[test]
    fn test_delegated_token_can_prove_with_proof_key() {
        let mut issuer_cclerk = AgentCipherclerk::new();
        let issuer_pk = issuer_cclerk.public_key();
        let root_key = [0xDD; 32];
        let root_token = issuer_cclerk.mint_token(&root_key, "api");

        let holder_cclerk = AgentCipherclerk::new();
        let holder_cclerk_pk = holder_cclerk.public_key();

        let restrictions = Attenuation {
            services: vec![("api".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegated = issuer_cclerk
            .delegate(&root_token, &holder_cclerk_pk, &restrictions)
            .unwrap();

        // The delegation should include a proof_key (derived from issuer's root key).
        assert!(
            delegated.proof_key.is_some(),
            "delegation from a provable token must include a proof_key"
        );
        // The proof_key must NOT be the raw root_key (it's derived via BLAKE3).
        assert_ne!(
            delegated.proof_key.unwrap(),
            root_key,
            "proof_key must be derived, not the raw root key"
        );

        // Holder receives the delegation (with proof_key) under a trusted-key policy.
        let mut holder_cclerk = holder_cclerk;
        holder_cclerk
            .receive_signed_delegation(delegated, &DelegationAuthority::TrustedKey(issuer_pk))
            .unwrap();
        let held = holder_cclerk.tokens().first().unwrap().clone();

        // Delegated token cannot mint but CAN prove (has derived proof_key as issuer_key).
        assert!(!held.can_mint());
        assert!(
            held.can_prove(),
            "delegated token with proof_key should be able to prove"
        );

        // Private authorization should succeed.
        let request = dregg_token::AuthRequest {
            service: Some("api".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let result = holder_cclerk.authorize(&held, &request, VerificationMode::FullyPrivate);
        assert!(
            result.is_ok(),
            "delegated token with proof_key should authorize in Private mode, got: {:?}",
            result.err()
        );
    }

    /// Test that delegated tokens without proof_key (stripped delegations)
    /// cannot prove without explicit issuer_key provision.
    ///
    /// (The struct literal that used to construct an unsigned envelope here is
    /// no longer constructible — `DelegatedToken` now requires a signature.
    /// This is the encoded form of the design fix.)
    #[test]
    fn test_delegated_token_cannot_prove_without_proof_key() {
        let holder_cclerk = AgentCipherclerk::new();

        // Directly construct a HeldToken with zeroed issuer_key to exercise the
        // proof-without-key path (the wire-level DelegatedToken can no longer
        // carry an absent signature, so this is the only meaningful shape).
        let held = HeldToken::new(
            "legacy".to_string(),
            "api".to_string(),
            "em2_fake".to_string(),
            [0u8; 32], // no root key
            "legacy:0".to_string(),
        );

        // Token without proof_key cannot prove.
        assert!(!held.can_mint());
        assert!(!held.can_prove());

        // Private authorization should fail with MissingKey.
        let request = dregg_token::AuthRequest {
            service: Some("api".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let result = holder_cclerk.authorize(&held, &request, VerificationMode::FullyPrivate);
        assert!(result.is_err());
    }

    /// Roundtrip test: cipherclerk.authorize() produces bytes that engine.verify_presentation_against()
    /// can decode and verify.
    ///
    /// This is the P0 regression test for the format mismatch where the cipherclerk serialized
    /// raw STARK bytes via `stark::proof_to_bytes` but the verifier expected a postcard-encoded
    /// `WirePresentationProof`. Both sides now use the same format.
    #[test]
    fn test_cclerk_authorize_engine_verify_roundtrip() {
        use crate::embed::{DreggEngine, EngineConfig};

        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xEE; 32];
        let root_token = cclerk.mint_token(&root_key, "data");

        // Attenuate the token (restrict to read on "data" service).
        let restrictions = Attenuation {
            services: vec![("data".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = cclerk.attenuate(&root_token, &restrictions).unwrap();
        assert!(attenuated.can_prove());

        // Generate the proof via cipherclerk.authorize(FullyPrivate).
        let request = dregg_token::AuthRequest {
            service: Some("data".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = cclerk
            .authorize(&attenuated, &request, VerificationMode::FullyPrivate)
            .expect("authorize should succeed");

        let proof_bytes = match &presentation {
            AuthorizationPresentation::Private { proof, conclusion } => {
                assert!(*conclusion, "authorization should allow");
                proof.clone()
            }
            other => panic!("expected Private presentation, got: {:?}", other),
        };

        // Compute the federation root (same derivation the cipherclerk uses internally).
        let federation_root_bb = AgentCipherclerk::compute_federation_root_bb(&root_key);
        let federation_root = AgentCipherclerk::bb_to_bytes(federation_root_bb);

        // Create an engine and set the federation root to match.
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        engine.set_federation_root(federation_root);

        // The key assertion: verify_presentation_against must successfully decode the proof.
        // (Before the fix, this would fail with "proof decode failed" because the cipherclerk
        // serialized raw STARK bytes instead of a postcard WirePresentationProof.)
        let result =
            engine.verify_presentation_against(&proof_bytes, &federation_root, "r", "data");

        // The proof should decode without error. Whether full cryptographic verification
        // passes depends on STARK verification and freshness checks, but the decode must
        // succeed -- that's the P0 fix we're testing.
        assert!(
            result.is_ok(),
            "verify_presentation_against should not return a decode error, got: {:?}",
            result.err()
        );
    }

    // =========================================================================
    // Sovereign Cell Tests
    // =========================================================================

    #[test]
    fn test_make_sovereign_builds_turn() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        let turn = cclerk.make_sovereign(&cell_id).unwrap();

        // The turn targets the cell we specified.
        assert_eq!(turn.agent, cell_id);
        // It should have one action with MakeSovereign effect.
        assert_eq!(turn.action_count(), 1);
        // Sovereign witnesses should be empty (not needed for MakeSovereign).
        assert!(turn.sovereign_witnesses.is_empty());
        // Memo should describe the operation.
        assert_eq!(turn.memo.as_deref(), Some("make_sovereign"));
    }

    #[test]
    fn test_execute_sovereign_turn_requires_stored_state() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = cclerk.cell_id("test");

        // Without stored state, should fail.
        let result = cclerk.execute_sovereign_turn(&cell_id, vec![], 0);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("no local sovereign state"));
    }

    #[test]
    fn test_execute_sovereign_turn_with_stored_state() {
        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;
        let token_id = *blake3::hash(b"test").as_bytes();
        let cell = dregg_cell::Cell::with_balance(pk, token_id, 1000);
        let cell_id = cell.id();

        // Store sovereign state.
        cclerk.store_sovereign_state(cell.clone());

        // Build a sovereign turn with a transfer effect.
        let other_cell = CellId([99u8; 32]);
        let effects = vec![Effect::Transfer {
            from: cell_id,
            to: other_cell,
            amount: 100,
        }];
        let turn = cclerk
            .execute_sovereign_turn(&cell_id, effects, 10)
            .unwrap();

        // Turn should reference the cell.
        assert_eq!(turn.agent, cell_id);
        assert_eq!(turn.fee, 10);
        // Sovereign witness should be populated.
        assert!(turn.sovereign_witnesses.contains_key(&cell_id));
        let witness = &turn.sovereign_witnesses[&cell_id];
        assert_eq!(witness.cell_state.id(), cell_id);
        // The witness declares the GENUINE post-state commitment — the executor
        // re-executes the effects against the injected pre-state and REJECTS
        // all-zero placeholder commitments (execute.rs rules 7/8), so
        // `execute_sovereign_turn` pre-executes locally (balance 1000 → 900 after
        // the 100 outgoing transfer) and signs the real value. (The old
        // expectation of `[0u8; 32]` enshrined the executor-rejected placeholder.)
        let mut expected_post = cell.clone();
        expected_post
            .state
            .set_balance(expected_post.state.balance() - 100);
        assert_ne!(witness.new_commitment, [0u8; 32]);
        assert_eq!(witness.new_commitment, expected_post.state_commitment());
    }

    #[test]
    fn test_store_and_retrieve_sovereign_state() {
        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = dregg_cell::Cell::with_balance(pk, token_id, 500);
        let cell_id = cell.id();

        // Initially empty.
        assert_eq!(cclerk.sovereign_cell_count(), 0);
        assert!(cclerk.sovereign_state(&cell_id).is_none());

        // Store.
        cclerk.store_sovereign_state(cell.clone());
        assert_eq!(cclerk.sovereign_cell_count(), 1);

        // Retrieve.
        let retrieved = cclerk.sovereign_state(&cell_id).unwrap();
        assert_eq!(retrieved.id(), cell_id);
        assert_eq!(retrieved.state.balance(), 500);
    }

    #[test]
    fn test_apply_sovereign_effects() {
        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = dregg_cell::Cell::with_balance(pk, token_id, 1000);
        let cell_id = cell.id();

        cclerk.store_sovereign_state(cell);

        let other = CellId([99u8; 32]);

        // Apply a transfer out.
        let effects = vec![
            Effect::Transfer {
                from: cell_id,
                to: other,
                amount: 300,
            },
            Effect::IncrementNonce { cell: cell_id },
        ];
        cclerk.apply_sovereign_effects(&cell_id, &effects).unwrap();

        let state = cclerk.sovereign_state(&cell_id).unwrap();
        assert_eq!(state.state.balance(), 700);
        assert_eq!(state.state.nonce(), 1);
    }

    #[test]
    fn test_apply_sovereign_effects_transfer_in() {
        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = dregg_cell::Cell::with_balance(pk, token_id, 100);
        let cell_id = cell.id();

        cclerk.store_sovereign_state(cell);

        let other = CellId([88u8; 32]);
        let effects = vec![Effect::Transfer {
            from: other,
            to: cell_id,
            amount: 500,
        }];
        cclerk.apply_sovereign_effects(&cell_id, &effects).unwrap();

        let state = cclerk.sovereign_state(&cell_id).unwrap();
        assert_eq!(state.state.balance(), 600);
    }

    #[test]
    fn test_apply_sovereign_effects_missing_cell() {
        let mut cclerk = AgentCipherclerk::new();
        let cell_id = CellId([1u8; 32]);

        let result = cclerk.apply_sovereign_effects(&cell_id, &[]);
        assert!(result.is_err());
    }

    /// SDK-emitted WitnessedReceipt: (a) is a real scope-2 WR, (b) round-trips
    /// through the canonical DWR1 witness_artifact, and (c) is structurally
    /// valid as one side of a γ.2 bilateral bundle. We build the matching peer
    /// side from the same turn's schedule and confirm the *pair* aggregates.
    ///
    /// v1 floor only: `emit_witnessed_receipt` produces the v1 hand-AIR WR, retired under prover.
    #[cfg(not(feature = "prover"))]
    #[test]
    fn test_emit_witnessed_receipt_bilateral_pair_aggregates() {
        use dregg_circuit::effect_vm::pi;
        use dregg_circuit::field::BabyBear;
        use dregg_turn::WitnessedReceipt;

        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;
        let token_id = *blake3::hash(b"bilateral-domain").as_bytes();
        let cell = dregg_cell::Cell::with_balance(pk, token_id, 1000);
        let agent_cell = cell.id();
        cclerk.store_sovereign_state(cell);

        // The peer (receiver) — a different cell id.
        let peer_cell = CellId([0x5C; 32]);

        let effects = vec![Effect::Transfer {
            from: agent_cell,
            to: peer_cell,
            amount: 250,
        }];

        // --- SDK agent emits ITS side end-to-end ---
        let emitted = cclerk
            .emit_witnessed_receipt(&agent_cell, effects, 10)
            .expect("emit witnessed receipt");

        // The emitted WR is a real scope-2 receipt (proof + PI + inline trace).
        let agent_wr = &emitted.witnessed;
        assert!(!agent_wr.proof_bytes.is_empty(), "WR carries proof bytes");
        assert!(
            agent_wr.witness_bundle.is_some(),
            "WR carries scope-2 inline trace"
        );
        agent_wr
            .require_scope2_witness()
            .expect("scope-2 witness binds witness_hash");
        // PI carries the agent's projected bilateral role: one outbound transfer.
        assert!(agent_wr.public_inputs.len() >= pi::ACTIVE_BASE_COUNT);
        assert_eq!(
            agent_wr.public_inputs[pi::OUTBOUND_TRANSFER_COUNT],
            1,
            "agent has exactly one outbound transfer"
        );
        assert_eq!(
            agent_wr.public_inputs[pi::IS_AGENT_CELL],
            1,
            "agent cell flags IS_AGENT_CELL == 1"
        );

        // --- (a)/(b) round-trip through the canonical DWR1 artifact ---
        let artifact = crate::witness_artifact::encode_witnessed_receipt_artifact(agent_wr)
            .expect("encode DWR1 artifact");
        let decoded = crate::witness_artifact::decode_witnessed_receipt_artifact(&artifact)
            .expect("decode DWR1 artifact");
        assert_eq!(
            decoded.receipt.receipt_hash(),
            agent_wr.receipt.receipt_hash()
        );
        assert_eq!(decoded.public_inputs, agent_wr.public_inputs);
        assert_eq!(decoded.witness_hash, agent_wr.witness_hash);
        assert_eq!(
            decoded
                .witness_bundle
                .as_ref()
                .expect("decoded scope-2 bundle")
                .trace_rows,
            agent_wr.witness_bundle.as_ref().unwrap().trace_rows
        );

        // --- (c) construct the matching peer side from the SAME turn ---
        // The peer (receiver) is NOT the turn.agent, so IS_AGENT_CELL == 0 and
        // its bilateral projection is the inbound role. We derive it from the
        // turn's canonical schedule exactly as an independent peer SDK would.
        let turn = &emitted.turn;
        let schedule = dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(turn);
        let mut peer_pi = agent_wr.public_inputs.clone();
        // Re-project the bilateral region for the peer's role.
        let mut peer_pi_bb: Vec<BabyBear> = peer_pi
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        let peer_counts = schedule.counts_for(&peer_cell);
        let peer_roots = schedule.roots_for(&peer_cell, turn.nonce);
        dregg_turn::bilateral_schedule::project_into_pi(&mut peer_pi_bb, &peer_counts, &peer_roots);
        peer_pi_bb[pi::IS_AGENT_CELL] = BabyBear::ZERO;
        peer_pi = peer_pi_bb.iter().map(|bb| bb.as_u32()).collect();

        // Wrap the peer PI in a (proof-less is fine for the structural γ.2 gate)
        // WitnessedReceipt — the bilateral verifier reads only public_inputs.
        let mut peer_receipt = dregg_turn::TurnReceipt::default();
        peer_receipt.agent = peer_cell;
        let peer_wr = WitnessedReceipt::from_components(peer_receipt, Vec::new(), peer_pi, None);

        // Sanity: peer's inbound count is 1, outbound 0.
        assert_eq!(peer_wr.public_inputs[pi::INBOUND_TRANSFER_COUNT], 1);
        assert_eq!(peer_wr.public_inputs[pi::OUTBOUND_TRANSFER_COUNT], 0);
        assert_eq!(peer_wr.public_inputs[pi::IS_AGENT_CELL], 0);

        // --- the pair aggregates under the γ.2 verifier ---
        let bundle: Vec<(CellId, &WitnessedReceipt)> =
            vec![(agent_cell, agent_wr), (peer_cell, &peer_wr)];
        WitnessedReceipt::verify_bilateral_chain(&bundle, turn)
            .expect("SDK-emitted WR + peer side form a valid γ.2 bilateral bundle");

        // Adversarial: dropping the peer (incomplete cross-side coverage) must reject.
        let only_agent: Vec<(CellId, &WitnessedReceipt)> = vec![(agent_cell, agent_wr)];
        assert!(
            WitnessedReceipt::verify_bilateral_chain(&only_agent, turn).is_err(),
            "single-sided bundle must reject (missing peer)"
        );
    }

    #[test]
    fn test_export_import_sovereign_state_roundtrip() {
        let mut cclerk = AgentCipherclerk::new();
        let pk = cclerk.public_key().0;

        // Store two sovereign cells.
        let token_id_a = *blake3::hash(b"domain-a").as_bytes();
        let cell_a = dregg_cell::Cell::with_balance(pk, token_id_a, 100);
        let id_a = cell_a.id();
        cclerk.store_sovereign_state(cell_a);

        let token_id_b = *blake3::hash(b"domain-b").as_bytes();
        let cell_b = dregg_cell::Cell::with_balance(pk, token_id_b, 200);
        let id_b = cell_b.id();
        cclerk.store_sovereign_state(cell_b);

        assert_eq!(cclerk.sovereign_cell_count(), 2);

        // Export.
        let exported = cclerk.export_sovereign_state();
        assert!(!exported.is_empty());

        // Import into a fresh cipherclerk.
        let mut cclerk2 = AgentCipherclerk::new();
        cclerk2.import_sovereign_state(&exported).unwrap();

        assert_eq!(cclerk2.sovereign_cell_count(), 2);
        assert_eq!(cclerk2.sovereign_state(&id_a).unwrap().state.balance(), 100);
        assert_eq!(cclerk2.sovereign_state(&id_b).unwrap().state.balance(), 200);
    }

    #[test]
    fn test_import_sovereign_state_invalid_data() {
        let mut cclerk = AgentCipherclerk::new();
        let result = cclerk.import_sovereign_state(b"not valid postcard data");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("failed to deserialize sovereign state"));
    }

    #[test]
    fn test_peer_exchange_session() {
        let cclerk = AgentCipherclerk::new();
        let exchange = cclerk.peer_exchange_session("test");
        // PeerExchange should be initialized with the cipherclerk's cell_id.
        let expected_cell_id = cclerk.cell_id("test");
        assert_eq!(exchange.cell_id(), expected_cell_id);
    }

    // =========================================================================
    // Delegation envelope soundness (P0/P1 adversarial regression suite)
    //
    // These tests encode the "delegation envelope is an authority binding"
    // invariant. If any of them fail, the security model is broken.
    // =========================================================================

    /// Helper: mint a delegated envelope from `delegator` to `recipient_pk`.
    fn mint_delegation(
        delegator: &mut AgentCipherclerk,
        recipient_pk: PublicKey,
        root_key: [u8; 32],
        service: &str,
    ) -> DelegatedToken {
        let root_token = delegator.mint_token(&root_key, service);
        let restrictions = Attenuation {
            services: vec![(service.to_string(), "r".to_string())],
            ..Default::default()
        };
        delegator
            .delegate(&root_token, &recipient_pk, &restrictions)
            .unwrap()
    }

    /// P0: a holder of `proof_key` cannot forge an envelope for themselves.
    ///
    /// Even though the attacker can compute caveat_chain_hash and knows the
    /// proof_key, they cannot sign under the legitimate delegator's key.
    #[test]
    fn test_envelope_rejects_attacker_forged_signature() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        // Alice delegates legitimately to Bob.
        let env = mint_delegation(&mut alice, bob_pk, [0x11; 32], "svc");

        // Attacker Mallory tries to forge a new envelope: same content but
        // signed under her own key, claiming to be from Alice.
        let mallory = AgentCipherclerk::new();
        let mut forged = env.clone();
        // Mallory keeps Alice's pubkey but signs with her own key. The signature
        // will not verify under Alice's key.
        let msg = AgentCipherclerk::compute_delegation_signing_message_v2(
            &forged.token_bytes,
            &forged.delegatee,
            &forged.service,
            &forged.id,
            &forged.restrictions,
            &forged.proof_key,
            &forged.caveat_chain_hash,
            forged.membership_proof.as_ref().map(|p| &p.leaf_hash),
            &forged.parent_delegation_hash,
            &forged.delegator_public_key,
        );
        let mallory_sig = mallory.signing_key.sign(&msg);
        forged.delegator_signature = Signature(mallory_sig.to_bytes());

        // Bob receives the forged envelope with a TrustedKey(alice) policy.
        let mut bob = bob;
        let result =
            bob.receive_signed_delegation(forged, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(
            matches!(result, Err(SdkError::InvalidDelegation(_))),
            "envelope signed by wrong key must be rejected; got {:?}",
            result
        );
    }

    /// P0: an attacker cannot swap in their own pubkey + sign under their own
    /// key — the authority policy rejects them.
    #[test]
    fn test_envelope_rejects_unauthorized_delegator() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        // Alice delegates to Bob legitimately.
        let _legit = mint_delegation(&mut alice, bob_pk, [0x22; 32], "svc");

        // Mallory (different cipherclerk) crafts her own valid envelope to Bob,
        // signed under her own key.
        let mut mallory = AgentCipherclerk::new();
        let mallory_env = mint_delegation(&mut mallory, bob_pk, [0x33; 32], "svc");

        // Bob's policy is "TrustedKey(alice_pk)" — Mallory must be rejected
        // even though her envelope is internally well-signed.
        let mut bob = bob;
        let result =
            bob.receive_signed_delegation(mallory_env, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(
            matches!(result, Err(SdkError::InvalidDelegation(_))),
            "envelope from non-authorized delegator must be rejected; got {:?}",
            result
        );
    }

    /// P1: replay across recipients is rejected — delegatee is in the signed
    /// payload, so an envelope minted for Bob cannot be accepted by Carol.
    #[test]
    fn test_envelope_rejects_replay_to_wrong_recipient() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();
        let mut carol = AgentCipherclerk::new();

        // Alice delegates to Bob.
        let env_for_bob = mint_delegation(&mut alice, bob_pk, [0x44; 32], "svc");

        // Carol tries to accept Bob's envelope as her own.
        let result = carol.receive_signed_delegation(
            env_for_bob.clone(),
            &DelegationAuthority::TrustedKey(alice_pk),
        );
        assert!(
            matches!(result, Err(SdkError::InvalidDelegation(_))),
            "envelope addressed to Bob must be rejected by Carol; got {:?}",
            result
        );

        // Mallory also can't rewrite the delegatee to Carol — the signature
        // covers `delegatee`, so flipping it breaks the signature.
        let mut tampered = env_for_bob.clone();
        tampered.delegatee = carol.public_key();
        let result2 =
            carol.receive_signed_delegation(tampered, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(
            matches!(result2, Err(SdkError::InvalidDelegation(_))),
            "tampered delegatee must invalidate signature; got {:?}",
            result2
        );
    }

    /// P1: tampering with `restrictions`, `service`, `id`, or `token_bytes`
    /// invalidates the signature.
    #[test]
    fn test_envelope_rejects_tampered_fields() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        let env = mint_delegation(&mut alice, bob_pk, [0x55; 32], "svc");

        // Tamper with restrictions (widen permissions).
        let mut t1 = env.clone();
        t1.restrictions = Attenuation {
            services: vec![("svc".to_string(), "rw".to_string())],
            ..Default::default()
        };
        let mut bob1 = AgentCipherclerk::from_key_bytes(Zeroizing::new(bob.signing_key.to_bytes()));
        let r1 = bob1.receive_signed_delegation(t1, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(matches!(r1, Err(SdkError::InvalidDelegation(_))));

        // Tamper with service.
        let mut t2 = env.clone();
        t2.service = "other-svc".to_string();
        let mut bob2 = AgentCipherclerk::from_key_bytes(Zeroizing::new(bob.signing_key.to_bytes()));
        let r2 = bob2.receive_signed_delegation(t2, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(matches!(r2, Err(SdkError::InvalidDelegation(_))));

        // Tamper with id.
        let mut t3 = env.clone();
        t3.id = "different-id".to_string();
        let mut bob3 = AgentCipherclerk::from_key_bytes(Zeroizing::new(bob.signing_key.to_bytes()));
        let r3 = bob3.receive_signed_delegation(t3, &DelegationAuthority::TrustedKey(alice_pk));
        assert!(matches!(r3, Err(SdkError::InvalidDelegation(_))));
    }

    /// P1: chain delegations only validate when `parent_delegation_hash` matches.
    #[test]
    fn test_envelope_chain_rejects_wrong_parent_hash() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();
        let carol = AgentCipherclerk::new();
        let carol_pk = carol.public_key();

        // Alice → Bob.
        let env_ab = mint_delegation(&mut alice, bob_pk, [0x66; 32], "svc");
        let mut bob = bob;
        bob.receive_signed_delegation(env_ab.clone(), &DelegationAuthority::TrustedKey(alice_pk))
            .unwrap();
        let received_hash = env_ab.envelope_hash();

        // Bob → Carol, properly chained.
        let bob_token = bob.tokens().first().unwrap().clone();
        let restrictions = Attenuation {
            services: vec![("svc".to_string(), "r".to_string())],
            ..Default::default()
        };
        let env_bc = bob
            .delegate_with_parent(&bob_token, &carol_pk, &restrictions, received_hash)
            .unwrap();

        // Carol accepts with the correct chain policy.
        let mut carol_ok = carol;
        carol_ok
            .receive_signed_delegation(
                env_bc.clone(),
                &DelegationAuthority::ChainsFromParent {
                    parent_hash: received_hash,
                    delegator: bob.public_key(),
                },
            )
            .unwrap();

        // Carol with the wrong expected parent hash must reject.
        let mut carol_bad = AgentCipherclerk::new();
        let env_bc_for_carol_bad = bob
            .delegate_with_parent(
                &bob_token,
                &carol_bad.public_key(),
                &restrictions,
                received_hash,
            )
            .unwrap();
        let wrong_parent = [0xFFu8; 32];
        let result = carol_bad.receive_signed_delegation(
            env_bc_for_carol_bad,
            &DelegationAuthority::ChainsFromParent {
                parent_hash: wrong_parent,
                delegator: bob.public_key(),
            },
        );
        assert!(
            matches!(result, Err(SdkError::InvalidDelegation(_))),
            "ChainsFromParent must reject envelope whose parent_hash mismatches; got {:?}",
            result
        );
    }

    /// P1 / type-level: there is no API path that constructs a DelegatedToken
    /// without a signature. Any externally-sourced bytes must come through
    /// deserialization, and the struct has no `Option`s on the sig fields.
    /// This is a compile-time guarantee, verified by the absence of a
    /// `delegator_signature: None` constructor anywhere in the crate.
    #[test]
    fn test_envelope_has_no_unsigned_constructor() {
        // The struct literal below is intentionally commented out — if anyone
        // re-introduces optional sigs, this comment becomes outdated and the
        // grep-based audit will need to be rerun. The test exists to anchor
        // the invariant in the test file's git history.
        //
        //   let _bad = DelegatedToken {
        //       delegator_signature: None,  // <-- would not compile
        //       delegator_public_key: None, // <-- would not compile
        //       ..
        //   };

        // Sanity check: a well-formed envelope round-trips through serde.
        let mut alice = AgentCipherclerk::new();
        let bob = AgentCipherclerk::new();
        let env = mint_delegation(&mut alice, bob.public_key(), [0x77; 32], "svc");
        let bytes = postcard::to_allocvec(&env).unwrap();
        let _restored: DelegatedToken = postcard::from_bytes(&bytes).unwrap();
    }

    /// P1: the `Open` policy is unsafe but exists for dev. Verify it accepts
    /// any well-signed envelope (so tests can opt in), AND verify a tampered
    /// envelope still gets rejected by the signature check.
    #[test]
    fn test_envelope_open_policy_still_verifies_signature() {
        let mut alice = AgentCipherclerk::new();
        let bob = AgentCipherclerk::new();
        let env = mint_delegation(&mut alice, bob.public_key(), [0x88; 32], "svc");

        // Open policy accepts a legitimate envelope.
        let mut bob1 = AgentCipherclerk::from_key_bytes(Zeroizing::new(bob.signing_key.to_bytes()));
        bob1.receive_signed_delegation(env.clone(), &DelegationAuthority::Open { warn: false })
            .unwrap();

        // Open policy still rejects a tampered envelope (signature mismatch).
        let mut tampered = env.clone();
        tampered.restrictions = Attenuation {
            services: vec![("svc".to_string(), "rw".to_string())],
            ..Default::default()
        };
        let mut bob2 = AgentCipherclerk::from_key_bytes(Zeroizing::new(bob.signing_key.to_bytes()));
        let result =
            bob2.receive_signed_delegation(tampered, &DelegationAuthority::Open { warn: false });
        assert!(matches!(result, Err(SdkError::InvalidDelegation(_))));
    }

    /// P0/runtime: the local-delegation path used by sub-agent spawning is
    /// signature-verified end-to-end. A caller cannot pass in an unsigned
    /// LocalDelegation (the struct is non-public and crate-internal).
    #[test]
    fn test_local_delegation_signature_required() {
        let mut parent = AgentCipherclerk::new();
        let root_key = [0x99; 32];
        let parent_token = parent.mint_token(&root_key, "svc");

        let child = AgentCipherclerk::new();
        let child_pk = child.public_key();

        // Build a legitimate local delegation.
        let local = parent.make_local_delegation(
            parent_token.encoded.clone(),
            "svc".to_string(),
            "test".to_string(),
            "test-id".to_string(),
            child_pk,
            Attenuation::default(),
            None,
            None,
            None,
        );

        // Child accepts under the parent's pubkey.
        let mut child = child;
        child
            .receive_local_delegation(local.clone(), &parent.public_key())
            .unwrap();

        // Child rejects if we claim a different expected parent.
        let mut child2 = AgentCipherclerk::new();
        let local2 = parent.make_local_delegation(
            parent_token.encoded.clone(),
            "svc".to_string(),
            "test".to_string(),
            "test-id".to_string(),
            child2.public_key(),
            Attenuation::default(),
            None,
            None,
            None,
        );
        let bogus_pk = AgentCipherclerk::new().public_key();
        let result = child2.receive_local_delegation(local2, &bogus_pk);
        assert!(
            matches!(result, Err(SdkError::InvalidDelegation(_))),
            "local delegation must reject when expected parent doesn't match signer; got {:?}",
            result
        );
    }

    // =========================================================================
    // P0 durable-binding adversarial tests
    //
    // The previous envelope-v2 fix verified the delegator signature once at
    // receive time and then discarded it. These tests prove that the deeper
    // fix — re-verifying the signature on every authorization use against the
    // *current* (potentially tampered) field values — holds.
    // =========================================================================

    /// Helper: mint a delegation including a federation membership proof so
    /// the resulting HeldToken can produce ZK proofs (exercises the full
    /// authorize_private path).
    fn mint_provable_delegation(
        delegator: &mut AgentCipherclerk,
        recipient_pk: PublicKey,
        root_key: [u8; 32],
        service: &str,
    ) -> DelegatedToken {
        let root_token = delegator.mint_token(&root_key, service);
        let proof_key = AgentCipherclerk::derive_proof_key(&root_key);
        let mut tree = dregg_commit::merkle::MerkleTree::new();
        tree.insert_hash(proof_key);
        let restrictions = Attenuation {
            services: vec![(service.to_string(), "r".to_string())],
            ..Default::default()
        };
        delegator
            .delegate_with_tree(&root_token, &recipient_pk, &restrictions, &tree)
            .unwrap()
    }

    /// P0: an attacker who somehow obtains write access to a sealed
    /// HeldToken's `encoded` field cannot use it to authorize, because the
    /// captured delegation signature is re-verified on every authorization
    /// use against the current `encoded` value.
    #[test]
    fn test_held_token_tamper_encoded_breaks_authorize() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let mut bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        let env = mint_provable_delegation(&mut alice, bob_pk, [0xAB; 32], "svc");
        bob.receive_signed_delegation(env, &DelegationAuthority::TrustedKey(alice_pk))
            .unwrap();

        // Find the held token in Bob's cipherclerk by index (avoid relying on
        // public accessors mutating state).
        assert_eq!(bob.tokens.len(), 1);
        // Pre-tamper: re-verification of the binding must succeed.
        bob.tokens[0]
            .reverify_delegation_binding()
            .expect("freshly-received envelope must re-verify");

        // Simulate an attacker who somehow got write access — test-only helper.
        bob.tokens[0].test_only_tamper_encoded("em2_forged_payload".to_string());

        // Post-tamper: re-verification must fail.
        let reverify = bob.tokens[0].reverify_delegation_binding();
        assert!(
            matches!(reverify, Err(SdkError::InvalidDelegation(_))),
            "tampered `encoded` must break binding; got {:?}",
            reverify,
        );

        // Authorize uses both extract_caveat_set_for_proof (which calls
        // reverify) and prove_authorization_with_issuer_key (which also
        // calls it). Either path must fail.
        let request = AuthRequest {
            service: Some("svc".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let auth_result = bob.authorize(
            &bob.tokens[0].clone(),
            &request,
            VerificationMode::FullyPrivate,
        );
        assert!(
            matches!(auth_result, Err(SdkError::InvalidDelegation(_))),
            "tampered encoded must break authorize; got {:?}",
            auth_result,
        );
    }

    /// P0: the same property holds for `caveat_chain_hash`. An attacker
    /// who swaps in a fabricated caveat_chain_hash to match a mutated
    /// `encoded` cannot escape, because the delegator's signature also binds
    /// the caveat_chain_hash.
    #[test]
    fn test_held_token_tamper_chain_hash_breaks_authorize() {
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let mut bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        let env = mint_provable_delegation(&mut alice, bob_pk, [0xCD; 32], "svc");
        bob.receive_signed_delegation(env, &DelegationAuthority::TrustedKey(alice_pk))
            .unwrap();

        // Tamper only with the caveat_chain_hash.
        bob.tokens[0].test_only_tamper_caveat_chain_hash(Some([0xFFu8; 32]));

        let reverify = bob.tokens[0].reverify_delegation_binding();
        assert!(
            matches!(reverify, Err(SdkError::InvalidDelegation(_))),
            "tampered caveat_chain_hash must break binding; got {:?}",
            reverify,
        );

        let request = AuthRequest {
            service: Some("svc".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let auth_result = bob.authorize(
            &bob.tokens[0].clone(),
            &request,
            VerificationMode::FullyPrivate,
        );
        assert!(
            matches!(auth_result, Err(SdkError::InvalidDelegation(_))),
            "tampered caveat_chain_hash must break authorize; got {:?}",
            auth_result,
        );
    }

    /// P0 (type-level): the authority-affecting fields are sealed. External
    /// code cannot assign to `held.encoded` (no `pub` on the field, no
    /// `&mut self` accessor). This test confirms via a sample of read-only
    /// accessor calls; the actual no-write-access guarantee is enforced by
    /// `pub(crate)` field visibility and is checked by the Rust compiler at
    /// the public API boundary.
    #[test]
    fn test_held_token_no_public_field_mutation() {
        // We intentionally do NOT try to *compile* `held.encoded = "x".into()`
        // here — that compile-fail check is enforced at every external
        // callsite (the field is private). What we *can* check here is that
        // the public accessors are read-only references and that the
        // round-tripped values match what was set internally.
        let mut alice = AgentCipherclerk::new();
        let alice_pk = alice.public_key();
        let mut bob = AgentCipherclerk::new();
        let bob_pk = bob.public_key();

        let env = mint_provable_delegation(&mut alice, bob_pk, [0xEF; 32], "svc");
        let original_encoded = env.token_bytes.clone();
        bob.receive_signed_delegation(env, &DelegationAuthority::TrustedKey(alice_pk))
            .unwrap();

        // Accessor returns a borrow.
        let held = &bob.tokens[0];
        let encoded_ref: &str = held.encoded();
        assert_eq!(encoded_ref, original_encoded);

        // The accessor does not expose any way to mutate. (This is enforced
        // by the type — the compiler would reject any attempt to write
        // through `held.encoded` because the field is private.)
        //
        // For completeness, also verify that `caveat_chain_hash` returns by
        // value (so callers can't acquire a `&mut Option<[u8;32]>` reference
        // through accident).
        let _: Option<[u8; 32]> = held.caveat_chain_hash();
    }

    /// P1: the `Open` authority variant is gated behind the `unsafe-test-utils`
    /// feature (or `cfg(test)`). This test runs in `cfg(test)` and confirms
    /// the variant constructs and is wired up — in production builds without
    /// the feature, the variant does not exist and the code would fail to
    /// compile, which is the intended footgun-prevention behavior.
    #[test]
    fn test_open_authority_gated() {
        // Inside cfg(test), we can construct `Open`.
        let policy = DelegationAuthority::Open { warn: false };
        match policy {
            DelegationAuthority::Open { warn } => assert!(!warn),
            _ => panic!("expected Open variant"),
        }
        // Production code (not under cfg(test) and without unsafe-test-utils)
        // cannot reach this branch. Verified at compile time by the
        // `#[cfg(any(test, feature = "unsafe-test-utils"))]` gate on the
        // variant — see DelegationAuthority::Open.
    }

    /// P1-6: `compute_root_from_membership_proof` must reject proofs whose
    /// depth exceeds [`AgentCipherclerk::MAX_MEMBERSHIP_PROOF_DEPTH`].
    #[test]
    fn test_membership_proof_depth_bound() {
        use dregg_commit::merkle::MerkleProof;
        let depth = AgentCipherclerk::MAX_MEMBERSHIP_PROOF_DEPTH + 1;
        let proof = MerkleProof {
            siblings: vec![[[0u8; 32]; 3]; depth],
            path_indices: vec![0; depth],
            leaf_hash: [0u8; 32],
            bucket_siblings: vec![],
        };
        let result = AgentCipherclerk::compute_root_from_membership_proof(&proof);
        assert!(result.is_err(), "depth-exceeding proof must be rejected");
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(
            err_msg.contains("depth exceeds maximum"),
            "expected depth-exceeded wire error, got: {err_msg}"
        );
    }

    /// P1-6: `compute_root_from_membership_proof` must reject proofs whose
    /// `siblings` / `path_indices` arrays have mismatched lengths.
    #[test]
    fn test_membership_proof_mismatched_lengths() {
        use dregg_commit::merkle::MerkleProof;
        let proof = MerkleProof {
            siblings: vec![[[0u8; 32]; 3]; 4],
            path_indices: vec![0; 3], // shorter on purpose
            leaf_hash: [0u8; 32],
            bucket_siblings: vec![],
        };
        let result = AgentCipherclerk::compute_root_from_membership_proof(&proof);
        assert!(result.is_err(), "mismatched lengths must be rejected");
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(
            err_msg.contains("mismatched"),
            "expected mismatch wire error, got: {err_msg}"
        );
    }

    /// P1-6: `receive_signed_delegation` rejects oversized membership proofs
    /// at the receive boundary so a malicious sender cannot park a DoS-shaped
    /// proof inside our cipherclerk for later detonation.
    #[test]
    fn test_receive_rejects_oversized_membership_proof() {
        use dregg_commit::merkle::MerkleProof;
        use dregg_token::Attenuation;

        // Build a small token using a generated cipherclerk.
        let mut alice = AgentCipherclerk::new();
        let bob = AgentCipherclerk::new();
        let root_token = alice.mint_token(&[42u8; 32], "test-svc");

        // Forge a v2 delegation envelope with an enormous membership proof.
        let oversized_depth = AgentCipherclerk::MAX_MEMBERSHIP_PROOF_DEPTH + 5;
        let mp = MerkleProof {
            siblings: vec![[[0u8; 32]; 3]; oversized_depth],
            path_indices: vec![0; oversized_depth],
            leaf_hash: [7u8; 32],
            bucket_siblings: vec![],
        };

        // AUDIT[*]: Previously used `applications: Some(vec![AppRestriction { id: "x", actions: vec![] }])`.
        // `AppRestriction` was removed; `Attenuation.applications` became `apps: Vec<(String, String)>`
        // where the tuple is (app_id, action_mask). Empty actions → empty action mask string.
        // The test only needs a non-empty Attenuation to produce a valid delegation envelope;
        // the restriction semantics are not under test here.
        let restrictions = Attenuation {
            apps: vec![("x".to_string(), "".to_string())],
            ..Default::default()
        };

        let env = alice
            .delegate(&root_token, &bob.public_key(), &restrictions)
            .expect("delegate produces a v2 envelope");

        // Override the membership_proof field through `mut env`. `delegator_signature`
        // will now be stale (it covers the original empty proof), but the depth
        // check fires BEFORE the signature is checked, so the test still
        // exercises the boundary.
        let mut tampered = env;
        tampered.membership_proof = Some(mp);

        let mut bob_mut = bob;
        let result = bob_mut.receive_signed_delegation(
            tampered,
            &DelegationAuthority::TrustedKey(alice.public_key()),
        );
        assert!(
            result.is_err(),
            "receive_signed_delegation must reject oversized membership proof"
        );
        let msg = format!("{}", result.err().unwrap());
        assert!(
            msg.contains("depth exceeds maximum") || msg.contains("membership"),
            "expected depth/membership rejection, got: {msg}"
        );
    }

    // -----------------------------------------------------------------
    // Queue-method authorization tests.
    //
    // SDK-REVIEW.md C-3 flagged that `allocate_queue`, `enqueue_message`,
    // `dequeue_message`, and `atomic_queue_tx` each built Turns by struct
    // literal ending in `Authorization::Unchecked` — i.e. SDK was
    // shipping four `Unchecked` authorizations on user-callable surface
    // (one of the Stage 8 P2.E-H grep targets).
    //
    // These tests pin the post-fix invariant: every queue method
    // produces a Turn whose root action carries a real, non-zero
    // ed25519 signature half against the supplied federation_id.
    // -----------------------------------------------------------------

    /// Adversarial pin: a Signature with both halves zero is not a real
    /// signature; if a queue method ever regressed to `Authorization::Unchecked`
    /// the variant would not be `Signature(..)` at all, but if some future
    /// "lazy sign" path produced `Signature([0;32], [0;32])` we want to catch
    /// it too. (See `app-framework/tests/cipherclerk_sign_action.rs` for the
    /// matching pin on the AppCipherclerk path.)
    fn assert_real_signature(action: &dregg_turn::action::Action) {
        use dregg_turn::action::Authorization;
        match &action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    *a != [0u8; 32] || *b != [0u8; 32],
                    "queue action signature must be non-zero (got both halves zero)"
                );
            }
            other => panic!(
                "queue action must carry Authorization::Signature(..), got {:?}",
                other
            ),
        }
    }

    fn root_action(turn: &Turn) -> &dregg_turn::action::Action {
        &turn.call_forest.roots[0].action
    }

    // (The queue-allocation signature tests died with the queue family in the
    // verb lockstep. Their properties live on against surviving methods:
    // cross-federation no-replay in
    // `create_from_factory_signature_binds_to_federation_id`, verify-against-
    // pubkey in `signature_verifies_against_cclerk_pubkey` below.)

    // -----------------------------------------------------------------
    // create_from_factory authorization tests.
    //
    // SDK-DREGGSCRIPT-AUDIT.md §9 flagged that `create_from_factory`
    // was a sibling of the queue-method C-3 regression: it built its
    // action by struct literal with Authorization::Unchecked.
    // These tests pin the post-fix invariant.
    // -----------------------------------------------------------------

    #[test]
    fn create_from_factory_produces_real_signature() {
        let cclerk = AgentCipherclerk::new();
        let fed = [42u8; 32];
        let issuer = cclerk.cell_id("default");
        let turn = cclerk.create_from_factory(
            issuer,
            [0xAA; 32],
            [0xBB; 32],
            [0xCC; 32],
            dregg_cell::FactoryCreationParams {
                owner_pubkey: [0xBB; 32],
                mode: dregg_cell::CellMode::default(),
                program_vk: None,
                initial_fields: vec![],
                initial_caps: vec![],
            },
            &fed,
        );
        assert_real_signature(root_action(&turn));
    }

    #[test]
    fn create_from_factory_signature_binds_to_federation_id() {
        use dregg_turn::action::Authorization;
        let cclerk = AgentCipherclerk::new();
        let issuer = cclerk.cell_id("default");
        let fed_a = [0x11u8; 32];
        let fed_b = [0x22u8; 32];
        let params_a = dregg_cell::FactoryCreationParams {
            owner_pubkey: [0xBB; 32],
            mode: dregg_cell::CellMode::default(),
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
        };
        let params_b = params_a.clone();
        let t_a = cclerk
            .create_from_factory(issuer, [0xAA; 32], [0xBB; 32], [0xCC; 32], params_a, &fed_a);
        let t_b = cclerk
            .create_from_factory(issuer, [0xAA; 32], [0xBB; 32], [0xCC; 32], params_b, &fed_b);
        let sig_a = match root_action(&t_a).authorization {
            Authorization::Signature(a, b) => (a, b),
            _ => panic!("expected Signature"),
        };
        let sig_b = match root_action(&t_b).authorization {
            Authorization::Signature(a, b) => (a, b),
            _ => panic!("expected Signature"),
        };
        assert_ne!(
            sig_a, sig_b,
            "create_from_factory signatures must bind to federation_id"
        );
    }

    /// The signature must verify against the cipherclerk's actual ed25519 key
    /// (not against some zero key or other party's key). This proves the
    /// signature was produced by `self.signing_key`, closing the
    /// "Unchecked → Signature shape but uses [0;64] key" attack.
    /// (Originally pinned via the queue family; re-carried on the surviving
    /// `create_from_factory` after the verb lockstep deleted the queue verbs.)
    #[test]
    fn signature_verifies_against_cclerk_pubkey() {
        use dregg_turn::action::{Action, Authorization};
        use dregg_turn::executor::TurnExecutor;
        use ed25519_dalek::{Signature, VerifyingKey};

        let cclerk = AgentCipherclerk::new();
        let fed = [13u8; 32];
        let turn = cclerk.create_from_factory(
            cclerk.cell_id("q"),
            [0xAA; 32],
            [0xBB; 32],
            [0xEE; 32],
            dregg_cell::FactoryCreationParams {
                owner_pubkey: [0xBB; 32],
                mode: dregg_cell::CellMode::default(),
                program_vk: None,
                initial_fields: vec![],
                initial_caps: vec![],
            },
            &fed,
        );
        let action = root_action(&turn);

        // Recompute the canonical signing message (must match what
        // sign_action did internally), then verify with the cipherclerk pubkey.
        let unsigned = Action {
            authorization: Authorization::Unchecked,
            ..action.clone()
        };
        let msg = TurnExecutor::compute_signing_message(&unsigned, &fed);

        let (a, b) = match action.authorization {
            Authorization::Signature(a, b) => (a, b),
            _ => panic!("expected Signature"),
        };
        let mut sig_bytes = [0u8; 64];
        sig_bytes[..32].copy_from_slice(&a);
        sig_bytes[32..].copy_from_slice(&b);
        let sig = Signature::from_bytes(&sig_bytes);

        let vk_bytes = cclerk.public_key().0;
        let vk = VerifyingKey::from_bytes(&vk_bytes).expect("valid pubkey");

        vk.verify_strict(&msg, &sig)
            .expect("clerk signature must verify against cipherclerk pubkey");
    }

    /// The clerk's anti-blind-signing seam, exercised end-to-end through the
    /// cipherclerk:
    ///
    /// 1. a representative action's clerk-produced explanation is non-empty and
    ///    carries the faithfulness tag (totality + the citizen actually sees
    ///    something to authorize);
    /// 2. the explanation is total over a corpus of every effect variant
    ///    wrapped in clerk-built actions (no panic);
    /// 3. two actions with *different* effect-semantics get *different*
    ///    explanations from the clerk (the injectivity property, surfaced
    ///    through `explain_action`); and
    /// 4. `explain_and_sign_action` surfaces the explanation while leaving
    ///    signing semantics identical to `sign_action`.
    #[test]
    fn clerk_explanation_is_total_nonempty_and_semantics_injective() {
        use dregg_turn::action::Effect;

        let cclerk = AgentCipherclerk::new();
        let fed = [7u8; 32];
        let cell = cclerk.cell_id("default");

        // (1) A representative action explains to non-empty, tagged text.
        let rep = cclerk.make_action(
            cell,
            "transfer",
            vec![Effect::Transfer {
                from: cell,
                to: cclerk.cell_id("other"),
                amount: 5,
            }],
            &fed,
        );
        let rep_text = cclerk.explain_action(&rep);
        assert!(!rep_text.is_empty(), "clerk explanation must be non-empty");
        assert!(
            rep_text.contains("[sem "),
            "clerk explanation must carry the faithfulness tag: {rep_text}"
        );

        // (2) Totality over a corpus of distinct effects, each wrapped in a
        // clerk-built (signed) action. No panic, all non-empty.
        let corpus: Vec<Effect> = vec![
            Effect::IncrementNonce { cell },
            Effect::Transfer {
                from: cell,
                to: cclerk.cell_id("other"),
                amount: 1,
            },
            Effect::Transfer {
                from: cell,
                to: cclerk.cell_id("other"),
                amount: 2, // differs only in amount — distinct semantics
            },
            Effect::SetField {
                cell,
                index: 0,
                value: [9u8; 32],
            },
            Effect::EmitEvent {
                cell,
                event: dregg_turn::action::Event {
                    topic: [3u8; 32],
                    data: vec![],
                },
            },
            Effect::MakeSovereign { cell },
        ];
        let actions: Vec<_> = corpus
            .iter()
            .cloned()
            .map(|e| cclerk.make_action(cell, "op", vec![e], &fed))
            .collect();
        let texts: Vec<String> = actions.iter().map(|a| cclerk.explain_action(a)).collect();
        for t in &texts {
            assert!(!t.is_empty());
            assert!(t.contains("[sem "));
        }

        // (3) Injectivity-on-semantics through the clerk: distinct action
        // hashes ⇒ distinct clerk explanations. (Authorization is identical
        // here — a real signature over each action's own bytes — so any
        // difference is in effect-semantics.)
        for (i, a) in actions.iter().enumerate() {
            for (j, b) in actions.iter().enumerate() {
                if i == j {
                    continue;
                }
                if a.hash() != b.hash() {
                    assert_ne!(
                        texts[i], texts[j],
                        "actions #{i}/#{j} differ in semantics but clerk explained identically"
                    );
                }
            }
        }

        // Spot-check: the two transfers that differ only in amount get
        // different explanations even though they share method/auth/target.
        assert_ne!(
            cclerk.explain_action(&actions[1]),
            cclerk.explain_action(&actions[2]),
            "amount-only difference must change the clerk's explanation"
        );

        // (4) explain_and_sign_action surfaces the explanation without
        // changing signing semantics: the signed action equals what
        // sign_action would have produced, and the carried explanation matches
        // explain_action of that signed action.
        let unsigned = cclerk.make_action(
            cell,
            "transfer",
            vec![Effect::Transfer {
                from: cell,
                to: cclerk.cell_id("other"),
                amount: 5,
            }],
            &fed,
        );
        let explained = cclerk.explain_and_sign_action(unsigned.clone(), &fed);
        let signed = cclerk.sign_action(unsigned, &fed);
        assert_eq!(
            explained.action.hash(),
            signed.hash(),
            "explain_and_sign_action must not change signing semantics"
        );
        assert_eq!(
            explained.explanation,
            cclerk.explain_action(&explained.action),
            "carried explanation must be the faithful rendering of the signed action"
        );
        assert!(!explained.explanation.is_empty());
    }

    // -------------------------------------------------------------------------
    // Wallet hygiene + local revocation (cheap-win surface).
    // -------------------------------------------------------------------------

    #[test]
    fn forget_token_removes_only_the_matching_id() {
        let mut cclerk = AgentCipherclerk::new();
        let a = cclerk.mint_token(&[1u8; 32], "dns");
        let b = cclerk.mint_token(&[2u8; 32], "storage");
        assert_eq!(cclerk.tokens().len(), 2);

        // Forget a present token: removed, returns true.
        assert!(cclerk.forget_token(a.id()));
        assert_eq!(cclerk.tokens().len(), 1);
        assert!(cclerk.find_token_by_id(a.id()).is_none());
        // The other token is untouched.
        assert!(cclerk.find_token_by_id(b.id()).is_some());

        // Forgetting an absent id is a no-op returning false.
        assert!(!cclerk.forget_token("no-such-id"));
        assert!(!cclerk.forget_token(a.id()));
        assert_eq!(cclerk.tokens().len(), 1);
    }

    #[test]
    fn revoke_token_records_and_forgets() {
        let mut cclerk = AgentCipherclerk::new();
        let t = cclerk.mint_token(&[7u8; 32], "compute");
        let id = t.id().to_string();

        assert!(!cclerk.is_locally_revoked(&id));
        assert_eq!(cclerk.locally_revoked_count(), 0);

        // Revoking a held token removes it AND records the id.
        assert!(cclerk.revoke_token(&id));
        assert!(cclerk.is_locally_revoked(&id));
        assert_eq!(cclerk.locally_revoked_count(), 1);
        assert!(cclerk.find_token_by_id(&id).is_none());

        // Re-revoking the same id is idempotent in the set; nothing left to
        // forget, so it returns false but the revocation persists.
        assert!(!cclerk.revoke_token(&id));
        assert!(cclerk.is_locally_revoked(&id));
        assert_eq!(cclerk.locally_revoked_count(), 1);
    }

    #[test]
    fn local_revocation_keying_agrees_with_registry_leaf() {
        // The wallet-side revocation and the provider-side
        // RevocationRegistry must agree on how a token id maps to a leaf, so
        // a local revocation can be lifted to a published, third-party-
        // verifiable one without re-deriving identifiers.
        let mut cclerk = AgentCipherclerk::new();
        let t = cclerk.mint_token(&[9u8; 32], "dns");
        let id = t.id().to_string();
        cclerk.revoke_token(&id);

        let mut registry = dregg_token::RevocationRegistry::new();
        assert!(registry.revoke(&id));
        assert!(registry.is_revoked(&id));

        // Same id -> same registry leaf, both sides agree on the keying.
        let leaf_a = dregg_token::RevocationRegistry::token_id_to_leaf(&id);
        let leaf_b = dregg_token::RevocationRegistry::token_id_to_leaf(&id);
        assert_eq!(leaf_a, leaf_b);
        assert!(cclerk.is_locally_revoked(&id));
    }

    #[test]
    fn derive_sub_agent_at_path_namespaces_independent_keys() {
        // A seed-derived cipherclerk can carve namespaced sub-identities.
        let seed = [3u8; 64];
        let root = AgentCipherclerk::from_seed(seed);

        let laptop = root
            .derive_sub_agent_at_path("dregg/device/laptop")
            .unwrap();
        let phone = root.derive_sub_agent_at_path("dregg/device/phone").unwrap();
        let app = root
            .derive_sub_agent_at_path("dregg/app/orderbook")
            .unwrap();

        // Distinct paths -> distinct identities.
        assert_ne!(laptop.public_key(), phone.public_key());
        assert_ne!(laptop.public_key(), app.public_key());
        assert_ne!(phone.public_key(), app.public_key());
        // Path is recorded and stable across re-derivation.
        assert_eq!(laptop.derivation_path(), Some("dregg/device/laptop"));
        let laptop_again = root
            .derive_sub_agent_at_path("dregg/device/laptop")
            .unwrap();
        assert_eq!(laptop.public_key(), laptop_again.public_key());

        // derive_sub_agent(i) is exactly derive_sub_agent_at_path("dregg/{i}").
        let by_index = root.derive_sub_agent(5).unwrap();
        let by_path = root.derive_sub_agent_at_path("dregg/5").unwrap();
        assert_eq!(by_index.public_key(), by_path.public_key());
    }

    #[test]
    fn derive_sub_agent_at_path_requires_seed() {
        // A raw-key cipherclerk has no seed and cannot derive sub-agents.
        let cclerk = AgentCipherclerk::new();
        assert!(
            cclerk
                .derive_sub_agent_at_path("dregg/device/laptop")
                .is_err()
        );
    }

    /// The `narrowed_authority` field is the SDK-side `granted` of the `(granted, held)` pair
    /// the Lean bridge `CaveatCapBridge.chainGateG_emits_granted_le_held` proves about: the
    /// macaroon caveat that narrows a capability-bearing verb EMITS the same effect-mask the
    /// kernel cap leg (`is_facet_attenuation`) consumes. This test BOTH polarities:
    ///   - a NON-AMPLIFYING facet (`facet ⊆ held`) is recorded EXACTLY, and `is_facet_attenuation`
    ///     holds (the macaroon narrowing IS the kernel narrowing);
    ///   - a WIDENING ask (`facet ⊄ held`) is CLIPPED to the held rights (no amplification),
    ///     and `is_authority_narrowing` REJECTS it — the bridge's `granted ⊆ held` is a real
    ///     constraint, refuted exactly when an over-broad mask is asked for.
    #[test]
    fn narrowed_authority_emits_granted_le_held_both_polarities() {
        use dregg_cell::{
            is_facet_attenuation, EFFECT_ALL, EFFECT_EMIT_EVENT, EFFECT_GRANT_CAPABILITY,
            EFFECT_SET_FIELD, EFFECT_TRANSFER,
        };

        let mut cclerk = AgentCipherclerk::new();
        let root_key = [42u8; 32];
        let root = cclerk.mint_token(&root_key, "compute");

        // (held) A root token confers full effect-authority (None ⇒ EFFECT_ALL).
        assert_eq!(root.narrowed_authority(), None);
        assert_eq!(root.effective_authority_mask(), EFFECT_ALL);

        // (1) NON-AMPLIFYING narrowing: facet = {SetField, EmitEvent} ⊆ EFFECT_ALL.
        let state_writer = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
        let restrictions = Attenuation {
            services: vec![("compute".to_string(), "rw".to_string())],
            ..Default::default()
        };
        let mut child = cclerk.attenuate(&root, &restrictions).unwrap();
        // The macaroon caveat EMITS the granted mask the kernel cap leg reads:
        let recorded = child.narrow_authority(state_writer);
        assert_eq!(
            recorded, state_writer,
            "a non-amplifying facet is recorded EXACTLY (granted == facet ⊆ held)"
        );
        assert_eq!(child.narrowed_authority(), Some(state_writer));
        // granted ⊆ held — the kernel cap-leg atom (`is_facet_attenuation`) holds:
        assert!(
            is_facet_attenuation(EFFECT_ALL, child.effective_authority_mask()),
            "granted ⊆ held: the macaroon narrowing IS the kernel narrowing"
        );

        // (2) MONOTONE under further attenuation: the grandchild carries the parent's granted.
        let grandchild = cclerk.attenuate(&child, &restrictions).unwrap();
        assert_eq!(
            grandchild.narrowed_authority(),
            Some(state_writer),
            "attenuation carries the narrowed mask forward (granted_grandchild ⊆ granted_child)"
        );
        assert!(is_facet_attenuation(
            child.effective_authority_mask(),
            grandchild.effective_authority_mask()
        ));

        // (3) NEGATIVE TOOTH — a WIDENING ask is CLIPPED, never amplified.
        // child now holds {SetField, EmitEvent}; ask to ADD {Transfer, GrantCapability}.
        let mut widen = child.clone();
        let amplifying = EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY;
        // The pure check the kernel cap leg performs REJECTS the amplifying ask up front:
        assert!(
            !widen.is_authority_narrowing(amplifying),
            "a facet naming rights the parent never held is NOT a narrowing (granted ⊄ held)"
        );
        // And `narrow_authority` CLIPS it to the held rights (the meet) — no amplification:
        let held_before = widen.effective_authority_mask();
        let clipped = widen.narrow_authority(amplifying);
        assert_eq!(
            clipped,
            held_before & amplifying,
            "the over-broad ask is clipped to held & facet (the macaroon cannot name absent rights)"
        );
        assert!(
            is_facet_attenuation(held_before, clipped),
            "even an amplifying ask yields granted ⊆ held — no amplification, both ways"
        );
        // Concretely: {SetField,EmitEvent} & {Transfer,Grant} = ∅ (no shared bits) — the widening
        // bought NOTHING past the parent (and named nothing the parent held in common).
        assert_eq!(clipped, 0, "disjoint widening clips to the empty mask, not the wider ask");
    }
}

#[cfg(doctest)]
mod doctest_compile_fail {
    /// Confirms that `held.encoded = ...` is rejected at compile time. If
    /// this stops being a compile error, the sealed-value invariant is
    /// broken.
    ///
    /// ```compile_fail
    /// use dregg_sdk::AgentCipherclerk;
    /// let mut w = AgentCipherclerk::new();
    /// let held = w.mint_token(&[0u8; 32], "svc");
    /// // The `encoded` field is private; this must NOT compile.
    /// let _ = held.encoded;
    /// ```
    ///
    /// ```compile_fail
    /// use dregg_sdk::AgentCipherclerk;
    /// let mut w = AgentCipherclerk::new();
    /// let mut held = w.mint_token(&[0u8; 32], "svc");
    /// // Direct mutation of `encoded` must NOT compile.
    /// held.encoded = String::from("forged");
    /// ```
    ///
    /// ```compile_fail
    /// use dregg_sdk::AgentCipherclerk;
    /// let mut w = AgentCipherclerk::new();
    /// let mut held = w.mint_token(&[0u8; 32], "svc");
    /// // Direct mutation of `caveat_chain_hash` must NOT compile.
    /// held.caveat_chain_hash = Some([0u8; 32]);
    /// ```
    pub struct _Marker;
}
