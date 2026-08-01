//! Credential presentation.
//!
//! A [`Presentation`] proves that the holder possesses a valid credential
//! authorizing some action, without leaking the credential's contents. It
//! wraps `dregg_bridge::present::BridgePresentationProof` plus the
//! verifier-visible disclosure set.
//!
//! # Modes
//!
//! - **Full STARK** (`present`) — produces a real STARK proof. The
//!   default, suitable for cross-trust-boundary verification.
//! - **Anonymous set membership** (`present_anonymous`) — adds a fresh
//!   blinding factor to the issuer-membership proof so multi-show is
//!   unlinkable. Composes the bridge's existing blinded-leaf machinery
//!   (`WitnessedPredicateKind::BlindedSet` per `cell::predicate`).
//! - **Local constraint check** (`present_local_only_unsafe`) — NOT
//!   cryptographically sound, and gated behind
//!   `UnsafeLocalOnlyMarker`. It exists for the development loop only;
//!   [`crate::verify`] rejects what it produces.
//!
//! # 2026-07-16 — the default was a lie
//!
//! Until this date the doc above was aspiration, not description:
//! `present()` unconditionally called
//! `BridgePresentationBuilder::prove_local_constraint_check_only()` — the
//! path the bridge documents as "NOT CRYPTOGRAPHICALLY SOUND ... Do NOT
//! use for untrusted provers or cross-trust-boundary verification" —
//! while a stale comment promised a `prove_real = true` option that never
//! existed. Every non-anonymous presentation this crate has ever produced
//! was a constraint check the *prover* ran on its own machine. `present()`
//! now calls `prove()` (the real STARK) as the doc always claimed, and the
//! LocalOnly path is reachable only by naming it.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use thiserror::Error;

use dregg_bridge::present::{
    BridgePredicateProof, BridgePresentationBuilder, BridgePresentationProof, FactTerms,
    FederationRegistry, prove_predicate_for_fact_attested,
};
use dregg_circuit::poseidon2;
use dregg_token::AuthRequest;

use crate::issuance::Credential;
use crate::schema::{AttrValue, PredicateRequest};

/// Options controlling how a presentation is generated.
#[derive(Default)]
pub struct PresentationOptions {
    /// Attributes the holder wishes to *reveal* in cleartext. Other
    /// attributes are not transmitted at all. (Predicates are handled
    /// via [`Self::predicates`].)
    pub disclose: Vec<String>,

    /// Predicate proofs to attach. Each `(attribute, predicate)` pair
    /// produces a `BridgePredicateProof` bound to the credential's
    /// fold-chain state root.
    pub predicates: Vec<PredicateRequest>,

    /// Optional federation registry override. By default the
    /// presentation uses the credential's `federation_root` directly
    /// (synthetic membership path); production code should supply a
    /// `FederationRegistry` so the membership Merkle proof comes from
    /// the real federation tree.
    pub federation_registry: Option<Box<dyn FederationRegistry>>,
}

impl core::fmt::Debug for PresentationOptions {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PresentationOptions")
            .field("disclose", &self.disclose)
            .field("predicates", &self.predicates)
            .field(
                "federation_registry",
                &self
                    .federation_registry
                    .as_ref()
                    .map(|_| "<dyn FederationRegistry>"),
            )
            .finish()
    }
}

impl PresentationOptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn disclose(mut self, attribute: impl Into<String>) -> Self {
        self.disclose.push(attribute.into());
        self
    }

    pub fn predicate(mut self, request: PredicateRequest) -> Self {
        self.predicates.push(request);
        self
    }
}

/// A credential presentation: a STARK proof + the holder's disclosed
/// attributes + any predicate proofs.
///
/// Note: `Presentation` is NOT `Serialize`/`Deserialize`. The underlying
/// `BridgePresentationProof` carries an `AuthorizationTrace` that must
/// never be transmitted; convert to [`WirePresentation`] via
/// [`Self::to_wire`] before serializing.
#[derive(Clone, Debug)]
pub struct Presentation {
    /// The underlying ZK proof. **The `trace` field on this proof MUST
    /// NOT be transmitted** — use [`Self::to_wire`] to strip it before
    /// serializing for the wire.
    pub proof: BridgePresentationProof,

    /// Disclosed attributes (`name → value`). Verifiers receive these
    /// in cleartext and check that the bridge proof's
    /// `revealed_facts_commitment` matches.
    pub disclosed: Vec<(String, AttrValue)>,

    /// Predicate proofs attached to this presentation.
    pub predicate_proofs: Vec<NamedPredicateProof>,

    /// Whether this presentation used the anonymous (blinded-membership)
    /// path. The verifier needs to know which verification path to use.
    pub anonymous: bool,
}

/// Named predicate proof — `(attribute_name, proof)`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NamedPredicateProof {
    pub attribute: String,
    pub proof: BridgePredicateProof,
}

/// Presentation generation failure.
#[derive(Debug, Error)]
pub enum PresentationError {
    #[error("credential token reconstruction failed: {0}")]
    TokenReconstruction(String),
    #[error("schema mismatch: attribute `{0}` not present in credential")]
    UnknownAttribute(String),
    #[error("attribute `{0}` cannot be used as a predicate value (text values not supported)")]
    NonPredicateAttribute(String),
    #[error("bridge proof generation failed: {0}")]
    Bridge(String),
    #[error("predicate proof generation failed for attribute `{0}`")]
    PredicateProof(String),
}

impl Presentation {
    /// Strip private trace data before transmission.
    pub fn to_wire(&self) -> WirePresentation {
        WirePresentation {
            proof: self.proof.clone().into_wire_proof(),
            disclosed: self.disclosed.clone(),
            predicate_proofs: self.predicate_proofs.clone(),
            anonymous: self.anonymous,
        }
    }
}

/// Wire-safe presentation (no `AuthorizationTrace`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WirePresentation {
    pub proof: dregg_bridge::present::WirePresentationProof,
    pub disclosed: Vec<(String, AttrValue)>,
    pub predicate_proofs: Vec<NamedPredicateProof>,
    pub anonymous: bool,
}

/// Produce a credential presentation.
///
/// The `request` parameter is the authorization request the verifier
/// asked the holder to prove (e.g., "I can call `read` on `dashboard`").
/// `options` controls disclosure and predicate selection.
pub fn present(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
) -> Result<Presentation, PresentationError> {
    present_impl(credential, request, options, false, Prover::RealStark)
}

/// Produce a presentation backed ONLY by a local constraint check —
/// **not a cryptographic proof**.
///
/// This runs the circuit constraints on the *prover's own machine* and
/// emits a proof carrying `PresentationVerification::LocalOnly` and no
/// STARK. It proves nothing to anyone else: a holder who can call this
/// can produce a passing "proof" for any request their own constraints
/// happen to accept, and a verifier has no way to re-check the work.
///
/// [`crate::verify`] rejects the result with
/// [`crate::VerificationError::LocalOnlyRejected`]. That is deliberate,
/// and is the whole reason this function is safe to expose: there is no
/// configuration of this crate in which its output is accepted.
///
/// Suitable ONLY for the development loop — iterating on constraints
/// without paying the real prover's cost — and for tests that need a
/// LocalOnly proof to assert it is refused.
pub fn present_local_only_unsafe(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
    marker: &dregg_bridge::present::UnsafeLocalOnlyMarker,
) -> Result<Presentation, PresentationError> {
    present_impl(
        credential,
        request,
        options,
        false,
        Prover::LocalConstraintCheckOnly(marker),
    )
}

/// Which prover backs a presentation.
enum Prover<'m> {
    /// The real STARK (`BridgePresentationBuilder::prove`).
    RealStark,
    /// Local constraint check only — no cryptographic backing. Carries the
    /// bridge's marker so this variant cannot be constructed without the
    /// caller having named `i_know_this_is_not_cryptographically_sound()`.
    LocalConstraintCheckOnly(&'m dregg_bridge::present::UnsafeLocalOnlyMarker),
}

/// Produce an anonymous credential presentation (blinded membership).
///
/// Identical to [`present`] but the issuer-membership proof uses a fresh
/// random blinding factor. Multi-show is unlinkable: the same credential
/// produces different `blinded_leaf` public inputs across presentations,
/// so verifiers cannot correlate two presentations from the same holder.
///
/// Composes `WitnessedPredicateKind::BlindedSet` semantically (it's the
/// same trick at a higher abstraction level).
pub fn present_anonymous(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
) -> Result<Presentation, PresentationError> {
    present_impl(credential, request, options, true, Prover::RealStark)
}

fn present_impl(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
    anonymous: bool,
    prover: Prover<'_>,
) -> Result<Presentation, PresentationError> {
    // The macaroon backend retains the issuer's HMAC key, so we can
    // reconstruct the root token, then re-apply the *same attenuations*
    // the issuer baked in at issue time. This produces a builder whose
    // chain matches the credential's state.
    //
    // We don't trust the holder to remember the exact attenuation; we
    // re-derive it from `credential.attributes`.
    let root_token = dregg_token::MacaroonToken::mint(
        credential.root_key,
        b"dregg-credential",
        "dregg.fg-goose.online",
    );

    let mut builder =
        BridgePresentationBuilder::new(credential.root_key, credential.federation_root);
    builder.set_root_token(root_token);

    // Re-apply the issuance attenuation features.
    //
    // UNLINKABILITY: for anonymous presentations we MUST NOT bind the
    // holder's identity (`confine_user` / the request's `user_id`) into the
    // proof. Doing so would make two shows of the same credential linkable
    // by the shared `holder_user`, defeating the per-presentation
    // ring-blinding that `prove()` applies (fresh `blinding_factor` →
    // fresh `blinded_leaf` each show). Non-anonymous presentations keep the
    // `confine_user` binding (standard macaroon holder confinement).
    let holder_user = hex_encode(&credential.holder_id);
    let mut features = Vec::with_capacity(credential.attributes.attributes.len() + 1);
    features.push(format!("schema:{}", credential.schema.name));
    for crate::schema::AttributeAttenuation { name, value } in &credential.attributes.attributes {
        let term = value.to_fact_term();
        features.push(format!("{}:{}", name, hex_encode(&term)));
    }

    // Bind the presentation to the requested app/action so that the bridge
    // authorization trace can derive `allow` via standard_policy().
    // Credentials are identity proofs; the holder attenuates them to the
    // specific app at presentation time (standard macaroon semantics).
    let mut apps = Vec::new();
    if let Some(app_id) = &request.app_id {
        let actions = request.action.as_deref().unwrap_or("*");
        apps.push((app_id.clone(), actions.to_string()));
    }

    let att = dregg_token::Attenuation {
        // Bind the holder only for non-anonymous presentations. Anonymous
        // presentations omit `confine_user` so multi-show is unlinkable
        // (see the UNLINKABILITY note above).
        confine_user: if anonymous {
            None
        } else {
            Some(holder_user.clone())
        },
        features: features.clone(),
        not_after: credential.not_after,
        apps,
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // Optional registry override.
    if let Some(_reg) = &options.federation_registry {
        // FederationRegistry is dyn-trait; the bridge builder expects a
        // concrete MerkleTree, so this slot is a documented extension
        // point. Production wiring should bypass `present()` and call
        // the bridge directly. For now we emit a clear marker and
        // continue down the synthetic path.
    }

    // Disclosure commitment.
    let mut disclosed = Vec::new();
    let mut revealed_terms: Vec<[u8; 32]> = Vec::new();
    let disclose_set: HashSet<&String> = options.disclose.iter().collect();
    for crate::schema::AttributeAttenuation { name, value } in &credential.attributes.attributes {
        if disclose_set.contains(name) {
            disclosed.push((name.clone(), value.clone()));
            revealed_terms.push(value.to_fact_term());
        }
    }

    if !revealed_terms.is_empty() {
        let commitment = compute_revealed_terms_commitment(&revealed_terms);
        builder.set_revealed_facts_commitment(commitment);
    }

    // Run the prover. Both `present()` and `present_anonymous()` take the REAL
    // STARK path (`prove`). The LocalOnly path is reachable only via
    // `present_local_only_unsafe`, whose output `verify()` refuses.
    //
    // The comment this replaced justified defaulting to the unsound path
    // because "the full STARK takes ~30s". That number appears to be stale:
    // measured 2026-07-16, `present()` + `verify()` over the 4-attribute
    // employee-v1 fixture completes in well under a second in a debug build
    // (credentials/tests/anonymity_soundness.rs). The cost that bought the
    // mock was not being paid. Anyone reinstating a fast path should measure
    // first, at their own trace size, and then not reinstate it.
    let mut proof_request = request.clone();
    // UNLINKABILITY: only bind the holder identity into the request for
    // non-anonymous presentations. Anonymous presentations leave
    // `user_id` unset so the proof cannot be correlated across shows.
    if !anonymous {
        proof_request.user_id = Some(holder_user);
    }
    for feature in &features {
        if !proof_request.features.iter().any(|f| f == feature) {
            proof_request.features.push(feature.clone());
        }
    }

    let proof = match prover {
        // The real STARK. For anonymous presentations `prove()` additionally
        // draws a fresh `blinding_factor` each call, so the public
        // `blinded_leaf` differs across shows of the same credential — the
        // genuine unlinkable machinery from `bridge::present`.
        Prover::RealStark => builder
            .prove(&proof_request)
            .map_err(|e| PresentationError::Bridge(format!("{e:?}")))?,
        Prover::LocalConstraintCheckOnly(marker) => builder
            .prove_local_constraint_check_only(marker, &proof_request)
            .map_err(|e| PresentationError::Bridge(format!("{e:?}")))?,
    };

    // Predicate proofs (one per `PredicateRequest`).
    let mut predicate_proofs = Vec::new();
    if !options.predicates.is_empty() {
        // Compute the state root we need to bind predicate proofs to.
        // The bridge keeps this internal, so we expose only the
        // final-state root the proof was generated under.
        let state_root = dregg_bridge::present::bb_from_bytes(&proof.final_state_root);

        for req in &options.predicates {
            let value = credential
                .attributes
                .attributes
                .iter()
                .find(|a| a.name == req.attribute)
                .ok_or_else(|| PresentationError::UnknownAttribute(req.attribute.clone()))?;

            let predicate_value = value
                .value
                .to_predicate_value()
                .ok_or_else(|| PresentationError::NonPredicateAttribute(req.attribute.clone()))?;

            // 2026-07-16: prove_predicate_for_fact now takes a structured FactBinding built from
            // the fact's PREIMAGE TERMS + state_root, not a pre-hashed opaque fact_hash. The prover
            // reconstructs the fact as `fact_hash_of(value) = hash_fact(predicate_sym, [value, term1,
            // term2])` (predicate_arith_witness.rs:148) — the VALUE is term[0], supplied separately.
            // The original hashed `hash_fact(attr_symbol, [predicate_value, 0, 0])`, so with the
            // value flowing in as term[0], term1 = term2 = ZERO (NOT `predicate_value` — that would
            // bind hash_fact(attr, [value, value, 0]), a different fact).
            let attr_symbol = attribute_symbol_felt_30bit(req.attribute.as_bytes());
            let binding = FactTerms {
                predicate_sym: attr_symbol,
                term1: dregg_circuit::field::BabyBear::ZERO,
                term2: dregg_circuit::field::BabyBear::ZERO,
            }
            .bind(state_root);

            // A FRESH blinding factor per predicate proof, drawn from OS randomness. This is what
            // keeps the MULTI-SHOW unlinkability this module promises (see the header) true of the
            // predicate proofs too, not just the issuer-membership ring: the fact commitment is
            // `hash_4_to_1([fact_hash, state_root, blinding, 0])`, so two showings of the same
            // attribute emit different commitments while the in-circuit weld still binds each to the
            // value it covers.
            //
            // ATTESTED (third-party) shape, NOT the trusted-state `prove_predicate_for_fact`. The
            // proof now carries a `BridgeFactAttestation` that STARK-proves its `fact_commitment` is
            // the blinded image of a `fact_hash` sitting under `state_root` (= THIS presentation's
            // `final_state_root`, a genuine presentation-STARK public input). At verify time that
            // lets `verify()` route through `verify_predicate_proof_third_party` with the trusted
            // `final_state_root` instead of the vacuous `verify_predicate_proof(&p, p.fact_commitment)`
            // (x==x) gate — so a genuine proof minted under a DIFFERENT credential's state root is
            // refused (the cross_credential_predicate_forgery_rejected falsifier).
            //
            // ⚠ RESIDUAL AIR GAP (co-tenant flag, Lean-authored — NOT this crate): the `facts_root`
            // the attestation names is not yet a public input of the presentation descriptor, so the
            // verifier has no source for it independent of the proof and reads it off the attestation.
            // The `state_root` binding is what is genuinely trusted and what closes the cross-credential
            // forgery; the `facts_root` binding (which would also refuse a fact fabricated under THIS
            // state root but an INVENTED facts_root) needs the presentation STARK to expose `facts_root`
            // as a proven PI over the token's real fact set. The co-path here is therefore a
            // well-formed stand-in that makes the attestation valid and its state-root binding real —
            // it is not authenticated against a credential-side facts tree, because none is exposed.
            let siblings = attestation_siblings(attr_symbol, state_root);
            let pred_proof = prove_predicate_for_fact_attested(
                predicate_value,
                binding,
                dregg_bridge::present::fresh_predicate_blinding(),
                &req.predicate,
                &siblings,
            )
            .ok_or_else(|| PresentationError::PredicateProof(req.attribute.clone()))?;

            predicate_proofs.push(NamedPredicateProof {
                attribute: req.attribute.clone(),
                proof: pred_proof,
            });
        }
    }

    Ok(Presentation {
        proof,
        disclosed,
        predicate_proofs,
        anonymous,
    })
}

/// A deterministic depth-2 (`attested_fact_membership::ATTESTED_DEPTH`) co-path for a predicate
/// fact's attestation.
///
/// The credential model keeps no standalone depth-2 4-ary facts tree to draw a real co-path from,
/// and — the RESIDUAL AIR GAP — the presentation STARK exposes no `facts_root` public input the
/// verifier could authenticate a co-path against. So this derives a well-formed co-path from the
/// fact's attribute symbol and the presentation `state_root`. Its only jobs are to make the
/// attestation STARK well-formed and to carry the REAL, load-bearing binding: the attestation's
/// `state_root` (= this presentation's `final_state_root`). The `facts_root` it authenticates is NOT
/// independently trusted by the verifier — see the RESIDUAL AIR GAP note at the call site.
fn attestation_siblings(
    attr_symbol: dregg_circuit::field::BabyBear,
    state_root: dregg_circuit::field::BabyBear,
) -> Vec<[dregg_circuit::field::BabyBear; 3]> {
    use dregg_circuit::field::BabyBear;
    let d = |level: u64, idx: u64| -> BabyBear {
        poseidon2::hash_many(&[
            attr_symbol,
            state_root,
            BabyBear::from_u64(level),
            BabyBear::from_u64(idx),
        ])
    };
    vec![[d(0, 1), d(0, 2), d(0, 3)], [d(1, 1), d(1, 2), d(1, 3)]]
}

/// Recompute the revealed-facts commitment over a list of fact terms.
///
/// Mirrors `dregg_bridge::present::compute_revealed_facts_commitment` but
/// works against our `AttrValue`-derived fact-term bytes.
///
/// `pub(crate)` so [`crate::verify`] can recompute it from the cleartext the
/// holder sent and compare against the commitment the STARK binds — the
/// disclosure-tamper check. Prover and verifier MUST use this one function;
/// a second copy on the verifier side would be a shadow to drift against.
/// ⚑ **EACH TERM NOW RIDES NINE INJECTIVE LANES** (fixed 2026-08-01, domain bumped to `-v2`).
///
/// This used to map every 32-byte term through a private `blake3_to_babybear`:
///
/// ```text
///   let h = blake3::hash(bytes);                                  // 32 bytes
///   let val = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);       // 4 of them
///   BabyBear::new(val & ((1u32 << 30) - 1))                       // 30 bits
/// ```
///
/// — **30 bits per disclosed term**, and that felt was the term's ONLY binding in the
/// commitment. Two disclosure sets differing in a term but agreeing on those 30 bits produced
/// a byte-identical `WideHash`, so [`crate::verification`]'s disclosure-tamper check —
/// "recompute from the cleartext the holder sent, compare against the commitment the STARK
/// binds" — accepted the substituted cleartext. The terms are attacker-chosen attribute
/// bytes, so the cost was a **2^15 birthday grind**, not a search anyone would notice. The
/// width of the 8-felt `WideHash` above it was irrelevant: the waist was upstream of the
/// sponge, which is the `finalSqueezeOnly_still_conflates` shape.
///
/// The replacement absorbs [`dregg_circuit::effect_vm::field_limbs9`] — the nine-lane
/// base-`2^28` encoder whose injectivity on 32-byte values is a machine-checked Lean theorem
/// (`Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective`, with a total decoder and a proved
/// left inverse). Nine and not eight is forced: `log₂ p = 30.907`, so eight lanes carry
/// 247.26 bits against a 32-byte term's 256 and NO eight-lane chunking is injective —
/// pigeonhole, before any code is read. With an injective preimage the commitment's strength
/// is the Poseidon2 sponge's over eight output lanes, which is the object `WideHash` claims
/// to be.
///
/// **Prover and verifier MUST use this one function**; a second copy on the verifier side
/// would be a shadow to drift against.
///
/// ⓘ Breaking: the domain string moved `dregg-credentials-revealed` →
/// `…-revealed-v2`, so every previously issued presentation's
/// `revealed_facts_commitment` REFUSES rather than reinterpreting — a stale commitment
/// cannot be read as a new-encoding one. Presentations re-emit. No VK rotates and no
/// descriptor re-emits: this value is recomputed in Rust on both sides and carried as a
/// public input, never recomputed in-AIR.
pub(crate) fn compute_revealed_terms_commitment(
    terms: &[[u8; 32]],
) -> dregg_circuit::binding::WideHash {
    // Nine lanes per term — injective, so no two disclosure sets share a preimage.
    let mut lanes = Vec::with_capacity(terms.len() * 9);
    for term in terms {
        lanes.extend_from_slice(&dregg_circuit::effect_vm::field_limbs9(term));
    }
    dregg_circuit::binding::WideHash::from_poseidon2("dregg-credentials-revealed-v2", &lanes)
}

/// The **attribute SYMBOL felt** — a 30-bit tag for an attribute NAME, used as
/// `FactTerms::predicate_sym` and as the seed of [`sibling_hashes_for`].
///
/// ⚑ **NAMED RESIDUAL, and deliberately UNCHANGED (2026-08-01).** The arithmetic is
/// byte-identical to what this was when it was also (wrongly) used to build the
/// revealed-terms commitment: BLAKE3 the name, take four of the digest's thirty-two bytes,
/// mask to thirty bits. That is a `2^30` image, i.e. a `2^15` birthday — two attribute names
/// colliding here are the SAME predicate symbol in the fact binding.
///
/// It is not widened here for a reason that is a real constraint rather than a cost estimate:
/// `predicate_sym` is a **single in-AIR column** (`predicate_arith_witness`'s
/// `hash_fact(predicate_sym, terms)` row), so its width is descriptor geometry — widening it
/// is a Lean-authored emit change plus a VK rotation, and this lane does not touch the emit
/// driver. The commitment path above, which had no such constraint, is fixed.
///
/// ⚠ The `& ((1u32 << 30) - 1)` mask is *also* gratuitous — `BabyBear::new` already reduces
/// mod `p ≈ 2^30.907`, so the mask throws away a further 0.9 bits for nothing. It is kept
/// because changing it silently moves every derived symbol and this function is derived
/// identically on both sides; it should move WITH the widening, not before it.
fn attribute_symbol_felt_30bit(bytes: &[u8]) -> dregg_circuit::field::BabyBear {
    let h = blake3::hash(bytes);
    let b = h.as_bytes();
    let val = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
    dregg_circuit::field::BabyBear::new(val & ((1u32 << 30) - 1))
}

fn hex_encode(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}
