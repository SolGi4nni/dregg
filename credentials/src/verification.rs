//! Credential verification.
//!
//! A verifier consumes a [`crate::Presentation`] (or [`crate::presentation::WirePresentation`])
//! plus a [`VerificationOptions`] that captures the verifier's expectations
//! (which schema? what disclosure must be present? what predicates were
//! requested?). Verification rejects:
//!
//! 1. Bridge proof failure (the underlying STARK fails), OR the absence of
//!    a real STARK at all — a `LocalOnly` constraint check is refused
//!    unconditionally, since the verifier cannot re-check work the prover
//!    did on its own machine.
//! 2. Schema mismatch (the disclosed attributes do not belong to the
//!    expected schema).
//! 3. Predicate mismatch (the proof does not cover the predicate the
//!    verifier asked for).
//! 4. Revealed-facts commitment mismatch (the holder's cleartext
//!    disclosure does not commit to the value the proof witnesses).
//! 5. Anonymous-mode mismatch (verifier expects an anonymous proof,
//!    got a non-anonymous one, or vice versa).

use thiserror::Error;

use dregg_circuit::PresentationVerification;

use crate::presentation::Presentation;
use crate::revocation::{NonRevocationError, RevocationProof};
use crate::schema::{AttrValue, CredentialSchema, PredicateRequest};

/// Options carried by the verifier.
#[derive(Clone, Debug, Default)]
pub struct VerificationOptions {
    /// The schema the verifier expects.
    pub expected_schema: Option<CredentialSchema>,

    /// Attributes the verifier expects to be disclosed.
    pub expected_disclosure: Vec<String>,

    /// Predicate requests the verifier expects to be satisfied. The
    /// proof must contain a matching `NamedPredicateProof`.
    pub expected_predicates: Vec<PredicateRequest>,

    /// Whether the presentation must be anonymous (blinded membership).
    pub require_anonymous: bool,

    /// Optional non-revocation proof. If supplied the verifier performs
    /// a real non-membership check: it recomputes the revocation root
    /// from the proof's committed witness set, binds it to
    /// [`Self::expected_revocation_root`] (when set), and checks the
    /// credential's genuine absence from the committed set.
    pub revocation: Option<RevocationProof>,

    /// Externally-trusted revocation root the proof must be anchored
    /// against. When `Some`, the proof's root must equal it (rejecting
    /// stale or attacker-chosen roots). When `None`, the verifier still
    /// recomputes the root from the witness and checks genuine absence,
    /// but trusts the proof's own root (suitable only when the proof
    /// originates from a registry the caller already trusts).
    pub expected_revocation_root: Option<[u8; 32]>,

    /// Federation root the verifier expects the credential to be
    /// anchored against. When `Some`, this is compared against the
    /// proof's recovered federation root.
    pub expected_federation_root: Option<[u8; 32]>,
}

impl VerificationOptions {
    pub fn new() -> Self {
        Self::default()
    }
}

/// A successfully verified presentation.
#[derive(Clone, Debug)]
pub struct VerifiedPresentation {
    /// Attributes the verifier learned.
    pub disclosed: Vec<(String, AttrValue)>,
    /// The federation root the presentation was anchored against.
    pub federation_root: [u8; 32],
    /// Whether the proof used the anonymous path.
    pub anonymous: bool,
}

/// Verification failure.
#[derive(Debug, Error)]
pub enum VerificationError {
    #[error("bridge proof verification failed: {0:?}")]
    Bridge(PresentationVerification),
    #[error("required schema `{expected}` but presentation does not match")]
    SchemaMismatch { expected: String },
    #[error("expected disclosure of `{0}` but it was not revealed")]
    MissingDisclosure(String),
    #[error("expected predicate over `{0}` but it was not proven")]
    MissingPredicate(String),
    #[error("expected anonymous presentation, got non-anonymous (or vice versa)")]
    AnonymityMismatch,
    #[error("federation root mismatch (expected `{expected_hex}`)")]
    FederationRootMismatch { expected_hex: String },
    #[error("credential is revoked")]
    Revoked,
    #[error(
        "presentation carries no real STARK proof (LocalOnly = a constraint check the prover ran on its own machine); verification requires a cryptographic proof"
    )]
    LocalOnlyRejected,
    #[error("predicate proof for `{attribute}` failed cryptographic verification")]
    PredicateProofInvalid { attribute: String },
    #[error("predicate proof for `{attribute}` proves a different statement than requested")]
    PredicateMismatch { attribute: String },
    #[error("non-revocation witness does not commit to the proof's root")]
    RevocationRootMismatch,
    #[error("non-revocation proof anchored against an untrusted revocation root")]
    RevocationUnexpectedRoot,
    #[error(
        "disclosed cleartext does not match the revealed-facts commitment the proof witnesses (tampered or mismatched disclosure)"
    )]
    RevealedFactsMismatch,
}

/// Verify a presentation against the verifier's expectations.
pub fn verify(
    presentation: &Presentation,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    verify_inner(
        &presentation.disclosed,
        &presentation.predicate_proofs,
        presentation.anonymous,
        &presentation.proof,
        options,
    )
}

/// Verify a wire-form presentation. Equivalent to [`verify`] modulo the
/// stripped trace.
pub fn verify_anonymous(
    presentation: &Presentation,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    let mut opts = options.clone();
    opts.require_anonymous = true;
    verify(presentation, &opts)
}

fn verify_inner(
    disclosed: &[(String, AttrValue)],
    predicate_proofs: &[crate::presentation::NamedPredicateProof],
    anonymous: bool,
    proof: &dregg_bridge::present::BridgePresentationProof,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    // 1. Anonymity check.
    if options.require_anonymous && !anonymous {
        return Err(VerificationError::AnonymityMismatch);
    }

    // 2. Bridge proof check — FAIL CLOSED, unconditionally.
    //
    // A `LocalOnly` proof is a constraint check the PROVER ran on its own
    // machine. It carries no STARK, so a verifier cannot re-check any of it;
    // accepting one means believing the presenter's own report about its own
    // credential. That is exactly the `verified: bool` this crate exists to
    // replace (see the module doc on `apps/identity`), so there is no option
    // — `require_anonymous` or otherwise — that makes it acceptable.
    //
    // 2026-07-16: this check used to fire only when `options.require_anonymous`
    // was set, which is FALSE by default. Since `present()` also only ever
    // produced LocalOnly proofs, the crate's default present→verify round trip
    // performed zero cryptographic verification while returning a
    // `VerifiedPresentation`. Both halves are now fixed; this is the half that
    // must stay fixed even if a prover elsewhere regresses.
    match &proof.verification {
        PresentationVerification::Valid => {}
        PresentationVerification::LocalOnly => return Err(VerificationError::LocalOnlyRejected),
        other => return Err(VerificationError::Bridge(other.clone())),
    }

    // Require a real STARK proof object. `is_valid()` returns true only when a
    // real STARK proof is present AND verification is `Valid`, so this rejects
    // a hand-crafted `verification = Valid` carrying no proof — the mint-a-
    // consistent-fake attack that a field-tamper test never reaches.
    if !proof.is_valid() {
        return Err(VerificationError::LocalOnlyRejected);
    }

    // 3. Schema match. Each disclosed attribute must belong to the
    //    expected schema.
    if let Some(schema) = &options.expected_schema {
        for (name, _) in disclosed {
            if !schema.has_attribute(name) {
                return Err(VerificationError::SchemaMismatch {
                    expected: schema.name.clone(),
                });
            }
        }
    }

    // 4. Expected disclosure must be present.
    for expected in &options.expected_disclosure {
        if !disclosed.iter().any(|(n, _)| n == expected) {
            return Err(VerificationError::MissingDisclosure(expected.clone()));
        }
    }

    // 4b. Revealed-facts commitment: the cleartext the holder sent must be the
    //     cleartext the proof witnesses.
    //
    // `disclosed` is plain data travelling beside the proof — the holder can put
    // anything in it. The STARK binds `revealed_facts_commitment` as a public
    // input (bridge/src/present.rs:250), so recomputing it from the cleartext and
    // comparing is what makes the disclosure trustworthy. Without this, a holder
    // presents a genuine proof and then swaps the values: `verify()` hands the
    // caller a `VerifiedPresentation` carrying the ATTACKER's numbers.
    //
    // 2026-07-16: this check did not exist, though the module doc above has always
    // listed it as rejection reason 4. It could not have worked before today —
    // every non-anonymous `present()` produced a LocalOnly proof whose commitment
    // nothing bound. Now that `present()` emits a real STARK, the check has teeth.
    //
    // The empty case is not a hole to skip but a claim to check: a proof built with
    // no disclosures leaves the commitment at `WideHash::ZERO`, so a holder who
    // strips the cleartext out of a proof that HAD disclosures fails here rather
    // than downgrading to "disclosed nothing".
    let recomputed = if disclosed.is_empty() {
        dregg_circuit::binding::WideHash::ZERO
    } else {
        let terms: Vec<[u8; 32]> = disclosed.iter().map(|(_, v)| v.to_fact_term()).collect();
        crate::presentation::compute_revealed_terms_commitment(&terms)
    };
    if recomputed != proof.revealed_facts_commitment {
        return Err(VerificationError::RevealedFactsMismatch);
    }

    // 5. Expected predicates must be present AND cryptographically valid.
    //
    // SOUNDNESS: matching by attribute *name* alone is forgeable — a holder
    // could attach a `NamedPredicateProof { attribute: "age", .. }` whose
    // inner proof proves nothing (or proves a weaker statement). For every
    // requested predicate we:
    //   (i)   find a matching named proof,
    //   (ii)  require its proven statement to equal the requested predicate
    //         (same operator + threshold/bounds), not just the name, and
    //   (iii) verify the STARK cryptographically against the proof's own
    //         `fact_commitment` (which the proof's STARK binds to the
    //         witnessed value). A garbage / mismatched proof fails here.
    for expected in &options.expected_predicates {
        let candidate = predicate_proofs
            .iter()
            .find(|p| p.attribute == expected.attribute)
            .ok_or_else(|| VerificationError::MissingPredicate(expected.attribute.clone()))?;

        // (ii) The proof must prove exactly the requested statement.
        if candidate.proof.predicate != expected.predicate {
            return Err(VerificationError::PredicateMismatch {
                attribute: expected.attribute.clone(),
            });
        }

        // (iii) Cryptographically verify the predicate STARK. This proves the
        // WITNESSED STATEMENT — "some fact with commitment `c` satisfies the
        // predicate" — and rejects a name-only spoof carrying random bytes.
        //
        // ⚠ SOUNDNESS HOLE (LIVE — see the cross_credential_predicate_forgery_rejected
        // falsifier in credentials/tests/anonymity_soundness.rs, module note (b')):
        // the expected commitment passed here is the proof's OWN `fact_commitment`,
        // so the equality gate inside `verify_predicate_proof` is `x == x` — vacuous.
        // NOTHING binds `c` to (i) THIS presentation's credential / `final_state_root`
        // or (ii) the requested attribute beyond the holder-controlled
        // `candidate.attribute` string. A holder can therefore mint a genuine
        // `Gte(18)` proof from credential X (age 32) and attach it under
        // `attribute = "age"` to a presentation of credential A (age 15) — the STARK
        // verifies against its own `c` and the forgery is accepted.
        //
        // The SOUND replacement is `verify_predicate_proof_third_party(&candidate.proof,
        // facts_root, final_state_root)`, which manufactures the expected commitment
        // from a `BridgeFactAttestation` proving Merkle membership under a `facts_root`
        // the verifier independently trusts. That routing is BLOCKED on machinery not
        // yet wired: the presentation STARK exposes no `facts_root` public input, and
        // the producer (presentation.rs) attaches no attestation. Wiring both is a
        // circuit-level change tracked by the falsifier above; do NOT drop in the
        // third-party call before the producer attaches attestations (it would
        // fail-closed on every legitimate predicate presentation).
        if !dregg_bridge::present::verify_predicate_proof(
            &candidate.proof,
            candidate.proof.fact_commitment,
        ) {
            return Err(VerificationError::PredicateProofInvalid {
                attribute: expected.attribute.clone(),
            });
        }
    }

    // 6. Federation root check.
    if let Some(expected) = options.expected_federation_root
        && expected != proof.federation_root
    {
        return Err(VerificationError::FederationRootMismatch {
            expected_hex: hex_encode(&expected),
        });
    }

    // 7. Revocation check — a real non-membership check, not a trusted bool.
    //
    // The verifier recomputes the revocation root from the proof's
    // committed witness set, binds it to the trusted expected root (when
    // supplied), and checks the credential's genuine absence from the
    // committed set. A holder cannot escape revocation by flipping a
    // `revoked` boolean: dropping their own id from the witness changes the
    // recomputed root, which then fails the root-binding check.
    if let Some(rev) = &options.revocation {
        // When no externally-trusted root is configured, trust the proof's
        // own root for the binding step (the witness-commitment and
        // absence checks still run). When configured, enforce it.
        let expected_root = options.expected_revocation_root.unwrap_or(rev.root);
        match rev.verify_non_revocation(&expected_root) {
            Ok(()) => {}
            Err(NonRevocationError::Revoked) => return Err(VerificationError::Revoked),
            Err(NonRevocationError::RootMismatch) => {
                return Err(VerificationError::RevocationRootMismatch);
            }
            Err(NonRevocationError::UnexpectedRoot) => {
                return Err(VerificationError::RevocationUnexpectedRoot);
            }
        }
    }

    Ok(VerifiedPresentation {
        disclosed: disclosed.to_vec(),
        federation_root: proof.federation_root,
        anonymous,
    })
}

use crate::hex_encode;
