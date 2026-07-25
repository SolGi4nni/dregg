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
    // `never_loop` is a CORRECTNESS lint and it is RIGHT: this body cannot reach a
    // second iteration, because the FAIL-CLOSED refusal at the bottom returns
    // unconditionally. That is deliberate (see the long note there), not an escape
    // that forgot to `continue` — refusing on the first expected predicate refuses
    // the presentation. `expect` rather than `allow` on purpose: when the sound
    // accept path lands and the body stops returning unconditionally, the
    // expectation goes unfulfilled and this comment is dragged back into review.
    #[expect(
        clippy::never_loop,
        reason = "the body FAIL-CLOSES unconditionally until a trusted facts_root PI exists"
    )]
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

        // (iii) Cryptographically verify the predicate STARK, BOUND to this
        // presentation's credential — via the THIRD-PARTY attestation path, NOT the
        // vacuous `verify_predicate_proof(&candidate.proof, candidate.proof.fact_commitment)`
        // (x==x) gate it replaces.
        //
        // The `state_root` fed to `verify_predicate_proof_third_party` is THIS
        // presentation's `final_state_root` — a genuine public input of the presentation
        // STARK, deterministic per token (`bridge/src/present.rs`), and the SAME value the
        // producer bound each predicate + attestation to (`presentation.rs`). The
        // attestation STARK forces `candidate.proof.fact_commitment` to be the blinded image
        // of a fact under that state root, and the predicate descriptor independently welds
        // `state_root` into the same commitment. That state_root binding closes cross-credential
        // REPLAY — but NOT the falsifier's attack: a fact FABRICATED under A's own
        // `final_state_root` with an INVENTED `facts_root`. verify() ACCEPTED that forgery under the
        // third_party call (the falsifier cross_credential_predicate_forgery_rejected proved it), so
        // the accept path below now FAIL-CLOSES rather than trust the prover-supplied facts_root.
        //
        // ⚠ RESIDUAL AIR GAP (co-tenant flag — Lean-authored, NOT this crate): `facts_root`
        // still has no source independent of the proof. The presentation descriptor
        // (`metatheory/Dregg2/Circuit/Emit` presentation family) does not expose `facts_root`
        // as a public input, so it is read off `attestation.facts_root` here and the
        // attestation's root-equality check is vacuous. The STATE-ROOT binding above is real
        // and closes the cross-credential replay; the FACTS-ROOT binding — which would also
        // refuse a fact FABRICATED under A's own `final_state_root` but under an INVENTED
        // `facts_root` — requires the presentation STARK to prove and expose `facts_root` over
        // the token's real fact set, then passing THAT trusted root here. That AIR change is
        // the exact residual; it is out of scope for a Rust fix and must be done in Lean.
        //
        // BINDING SOUNDNESS (model, PROVEN): the mathematical heart of that fix — "if the
        // attestation authenticates a member against a `facts_root` equal to the credential's
        // committed root, the member IS one of the committed leaves; a fabricated fact has no
        // authenticating co-path" — is proven (no sorry, no axioms, under `hash_4_to_1`
        // injectivity) in `metatheory/Dregg2/Circuit/Emit/AttestedFactsRootModel.lean`
        // (`attested_member_is_committed` / `fabricated_member_refused`). What is NOT yet
        // discharged, and is why this stays FAIL-CLOSED: the emitted presentation descriptor
        // exposes no `facts_root` PI, AND the credential commits no attribute-facts tree whose
        // root that PI could equal (the predicate fact `hash_fact(blake3(name),[value,0,0])` is a
        // different symbol space than the fold-chain facts, so `facts_root != derivation_state_root`).
        // Landing it is a campaign: issuance/convert (commit the attribute-facts tree) → the
        // presentation descriptor (expose + weld its root to the trusted derivation) → the
        // attestation (real co-path into that tree) → this call.
        //
        // HONEST FLOOR: even fully bound, this predicate proof inherits the deployed STARK/FRI
        // soundness floor (project-fri-soundness-reality) — a proof, not an on-chain-settled
        // fact. Do NOT read a pass here as "sound".
        // FAIL-CLOSED (2026-07-24): predicate accept is UNSOUND in Rust today, so we REFUSE.
        // The only `facts_root` available is `attestation.facts_root` — PROVER-SUPPLIED — so binding
        // against it is vacuous (a forger mints an attestation whose facts_root makes their fabricated
        // fact a member). The falsifier `cross_credential_predicate_forgery_rejected` proved verify()
        // ACCEPTED the forgery under the old `verify_predicate_proof_third_party` call: the trusted
        // state_root binding alone cannot refuse a fact fabricated under THIS state_root with an
        // INVENTED facts_root. A SOUND accept needs a TRUSTED facts_root exposed as a
        // presentation-STARK public input (the AIR residual named above, Lean-authored — out of scope
        // for this crate). Until it lands, refuse beats accept-forgery.
        return Err(VerificationError::PredicateProofInvalid {
            attribute: expected.attribute.clone(),
        });
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
