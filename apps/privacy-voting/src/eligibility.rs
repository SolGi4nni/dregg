//! Eligibility credential verification.
//!
//! Voters obtain a [`DelegatedToken`] from a known eligibility issuer (e.g., a
//! census authority, a DAO membership service). At ballot-submission time, the
//! voter forwards the envelope to the voting server; the server verifies:
//!
//! 1. The envelope's `delegator_public_key` matches a configured authority
//!    (a single `TrustedKey`, or one of several `TrustedKeys`).
//! 2. The Ed25519 signature over [`DelegatedToken::envelope_hash`] verifies
//!    under that key.
//!
//! ## Why we do not call `receive_signed_delegation`
//!
//! `AgentCipherclerk::receive_signed_delegation` requires `delegatee == cipherclerk.public_key`.
//! Eligibility credentials are addressed to the VOTER, not the server. So we
//! verify the envelope's signature directly using the same signing message that
//! `envelope_hash()` returns (which is the value that was signed at issuance).
//!
//! ## Unlinkability
//!
//! The credential's delegatee field IS the voter's public key — knowing it would
//! let an observer link votes to identities. So this module's verifier returns
//! only `Ok(())` / `Err(...)`; **callers MUST NOT persist the voter pubkey
//! alongside the ballot commitment.** See `server.rs` for how the double-vote
//! set is kept separate from the queue.

use std::collections::HashSet;

use ed25519_dalek::Verifier;
use dregg_sdk::cipherclerk::DelegatedToken;
use dregg_types::PublicKey;
use thiserror::Error;

/// Authority policy for accepting eligibility credentials.
///
/// Mirrors [`dregg_sdk::DelegationAuthority`] but is restricted to the two
/// variants safe for this app:
/// - `Single`: only credentials from one issuer are accepted.
/// - `Federation`: credentials from any issuer in the set are accepted.
///
/// The `Open` variant from the SDK is deliberately omitted — there is no
/// `Open` here, because an open-authority voting app would let anyone vote.
#[derive(Clone, Debug)]
pub enum EligibilityAuthority {
    Single(PublicKey),
    Federation(HashSet<PublicKey>),
}

impl EligibilityAuthority {
    /// `true` iff `key` is accepted as an issuer.
    pub fn accepts(&self, key: &PublicKey) -> bool {
        match self {
            EligibilityAuthority::Single(pk) => pk == key,
            EligibilityAuthority::Federation(set) => set.contains(key),
        }
    }
}

#[derive(Debug, Error)]
pub enum EligibilityError {
    #[error("issuer {got:?} is not an authorized eligibility issuer")]
    UnauthorizedIssuer { got: PublicKey },
    #[error("signature on credential envelope failed to verify: {0}")]
    InvalidSignature(String),
    #[error("malformed issuer public key: {0}")]
    MalformedKey(String),
}

/// Verify that `credential` is a valid eligibility credential.
///
/// Returns `Ok(voter_pubkey)` on success, where `voter_pubkey` is the
/// envelope's `delegatee` — the holder of the credential. The CALLER is
/// responsible for using this only to deduplicate double-votes (in a
/// queue-disjoint set); it MUST NOT be persisted in the public ballot queue.
pub fn verify_eligibility(
    authority: &EligibilityAuthority,
    credential: &DelegatedToken,
) -> Result<PublicKey, EligibilityError> {
    // (1) Issuer authority check.
    if !authority.accepts(&credential.delegator_public_key) {
        return Err(EligibilityError::UnauthorizedIssuer {
            got: credential.delegator_public_key,
        });
    }

    // (2) Signature verification. `envelope_hash()` returns the canonical
    // 32-byte signing message used at delegation time, so we verify the
    // ed25519 signature directly against it.
    let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(&credential.delegator_public_key.0)
        .map_err(|e| EligibilityError::MalformedKey(e.to_string()))?;

    let signing_message = credential.envelope_hash();
    let signature = ed25519_dalek::Signature::from_bytes(&credential.delegator_signature.0);

    verifying_key
        .verify(&signing_message, &signature)
        .map_err(|e| EligibilityError::InvalidSignature(e.to_string()))?;

    Ok(credential.delegatee)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::cipherclerk::AgentCipherclerk;
    use dregg_token::Attenuation;

    /// Helper: issuer mints a token, then delegates it to `voter_pk`.
    fn issue_credential(issuer: &mut AgentCipherclerk, voter_pk: PublicKey) -> DelegatedToken {
        let root_token = issuer.mint_token(&[0x11; 32], "vote");
        let restrictions = Attenuation {
            services: vec![("vote".into(), "submit".into())],
            ..Default::default()
        };
        issuer
            .delegate(&root_token, &voter_pk, &restrictions)
            .expect("delegate")
    }

    #[test]
    fn valid_credential_accepted() {
        let mut issuer = AgentCipherclerk::new();
        let issuer_pk = issuer.public_key();
        let voter = AgentCipherclerk::new();
        let cred = issue_credential(&mut issuer, voter.public_key());

        let auth = EligibilityAuthority::Single(issuer_pk);
        let voter_pk = verify_eligibility(&auth, &cred).expect("must verify");
        assert_eq!(voter_pk, voter.public_key());
    }

    #[test]
    fn wrong_issuer_rejected() {
        // Adversarial: a credential signed by an UNAUTHORIZED issuer must be
        // rejected even if its signature is well-formed.
        let mut rogue_issuer = AgentCipherclerk::new();
        let voter = AgentCipherclerk::new();
        let cred = issue_credential(&mut rogue_issuer, voter.public_key());

        let real_issuer = AgentCipherclerk::new();
        let auth = EligibilityAuthority::Single(real_issuer.public_key());
        let r = verify_eligibility(&auth, &cred);
        assert!(matches!(
            r,
            Err(EligibilityError::UnauthorizedIssuer { .. })
        ));
    }

    #[test]
    fn tampered_credential_rejected() {
        // Adversarial: credentials with a forged signature or a tampered
        // envelope must both fail verification.
        let mut issuer = AgentCipherclerk::new();
        let issuer_pk = issuer.public_key();
        let voter = AgentCipherclerk::new();
        let auth = EligibilityAuthority::Single(issuer_pk);

        let mut cred = issue_credential(&mut issuer, voter.public_key());
        cred.delegator_signature = dregg_types::Signature([0xAB; 64]);
        let r = verify_eligibility(&auth, &cred);
        assert!(
            matches!(r, Err(EligibilityError::InvalidSignature(_))),
            "forged signature must be rejected"
        );

        let mut cred = issue_credential(&mut issuer, voter.public_key());
        cred.delegatee = PublicKey([0xCC; 32]);
        let r = verify_eligibility(&auth, &cred);
        assert!(
            matches!(r, Err(EligibilityError::InvalidSignature(_))),
            "tampered envelope must be rejected"
        );
    }

    #[test]
    fn federation_membership_checked() {
        let mut iss_a = AgentCipherclerk::new();
        let iss_b = AgentCipherclerk::new();
        let mut rogue = AgentCipherclerk::new();
        let voter = AgentCipherclerk::new();

        let mut set = HashSet::new();
        set.insert(iss_a.public_key());
        set.insert(iss_b.public_key());
        let auth = EligibilityAuthority::Federation(set);

        let cred = issue_credential(&mut iss_a, voter.public_key());
        verify_eligibility(&auth, &cred).expect("federation member must be accepted");

        let cred = issue_credential(&mut rogue, voter.public_key());
        let r = verify_eligibility(&auth, &cred);
        assert!(
            matches!(r, Err(EligibilityError::UnauthorizedIssuer { .. })),
            "outsider must be rejected"
        );
    }
}
