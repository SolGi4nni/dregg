//! Production `ThresholdVerifier` for `dregg-dfa` governed route-table swaps,
//! backed by `dregg-federation`'s `FederationCommittee` + `ThresholdQC` BLS
//! aggregate verifier.
//!
//! This lives in its own crate (not in `dregg-dfa`) so the core DFA crate stays
//! dependency-light: pulling `dregg-federation` into `dregg-dfa` would close a
//! `cell -> dfa -> federation -> captp -> cell` dependency cycle, which would
//! block `dregg-cell` from depending on `dregg-dfa` for the real `Dfa` predicate
//! verifier. Apps that need governance-bound DFA swaps depend on THIS crate.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_dfa::{RouteTableBuilder, RouteTarget};
//! use dregg_dfa_federation::governed_router_with_committee;
//! use dregg_federation::threshold::FederationCommittee;
//!
//! let committee: FederationCommittee = /* loaded from federation state */;
//! let table = RouteTableBuilder::new()
//!     .route("/x/*", RouteTarget::handler("xh"))
//!     .compile();
//! let router = governed_router_with_committee(table, committee);
//! // `router.update_routes(new_table, &proof)` now REQUIRES `proof.proof_data`
//! // to be a valid `ThresholdQC` over `old_commitment || new_commitment`.
//! ```
//!
//! # Wire-format
//!
//! `GovernanceProof::proof_data` is a postcard-encoded
//! `dregg_federation::threshold::ThresholdQC`. The verifier reconstructs the
//! QC, builds the canonical signing message `old_commitment || new_commitment`,
//! and delegates to `FederationCommittee::verify(&qc, &message)`.

use std::fmt;
use std::sync::Arc;

use dregg_dfa::{GovernedRouter, RouteTable, ThresholdVerifier};
use dregg_federation::threshold::{FederationCommittee, ThresholdQC};

/// A `ThresholdVerifier` that delegates to `FederationCommittee::verify`.
///
/// `proof_data` is interpreted as a postcard-encoded [`ThresholdQC`]; the
/// signed message is the concatenation `old_commitment || new_commitment`.
pub struct FederationQcVerifier {
    committee: FederationCommittee,
}

impl FederationQcVerifier {
    pub fn new(committee: FederationCommittee) -> Self {
        Self { committee }
    }

    pub fn committee(&self) -> &FederationCommittee {
        &self.committee
    }

    /// The canonical signing message: `old || new`.
    pub fn signing_message(old_commitment: &[u8; 32], new_commitment: &[u8; 32]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(old_commitment);
        buf[32..].copy_from_slice(new_commitment);
        buf
    }
}

impl fmt::Debug for FederationQcVerifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FederationQcVerifier")
            .finish_non_exhaustive()
    }
}

impl ThresholdVerifier for FederationQcVerifier {
    fn verify(
        &self,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        proof_data: &[u8],
    ) -> Result<(), String> {
        let qc: ThresholdQC = postcard::from_bytes(proof_data)
            .map_err(|e| format!("ThresholdQC decode failed: {e}"))?;
        let message = Self::signing_message(old_commitment, new_commitment);
        self.committee
            .verify(&qc, &message)
            .map_err(|e| format!("ThresholdQC verification failed: {e}"))
    }
}

/// Build a [`GovernedRouter`] whose table swaps are gated by the **real**
/// `dregg-federation` threshold-signature verifier ([`FederationQcVerifier`]).
///
/// This is the production constructor: a `GovernanceProof::proof_data` must be
/// a postcard-encoded `ThresholdQC` carrying a valid weighted threshold of
/// committee signatures over `old_commitment || new_commitment`, or
/// `GovernedRouter::update_routes` rejects the swap with
/// `RouteUpdateError::ThresholdVerificationFailed`. Unlike
/// `GovernedRouter::new` (which installs the CAS-only `StubVerifier`), there is
/// no path here by which a CAS-correct-but-unsigned swap is accepted.
pub fn governed_router_with_committee(
    table: RouteTable,
    committee: FederationCommittee,
) -> GovernedRouter {
    let verifier = Arc::new(FederationQcVerifier::new(committee));
    GovernedRouter::with_verifier(table, verifier)
}

// ---------------------------------------------------------------------------
// Tests — the governance threshold gate
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use dregg_dfa::{GovernanceProof, RouteTableBuilder, RouteTarget, RouteUpdateError};
    use dregg_federation::threshold::{
        FederationCommittee, MemberSecret, PartialSignature, generate_test_committee,
        generate_test_committee_with_seed,
    };

    use super::*;

    /// Sign `old ‖ new` with a threshold of committee members and encode the
    /// QC the way `FederationQcVerifier::verify` expects it on the wire.
    fn sign_swap(
        committee: &FederationCommittee,
        members: &[MemberSecret],
        signer_count: usize,
        old: &[u8; 32],
        new: &[u8; 32],
    ) -> Vec<u8> {
        let message = FederationQcVerifier::signing_message(old, new);
        let shares: Vec<(usize, PartialSignature)> = members[..signer_count]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &message)))
            .collect();
        let qc = committee
            .aggregate(&shares, &message)
            .expect("aggregate above threshold");
        postcard::to_allocvec(&qc).expect("QC postcard encode")
    }

    /// THE BAR: a route-table swap REQUIRES a valid `ThresholdQC` over
    /// `old ‖ new`. A valid threshold-signed swap commits; an unsigned /
    /// CAS-only / forged-threshold swap is REJECTED.
    #[test]
    fn governance_swap_requires_real_threshold_signature() {
        // 4-member committee, threshold 3 (BFT: tolerates 1 fault).
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let t1 = RouteTableBuilder::new()
            .route("/a/*", RouteTarget::handler("a1"))
            .compile();
        let mut governed = governed_router_with_committee(t1.clone(), committee.clone());

        let t2 = RouteTableBuilder::new()
            .route("/a/*", RouteTarget::handler("a2"))
            .compile();

        // (1) CAS-only / no real signature: a non-empty garbage blob that
        // would have passed the old `StubVerifier` is now REJECTED because it
        // is not a valid `ThresholdQC` over `old ‖ new`.
        let cas_only = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: vec![1, 2, 3],
        };
        assert!(
            matches!(
                governed.update_routes(t2.clone(), &cas_only),
                Err(RouteUpdateError::ThresholdVerificationFailed(_))
            ),
            "a CAS-only swap with no threshold signature must be rejected"
        );

        // (2) Forged threshold: a QC genuinely signed by a DIFFERENT committee
        // (the attacker's own keys) must NOT verify against the real committee.
        let (rogue, rogue_members) = generate_test_committee_with_seed(4, 3, [9u8; 32]).unwrap();
        let forged = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: sign_swap(&rogue, &rogue_members, 3, &t1.commitment, &t2.commitment),
        };
        assert!(
            matches!(
                governed.update_routes(t2.clone(), &forged),
                Err(RouteUpdateError::ThresholdVerificationFailed(_))
            ),
            "a swap signed by a rogue committee must be rejected"
        );

        // (3) Right committee but WRONG message (signs old‖old, not old‖new):
        // the signature is valid but over the wrong transition → rejected.
        let wrong_msg = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: sign_swap(&committee, &members, 3, &t1.commitment, &t1.commitment),
        };
        assert!(
            matches!(
                governed.update_routes(t2.clone(), &wrong_msg),
                Err(RouteUpdateError::ThresholdVerificationFailed(_))
            ),
            "a threshold sig over the wrong (old‖old) message must be rejected"
        );

        // (4) Valid threshold signature over `old ‖ new` → swap COMMITS.
        let good = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: sign_swap(&committee, &members, 3, &t1.commitment, &t2.commitment),
        };
        governed
            .update_routes(t2.clone(), &good)
            .expect("a valid threshold-signed swap must commit");

        // The swap actually took effect.
        let c = governed.classify_path(b"/a/x").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("a2"));

        // (5) Replaying the now-stale proof fails CAS (old commitment moved).
        let replay = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: sign_swap(&committee, &members, 3, &t1.commitment, &t2.commitment),
        };
        assert!(matches!(
            governed.update_routes(t2, &replay),
            Err(RouteUpdateError::CommitmentMismatch { .. })
        ));
    }

    /// `governed_router_with_committee` is sound by default: it never installs
    /// the CAS-only `StubVerifier`.
    #[test]
    fn federation_committee_constructor_rejects_empty_proof() {
        let (committee, _members) = generate_test_committee(4, 3).unwrap();
        let t1 = RouteTableBuilder::new()
            .route("/x/*", RouteTarget::handler("x"))
            .compile();
        let mut governed = governed_router_with_committee(t1.clone(), committee);
        let t2 = RouteTableBuilder::new()
            .route("/x/*", RouteTarget::handler("y"))
            .compile();
        let empty = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: vec![],
        };
        assert!(matches!(
            governed.update_routes(t2, &empty),
            Err(RouteUpdateError::ThresholdVerificationFailed(_))
        ));
    }
}
