//! Derivation trace and verification.
//!
//! The derivation trace is a chain of cryptographic steps recording how a
//! token was derived from its original minted form to its current state.
//! Each step records:
//! - What action was taken (mint, attenuate, delegate)
//! - Which authority performed the action
//! - The input and output state roots
//! - A signature over the output root
//!
//! A verifier can check the entire trace to confirm:
//! 1. The chain is unbroken (each step's output is the next step's input)
//! 2. Each step was signed by a valid authority
//! 3. The final output matches the presented token's state root
//!
//! This enables cross-silo verification: partner.org can verify acme.corp's
//! token without contacting acme.corp, as long as it knows the federation
//! trust root.
//!
//! NOTE: The trace verification here uses Ed25519 signature checks (real crypto).
//! The STARK proof of issuer membership in `stark_proof.rs` uses `dregg_circuit::stark`
//! to generate a real zero-knowledge proof. A full integration would prove the
//! entire derivation trace in zero-knowledge using the circuit's `fold_air` and
//! `derivation_air` components.
//!
//! // TODO: integrate with real dregg_circuit::fold_air to prove each attenuation
//! // step in zero-knowledge (currently trace verification is done via direct
//! // Ed25519 signature checks, which is correct but not zero-knowledge).

use crate::authority::{PublicKey, hex_encode};
use crate::federation::Federation;

// =============================================================================
// Derivation Step
// =============================================================================

/// A single step in the derivation trace.
#[derive(Clone, Debug)]
pub struct DerivationStep {
    /// The authority that performed this step.
    pub authority: PublicKey,
    /// The state root before this step (zeroed for mint).
    pub input_root: [u8; 32],
    /// The state root after this step.
    pub output_root: [u8; 32],
    /// Ed25519 signature over the output root by the authority (64 bytes).
    pub signature: [u8; 64],
}

// =============================================================================
// Trace Verification
// =============================================================================

/// Result of verifying a derivation trace.
#[derive(Clone, Debug)]
pub struct TraceVerificationResult {
    /// Whether the trace is valid.
    pub valid: bool,
    /// Number of steps verified.
    pub steps_verified: usize,
    /// If invalid, the reason why.
    pub failure_reason: Option<String>,
}

/// Verify a complete derivation trace.
///
/// This checks:
/// 1. Chain continuity: each step's output_root == next step's input_root
/// 2. Signature validity: each step's signature was produced by a federation member
/// 3. Final state: the last step's output_root matches the expected state root
///
/// This is the core of cross-silo verification: the verifier only needs
/// the federation registry (containing public keys) and the presented trace.
pub fn verify_trace(
    trace: &[DerivationStep],
    expected_final_root: &[u8; 32],
    federation: &Federation,
) -> TraceVerificationResult {
    if trace.is_empty() {
        return TraceVerificationResult {
            valid: false,
            steps_verified: 0,
            failure_reason: Some("empty derivation trace".to_string()),
        };
    }

    for (i, step) in trace.iter().enumerate() {
        // Check chain continuity (skip for first step which has no predecessor).
        if i > 0 {
            let prev = &trace[i - 1];
            if prev.output_root != step.input_root {
                return TraceVerificationResult {
                    valid: false,
                    steps_verified: i,
                    failure_reason: Some(format!(
                        "chain break at step {}: prev output {} != step input {}",
                        i,
                        hex_encode(&prev.output_root[..4]),
                        hex_encode(&step.input_root[..4]),
                    )),
                };
            }
        }

        // Check that the authority is a federation member.
        if !federation.is_member(&step.authority) {
            return TraceVerificationResult {
                valid: false,
                steps_verified: i,
                failure_reason: Some(format!(
                    "step {} authority {} is not a federation member",
                    i,
                    step.authority.short_hex(),
                )),
            };
        }

        // Verify the signature.
        let vk = federation.get_verification_key(&step.authority);
        match vk {
            Some(vk) => {
                if !vk.verify(&step.output_root, &step.signature) {
                    return TraceVerificationResult {
                        valid: false,
                        steps_verified: i,
                        failure_reason: Some(format!(
                            "step {} signature verification failed (authority: {})",
                            i,
                            step.authority.short_hex(),
                        )),
                    };
                }
            }
            None => {
                return TraceVerificationResult {
                    valid: false,
                    steps_verified: i,
                    failure_reason: Some(format!(
                        "step {} no verification key for authority {}",
                        i,
                        step.authority.short_hex(),
                    )),
                };
            }
        }
    }

    // Check the final state root matches.
    let last_output = &trace.last().unwrap().output_root;
    if last_output != expected_final_root {
        return TraceVerificationResult {
            valid: false,
            steps_verified: trace.len(),
            failure_reason: Some(format!(
                "final state root mismatch: trace ends at {}, expected {}",
                hex_encode(&last_output[..4]),
                hex_encode(&expected_final_root[..4]),
            )),
        };
    }

    TraceVerificationResult {
        valid: true,
        steps_verified: trace.len(),
        failure_reason: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authority::Authority;
    use crate::federation::FederationRole;
    use crate::token::{Fact, Rule};

    fn setup_federation() -> (Authority, Authority, Federation) {
        let auth1 = Authority::new("acme.corp");
        let auth2 = Authority::new("partner.org");
        let mut fed = Federation::new("test-federation");
        fed.add_member(
            "acme.corp",
            &auth1,
            vec![FederationRole::Issuer, FederationRole::Verifier],
        );
        fed.add_member("partner.org", &auth2, vec![FederationRole::Verifier]);
        fed.compute_root();
        (auth1, auth2, fed)
    }

    #[test]
    fn test_verify_simple_trace() {
        let (auth1, _auth2, fed) = setup_federation();
        let facts = vec![Fact::app("frontend", "rw")];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth1.mint_token(facts, rules);

        let result = verify_trace(&token.derivation_trace, &token.state_root, &fed);
        assert!(result.valid);
        assert_eq!(result.steps_verified, 1);
    }

    #[test]
    fn test_verify_attenuated_trace() {
        let (auth1, _auth2, fed) = setup_federation();
        let facts = vec![Fact::app("frontend", "rw"), Fact::app("backend", "rw")];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth1.mint_token(facts, rules);

        let remove = vec![Fact::app("backend", "rw")];
        let checks = vec![crate::token::Check::read_only()];
        let attenuated = token.attenuate(&remove, checks, &auth1);

        let result = verify_trace(&attenuated.derivation_trace, &attenuated.state_root, &fed);
        assert!(result.valid);
        assert_eq!(result.steps_verified, 2);
    }

    #[test]
    fn test_verify_trace_non_member() {
        let (auth1, _auth2, fed) = setup_federation();
        let outsider = Authority::new("outsider.org");

        let facts = vec![Fact::app("frontend", "rw")];
        let rules = vec![Rule::allow_app()];
        let token = auth1.mint_token(facts, rules);

        // Attenuate with a non-member authority.
        let attenuated = token.attenuate(&[], vec![], &outsider);

        let result = verify_trace(&attenuated.derivation_trace, &attenuated.state_root, &fed);
        assert!(!result.valid);
        assert!(
            result
                .failure_reason
                .unwrap()
                .contains("not a federation member")
        );
    }
}
