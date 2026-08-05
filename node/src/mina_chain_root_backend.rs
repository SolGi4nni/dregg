//! ⚑⚑ **THE NODE'S RECURSION-ROOT VERIFIER — where the capability actually enters.**
//!
//! `dregg-turn` defines the seam ([`dregg_turn::executor::MinaChainRootBackend`]) and refuses
//! every Mina anchored head while nothing is injected. This module is the injection: a
//! ~50-line adapter over `dregg-recursion-verify`, the crate that **unconditionally** verifies a
//! recursion root.
//!
//! # Why this is a crate edge and not a cargo feature
//!
//! Because the boundary should be visible in `cargo tree`. A `#[cfg(feature = "recursion")]`
//! would put the same code behind a flag that is on in one resolve and off in another, and the
//! difference between "this node can verify a fold root" and "this node cannot" would be a
//! feature-unification outcome rather than a dependency. The node takes the edge; `dregg-turn`
//! does not; and a consumer that takes neither gets a REFUSAL, not a skip.
//!
//! # ⚑ THE ANCHOR, AND WHY ITS ABSENCE IS ALSO A REFUSAL
//!
//! A recursion root has no descriptor to name — its identity is the
//! `recursion_vk_fingerprint` of the PROOF, extracted once from an honest fold by a setup party
//! and shipped. So the node must be TOLD which fingerprint it trusts. If the operator has not
//! said, this module installs **nothing**, and `dregg-turn`'s refusal 0 fires. There is
//! deliberately no default anchor: a default would be a fingerprint nobody chose, compared
//! against roots nobody vouched for.
//!
//! Set it with `DREGG_MINA_CHAIN_ROOT_VK=<64 hex chars>`. The value is printed by
//! `circuit-prove/tests/mina_phase2_chain_fold.rs` §4 (`recursion_vk_fingerprint` of an honest
//! fold), and its reproducibility is the shipped property
//! `circuit-prove/tests/recursion_vk_determinism.rs` exists to defend.

use std::sync::Arc;

use dregg_recursion_verify::chain_root::{chain_root_config, read_chain_claim_from_proof};
use dregg_recursion_verify::verify::{
    RecursionVk, decode_recursive_batch_proof, recursion_vk_fingerprint,
    verify_recursive_batch_proof_with_config,
};
use dregg_turn::executor::{MinaChainRootBackend, MinaChainRootClaim};

/// The operator's pin for the trusted `recursion_vk_fingerprint`, as 64 lowercase hex chars.
pub const CHAIN_ROOT_VK_ENV: &str = "DREGG_MINA_CHAIN_ROOT_VK";

/// The real backend: decode → fingerprint → verify → read claim.
///
/// ⚑ It does **not** decide whether the fingerprint is acceptable. It reports what it measured,
/// and `dregg-turn`'s [`dregg_turn::executor::check_chain_root_binding`] requires it to equal
/// [`Self::pinned`]. A backend that forgot to compare therefore cannot fail open — the
/// comparison is structurally out of its hands.
#[derive(Debug, Clone, Copy)]
pub struct P3MinaChainRootBackend {
    pinned: RecursionVk,
}

impl P3MinaChainRootBackend {
    /// Build a backend pinned to `vk`.
    pub fn new(pinned: RecursionVk) -> Self {
        Self { pinned }
    }

    /// Read the operator's pinned anchor from [`CHAIN_ROOT_VK_ENV`].
    ///
    /// `None` when unset, and `None` — **not a zero anchor** — when malformed: an operator typo
    /// must widen nothing. The caller installs no backend in either case, so the head stays
    /// refused.
    pub fn from_env() -> Option<Self> {
        let raw = std::env::var(CHAIN_ROOT_VK_ENV).ok()?;
        let trimmed = raw.trim();
        match RecursionVk::from_hex(trimmed) {
            Some(vk) => Some(Self::new(vk)),
            None => {
                tracing::error!(
                    env = CHAIN_ROOT_VK_ENV,
                    "recursion-root trust anchor is not 64 hex characters; installing NO \
                     recursion-root backend — every Mina anchored head will be REFUSED"
                );
                None
            }
        }
    }
}

impl MinaChainRootBackend for P3MinaChainRootBackend {
    fn pinned_root_vk(&self) -> [u8; 32] {
        self.pinned.0
    }

    fn verify_chain_root(
        &self,
        proof_bytes: &[u8],
    ) -> Result<([u8; 32], MinaChainRootClaim), String> {
        let proof = decode_recursive_batch_proof(proof_bytes)?;
        let measured = recursion_vk_fingerprint(&proof);
        // ⚑ THE CONFIG IS NOT A CHOICE HERE. The IR-v2 chain leaf/fold tower runs at
        // `ir2_leaf_wrap_config` (inner FRI log_blowup 6); verifying a root under the default
        // recursion knobs simply fails, which is honest but confusing, so the config comes from
        // the same crate that defines the fold's claim layout.
        verify_recursive_batch_proof_with_config(&proof, &chain_root_config())?;
        let claim = read_chain_claim_from_proof(&proof).ok_or_else(|| {
            "the recursion root verifies but publishes no Mina phase-2 chain claim".to_string()
        })?;
        Ok((
            measured.0,
            MinaChainRootClaim {
                in_state: claim.in_state.iter().map(|v| v.as_u32()).collect(),
                out_state: claim.out_state.iter().map(|v| v.as_u32()).collect(),
                transcript_acc: claim.transcript_acc.iter().map(|v| v.as_u32()).collect(),
            },
        ))
    }
}

/// Install the recursion-root backend into `registry` **iff** the operator pinned an anchor.
///
/// Returns `true` when the node gained the capability. `false` is not a failure and not a
/// warning-and-carry-on: it means every Mina anchored head this node sees will be REFUSED at
/// `dregg-turn`'s refusal 0, which is the correct behaviour for a node that has not been told
/// which fold circuit it trusts.
pub fn install_mina_chain_root_backend(
    registry: &mut dregg_cell::predicate::WitnessedPredicateRegistry,
) -> bool {
    let Some(backend) = P3MinaChainRootBackend::from_env() else {
        tracing::info!(
            env = CHAIN_ROOT_VK_ENV,
            "no recursion-root trust anchor pinned; Mina anchored-head predicates will be \
             REFUSED (fail-closed)"
        );
        return false;
    };
    tracing::info!(
        anchor = %backend.pinned.to_hex(),
        "recursion-root backend installed; Mina anchored heads will be checked against this \
         RecursionVk fingerprint"
    );
    dregg_turn::executor::register_mina_head_verifier_with_chain_root(registry, Arc::new(backend));
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::predicate::{
        PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    };

    /// ⚑⚑⚑ **THE ABSENT CASE, REFUSED — at the node's own registry.**
    ///
    /// Build the registry the way the node does but WITHOUT installing the backend, then present
    /// a head. The verifier resolves (so this is not a `KindNotRegistered` accident) and REJECTS,
    /// naming the missing capability. A node that cannot verify a recursion root refuses the
    /// head; it does not log and proceed.
    #[test]
    fn a_node_with_no_backend_refuses_a_mina_head() {
        let reg = dregg_turn::executor::registry_with_real_verifiers();
        let v = reg
            .get(WitnessedPredicateKind::Custom {
                vk_hash: dregg_turn::executor::mina_head_predicate_vk(),
            })
            .expect("the Mina head vk RESOLVES — the refusal below is the verifier's, not a miss");
        let err = v
            .verify(&[7u8; 32], &PredicateInput::Slot(&[3u8; 32]), &[0u8; 8])
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => assert!(
                reason.contains("no recursion-root backend is injected"),
                "the refusal must NAME the absent capability, got: {reason}"
            ),
            other => panic!("expected a fail-closed rejection, got {other:?}"),
        }
    }

    /// ⚑ And the installed case is a DIFFERENT verifier under the SAME vk — the upgrade is in
    /// place, so a cell program written against an unwired node keeps its predicate identity.
    #[test]
    fn installing_the_backend_upgrades_in_place() {
        let mut reg = dregg_turn::executor::registry_with_real_verifiers();
        dregg_turn::executor::register_mina_head_verifier_with_chain_root(
            &mut reg,
            Arc::new(P3MinaChainRootBackend::new(RecursionVk([9u8; 32]))),
        );
        let v = reg
            .get(WitnessedPredicateKind::Custom {
                vk_hash: dregg_turn::executor::mina_head_predicate_vk(),
            })
            .expect("still resolves");
        // A garbage blob now reaches the WIRE, not refusal 0 — the capability is present.
        let err = v
            .verify(&[7u8; 32], &PredicateInput::Slot(&[3u8; 32]), &[0xAAu8; 64])
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => assert!(
                reason.contains("did not decode"),
                "a wired node must get past refusal 0, got: {reason}"
            ),
            other => panic!("expected a wire rejection, got {other:?}"),
        }
    }

    /// A malformed anchor yields NO backend rather than a zero one. The registry is untouched, so
    /// the node stays refusing — a typo must never widen.
    #[test]
    fn a_malformed_anchor_installs_nothing() {
        let mut reg = WitnessedPredicateRegistry::empty();
        // SAFETY-of-test: `from_env` reads a process-global, so this test asserts the PARSER
        // rather than mutating the environment (which would race every other test in the binary).
        assert!(RecursionVk::from_hex("not-hex").is_none());
        assert!(RecursionVk::from_hex("").is_none());
        assert!(
            !install_mina_chain_root_backend(&mut reg) || std::env::var(CHAIN_ROOT_VK_ENV).is_ok()
        );
    }
}
