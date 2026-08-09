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
//! fold) and by `recursion-verify/tests/mina_chain_root_seam.rs` §2, and its reproducibility is
//! the shipped property `circuit-prove/tests/recursion_vk_determinism.rs` exists to defend.
//!
//! ⚑ **AND SINCE 2026-08-08 THERE ARE TWO ANCHORS.** `DREGG_MINA_BODY_ROOT_VK=<64 hex chars>`
//! pins the `state_body_hash` fold (`mina_body_hash_chain_fold`'s 25-leaf tower), which the wire
//! now REQUIRES (`dregg-turn` REFUSAL 16). Both towers publish the identical claim shape, so the
//! fingerprint is the only discriminator; a node pinned for only one refuses every head, loudly,
//! at install time rather than at the first head.
//!
//! ⚑⚑ **IT ROTATED ON 2026-08-08 AND IT WILL ROTATE AGAIN.** The phase-2 chain tower was switched
//! to the two-engine shape every other recursion tower already ran at: a leaf now VERIFIES its
//! IR-v2 child at the descriptor engine and MINTS at the recursion engine (`log_blowup 3, 38
//! queries`), so the fold circuit that verifies a 38-query child is a **different circuit** and its
//! `recursion_vk_fingerprint` is a different value. There is nothing in this repo to re-emit — the
//! anchor has no checked-in default, by the design above — but **an operator running a pin from
//! before that date will have every Mina anchored head REFUSED**, which is the correct failure and
//! not a silent one. Re-extract from an honest fold and re-pin.

use std::sync::Arc;

use dregg_recursion_verify::chain_root::{chain_root_config, read_chain_claim_from_proof};
use dregg_recursion_verify::verify::{
    RecursionVk, decode_recursive_batch_proof, recursion_vk_fingerprint,
    verify_recursive_batch_proof_with_config,
};
use dregg_turn::executor::{MinaChainRootBackend, MinaChainRootClaim};

/// The operator's pin for the trusted `recursion_vk_fingerprint`, as 64 lowercase hex chars.
pub const CHAIN_ROOT_VK_ENV: &str = "DREGG_MINA_CHAIN_ROOT_VK";

/// ⚑ The operator's pin for the **`state_body_hash` fold's** `recursion_vk_fingerprint` — the
/// 25-leaf tower of `mina_body_hash_chain_fold`. **New 2026-08-08**, with `dregg-turn`'s
/// REFUSAL 16: the two towers publish the IDENTICAL claim shape, so the fingerprint is the only
/// thing telling a phase-2 root from a body root, and one env var cannot anchor both. The value
/// is printed by `circuit-prove/tests/mina_body_hash_chain_fold.rs`'s root section, same
/// extraction ceremony as [`CHAIN_ROOT_VK_ENV`]'s.
pub const BODY_ROOT_VK_ENV: &str = "DREGG_MINA_BODY_ROOT_VK";

/// The real backend: decode → fingerprint → verify → read claim.
///
/// ⚑ It does **not** decide whether the fingerprint is acceptable. It reports what it measured,
/// and `dregg-turn`'s [`dregg_turn::executor::check_chain_root_binding`] /
/// `check_body_chain_binding` require it to equal the matching pin. A backend that forgot to
/// compare therefore cannot fail open — the comparison is structurally out of its hands.
#[derive(Debug, Clone, Copy)]
pub struct P3MinaChainRootBackend {
    pinned: RecursionVk,
    body_pinned: RecursionVk,
}

impl P3MinaChainRootBackend {
    /// Build a backend pinned to the phase-2 fold's `vk` and the body fold's `body_vk`.
    pub fn new(pinned: RecursionVk, body_pinned: RecursionVk) -> Self {
        Self {
            pinned,
            body_pinned,
        }
    }

    /// Read the operator's pinned anchors from [`CHAIN_ROOT_VK_ENV`] and [`BODY_ROOT_VK_ENV`].
    ///
    /// `None` unless BOTH are set and well-formed — **never a zero anchor** for either: an
    /// operator typo must widen nothing, and since the 2026-08-08 wire flag day a head cannot
    /// verify without a body root, so a node pinned for only one tower can only refuse anyway
    /// and says so here rather than at the first head.
    pub fn from_env() -> Option<Self> {
        let read = |env: &'static str| -> Option<RecursionVk> {
            let raw = std::env::var(env).ok()?;
            match RecursionVk::from_hex(raw.trim()) {
                Some(vk) => Some(vk),
                None => {
                    tracing::error!(
                        env,
                        "recursion-root trust anchor is not 64 hex characters; installing NO \
                         recursion-root backend — every Mina anchored head will be REFUSED"
                    );
                    None
                }
            }
        };
        let pinned = read(CHAIN_ROOT_VK_ENV)?;
        let body_pinned = read(BODY_ROOT_VK_ENV)?;
        Some(Self::new(pinned, body_pinned))
    }
}

impl MinaChainRootBackend for P3MinaChainRootBackend {
    fn pinned_root_vk(&self) -> [u8; 32] {
        self.pinned.0
    }

    fn pinned_body_root_vk(&self) -> [u8; 32] {
        self.body_pinned.0
    }

    fn verify_chain_root(
        &self,
        proof_bytes: &[u8],
    ) -> Result<([u8; 32], MinaChainRootClaim), String> {
        let proof = decode_recursive_batch_proof(proof_bytes)?;
        let measured = recursion_vk_fingerprint(&proof);
        // ⚑ THE CONFIG IS NOT A CHOICE HERE, AND IT IS DELEGATED RATHER THAN NAMED. A chain root
        // is minted at `recursion_layer_over`'s fixed point — since 2026-08-08, `log_blowup 3 /
        // 38 queries`, where until then the whole tower ran at its child's `log_blowup 6 / 19`.
        // Taking the accessor from the crate that also defines the fold's claim layout is what
        // made that rotation reach this node without an edit here; naming a config would not have.
        // ⚠ The operator's pinned `DREGG_MINA_CHAIN_ROOT_VK` DID have to be re-extracted: the root
        // is a different circuit, and an anchor from before the rotation refuses every root now.
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
            chain_env = CHAIN_ROOT_VK_ENV,
            body_env = BODY_ROOT_VK_ENV,
            "recursion-root trust anchors not (both) pinned; Mina anchored-head predicates will \
             be REFUSED (fail-closed)"
        );
        return false;
    };
    tracing::info!(
        anchor = %backend.pinned.to_hex(),
        body_anchor = %backend.body_pinned.to_hex(),
        "recursion-root backend installed; Mina anchored heads will be checked against these \
         RecursionVk fingerprints"
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
            Arc::new(P3MinaChainRootBackend::new(
                RecursionVk([9u8; 32]),
                RecursionVk([8u8; 32]),
            )),
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
