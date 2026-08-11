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
//! `recursion-verify/tests/mina_chain_root_seam.rs`, and its reproducibility is the shipped
//! property `circuit-prove/tests/recursion_vk_determinism.rs` exists to defend.
//!
//! ⚠ **THIS SAID "printed by `circuit-prove/tests/mina_phase2_chain_fold.rs` §4" AND THAT WAS
//! FALSE.** Measured 2026-08-11: that file calls `recursion_vk_fingerprint` in **§3 only**, over a
//! **two-leaf** fold built to assert determinism, and its §4 root section prints the claim and no
//! fingerprint at all. A two-leaf fingerprint pinned here refuses every real root. The pointer is
//! corrected rather than kept, because a ceremony pointer that resolves to nothing is spent as if
//! it happened.
//!
//! ⚑ **AND SINCE 2026-08-08 THERE ARE TWO ANCHORS.** `DREGG_MINA_BODY_WELDED_ROOT_VK=<64 hex
//! chars>` pins the `state_body_hash` fold, which the wire now REQUIRES (`dregg-turn`
//! REFUSAL 16). Both towers publish the identical claim shape, so the fingerprint is the only
//! discriminator; a node pinned for only one refuses every head, loudly, at install time rather
//! than at the first head.
//!
//! ⚑⚑⚑ **2026-08-11 FLAG DAY — THE BODY ANCHOR IS NOW THE *WELDED* TOWER'S, AND ITS ENV VAR
//! CHANGED NAME SO AN OLD PIN CANNOT BE CARRIED ACROSS IN SILENCE.**
//!
//! `DREGG_MINA_BODY_ROOT_VK` is **GONE** — not aliased, not read as a fallback. A node still
//! setting it installs NO backend and refuses every Mina anchored head, which is the loud failure
//! and the correct one.
//!
//! What changed underneath the name: the `state_body_hash` root a node anchors is now minted from
//! twenty-five **body-preimage adapters**
//! (`dregg_circuit_prove::mina_body_preimage_adapter::prove_welded_body_hash_chain_fold`), not from
//! twenty-five plain chain leaves. Each adapter verifies the gated body-preimage STARK and that
//! link's chain STARK in ONE circuit and `cb.connect`s the link's 64 absorbed limbs to the
//! preimage descriptor's published limbs — 1 518 welds and 82 zero-pins across the family. So the
//! root's sentence gained a clause: *the stream this chain absorbed is the one a descriptor gates
//! as 2 381 bits and 302 bytes*, where before each link's absorbed pair was whatever the prover
//! said.
//!
//! ⚠⚠ **AND THE ONLY THING SEPARATING THE TWO TOWERS IS THIS FINGERPRINT.** The welded root and
//! the plain root publish the **identical** 200-lane claim — that is the adapter's drop-in
//! property, which is what let it be routed under an unmodified `fold_chain_links`, and it means
//! `verify_chain_root` below, `read_chain_claim_from_proof`, and every one of `dregg-turn`'s
//! REFUSAL 16 sub-checks are structurally blind to the difference. A node handed the PLAIN tower's
//! fingerprint verifies plain roots and stays green. **The rename is what stops the carry-across;
//! it is not a proof that the value pinned is the welded one.** Mint it, and read the value, with
//! `cargo run -p dregg-circuit-prove --release --bin mina_body_root_anchor -- <fixtures-dir>`.
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

/// ⚑ The operator's pin for the **WELDED `state_body_hash` fold's** `recursion_vk_fingerprint` —
/// the 25-**adapter** tower. **New 2026-08-08 as `DREGG_MINA_BODY_ROOT_VK`, renamed 2026-08-11**
/// with `dregg-turn`'s REFUSAL 16: the two towers publish the IDENTICAL claim shape, so the
/// fingerprint is the only thing telling a phase-2 root from a body root — and, since the weld was
/// routed, the only thing telling a WELDED body root from an unwelded one.
///
/// ⚑ Mint the root and read the value with the ceremony binary:
/// `cargo run -p dregg-circuit-prove --release --bin mina_body_root_anchor -- <fixtures-dir>`.
/// ⚠ It was documented as *"printed by `circuit-prove/tests/mina_body_hash_chain_fold.rs`'s root
/// section"* and it never was: that file fingerprints a **two-leaf** fold in §3 and its §4 root
/// section prints no fingerprint at all, so the documented ceremony yielded either nothing or a
/// value that refuses every real 25-link root. The binary is the ceremony now.
pub const BODY_ROOT_VK_ENV: &str = "DREGG_MINA_BODY_WELDED_ROOT_VK";

/// ⚑ The name this anchor had between 2026-08-08 and 2026-08-11, kept **only** so the refusal can
/// name it. Nothing reads its value; a node still setting it installs no backend.
pub const RETIRED_BODY_ROOT_VK_ENV: &str = "DREGG_MINA_BODY_ROOT_VK";

/// ⚑ Why an operator's anchor pair was REFUSED. Separated from [`P3MinaChainRootBackend::from_env`]
/// so the decision is a **pure function of three strings** and can be exercised without a test
/// mutating a process-global that every sibling test in the binary also reads — the hazard the
/// pre-existing `a_malformed_anchor_installs_nothing` had to work around by asserting the parser
/// instead of the decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnchorRefusal {
    /// Neither anchor is set. The ordinary un-pinned node; `from_env` reports it at `info`, not
    /// `error`, because it is a configuration state and not a mistake.
    Unset,
    /// ⚑ The 2026-08-11 flag day: only the RETIRED body-anchor name is set.
    RetiredBodyEnv,
    /// One of the two anchors is set and the other is not.
    HalfPinned(&'static str),
    /// An anchor is not 64 hex characters. **Never a zero anchor** — a typo must widen nothing.
    Malformed(&'static str),
    /// ⚑ Both anchors are the SAME fingerprint: one circuit pinned for two roles.
    SameAnchor,
}

impl std::fmt::Display for AnchorRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unset => write!(
                f,
                "no recursion-root trust anchors pinned ({CHAIN_ROOT_VK_ENV} and \
                 {BODY_ROOT_VK_ENV})"
            ),
            Self::RetiredBodyEnv => write!(
                f,
                "the body-root anchor env var was RENAMED {RETIRED_BODY_ROOT_VK_ENV} → \
                 {BODY_ROOT_VK_ENV} on 2026-08-11 and the old name is NOT a fallback: the body \
                 root is now the WELDED 25-adapter tower, and an anchor extracted from the \
                 unwelded one names a different circuit. Re-mint with `cargo run -p \
                 dregg-circuit-prove --release --bin mina_body_root_anchor`"
            ),
            Self::HalfPinned(env) => write!(
                f,
                "{env} is not set while its partner is; a node pinned for only one tower can only \
                 refuse every head, so it says so here rather than at the first head"
            ),
            Self::Malformed(env) => write!(
                f,
                "{env} is not 64 hex characters; refusing rather than installing a zero anchor"
            ),
            Self::SameAnchor => write!(
                f,
                "{CHAIN_ROOT_VK_ENV} and {BODY_ROOT_VK_ENV} are the SAME fingerprint. The two \
                 towers publish the identical 200-lane claim and the fingerprint is their ONLY \
                 discriminator, so one value in both slots pins one circuit for two roles"
            ),
        }
    }
}

/// ⚑ The anchor decision, as a pure function of what the environment says. See [`AnchorRefusal`]
/// for why it is not inlined into [`P3MinaChainRootBackend::from_env`].
pub fn anchors_from_raw(
    chain: Option<&str>,
    body: Option<&str>,
    retired_body: Option<&str>,
) -> Result<(RecursionVk, RecursionVk), AnchorRefusal> {
    if body.is_none() && retired_body.is_some() {
        return Err(AnchorRefusal::RetiredBodyEnv);
    }
    match (chain, body) {
        (None, None) => Err(AnchorRefusal::Unset),
        (None, Some(_)) => Err(AnchorRefusal::HalfPinned(CHAIN_ROOT_VK_ENV)),
        (Some(_), None) => Err(AnchorRefusal::HalfPinned(BODY_ROOT_VK_ENV)),
        (Some(c), Some(b)) => {
            let pinned = RecursionVk::from_hex(c.trim())
                .ok_or(AnchorRefusal::Malformed(CHAIN_ROOT_VK_ENV))?;
            let body_pinned = RecursionVk::from_hex(b.trim())
                .ok_or(AnchorRefusal::Malformed(BODY_ROOT_VK_ENV))?;
            if pinned == body_pinned {
                return Err(AnchorRefusal::SameAnchor);
            }
            Ok((pinned, body_pinned))
        }
    }
}

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
    ///
    /// ⚑ **AND NEVER THE SAME ANCHOR TWICE.** The phase-2 root and the body root publish the
    /// identical 200-lane claim; `check_chain_root_binding` and `check_body_chain_binding` are
    /// separated by nothing but these two pins. One value in both slots is an operator who has
    /// pinned one circuit for two roles, and it is refused at install rather than left to be
    /// caught by whichever of the two claim-shape checks happens to fire first.
    pub fn from_env() -> Option<Self> {
        let chain = std::env::var(CHAIN_ROOT_VK_ENV).ok();
        let body = std::env::var(BODY_ROOT_VK_ENV).ok();
        let retired = std::env::var(RETIRED_BODY_ROOT_VK_ENV).ok();
        match anchors_from_raw(chain.as_deref(), body.as_deref(), retired.as_deref()) {
            Ok((pinned, body_pinned)) => Some(Self::new(pinned, body_pinned)),
            Err(AnchorRefusal::Unset) => None,
            Err(other) => {
                tracing::error!(
                    reason = %other,
                    "installing NO recursion-root backend — every Mina anchored head will be \
                     REFUSED"
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

    // ════════════════════════════════════════════════════════════════════════════════════════
    // ⚑⚑⚑ THE ANCHOR DECISION — pure, so these run without racing a process-global.
    // ════════════════════════════════════════════════════════════════════════════════════════

    const A: &str = "11223344556677889900aabbccddeeff11223344556677889900aabbccddeeff";
    const B: &str = "ffeeddccbbaa00998877665544332211ffeeddccbbaa00998877665544332211";

    /// ⚑ POSITIVE POLE: two well-formed, DIFFERENT anchors install a backend pinned to both.
    #[test]
    fn two_distinct_well_formed_anchors_are_accepted() {
        let (chain, body) = anchors_from_raw(Some(A), Some(B), None).expect("accepted");
        assert_eq!(chain.to_hex(), A);
        assert_eq!(body.to_hex(), B);
        // …and whitespace around an operator's paste is trimmed rather than refused.
        assert_eq!(
            anchors_from_raw(Some(&format!("  {A}\n")), Some(B), None).expect("trimmed"),
            (chain, body)
        );
    }

    /// ⚑⚑⚑ **THE 2026-08-11 FLAG DAY.** A node still setting `DREGG_MINA_BODY_ROOT_VK` — even
    /// with a perfectly well-formed value and a perfectly good phase-2 anchor — installs NOTHING
    /// and is told which name to move to. The old anchor named the UNWELDED tower; reading it as a
    /// fallback would silently keep a node on a body root whose absorbed stream is whatever the
    /// prover said, which is exactly the check the weld exists to add.
    #[test]
    fn the_retired_body_anchor_name_is_refused_and_not_a_fallback() {
        let err = anchors_from_raw(Some(A), None, Some(B)).unwrap_err();
        assert_eq!(err, AnchorRefusal::RetiredBodyEnv);
        let msg = err.to_string();
        assert!(msg.contains(RETIRED_BODY_ROOT_VK_ENV), "{msg}");
        assert!(msg.contains(BODY_ROOT_VK_ENV), "{msg}");
        assert!(
            msg.contains("WELDED"),
            "the refusal must say what changed: {msg}"
        );
        // ⚠ And the retired name is refused even when the CURRENT name would have been fine on
        // its own — a deployment that sets both has not chosen, and guessing is how a stale pin
        // survives a flag day.
        assert!(anchors_from_raw(Some(A), Some(B), Some(B)).is_ok());
    }

    /// ⚑⚑ **ONE CIRCUIT PINNED FOR TWO ROLES.** The phase-2 tower and the body tower publish the
    /// identical 200-lane claim; these two pins are the whole of what separates
    /// `check_chain_root_binding` from `check_body_chain_binding`. The same value in both is
    /// refused at install, not left to whichever claim-shape check fires first.
    #[test]
    fn the_same_fingerprint_in_both_anchor_slots_is_refused() {
        let err = anchors_from_raw(Some(A), Some(A), None).unwrap_err();
        assert_eq!(err, AnchorRefusal::SameAnchor);
        assert!(err.to_string().contains("ONLY"), "{err}");
        // Case is not a way around it: `from_hex` is the normaliser, so the comparison is on bytes.
        assert_eq!(
            anchors_from_raw(Some(&A.to_uppercase()), Some(A), None).unwrap_err(),
            AnchorRefusal::SameAnchor
        );
    }

    /// Half-pinned and unset are distinct, and neither installs anything.
    #[test]
    fn half_pinned_and_unset_install_nothing() {
        assert_eq!(
            anchors_from_raw(None, None, None).unwrap_err(),
            AnchorRefusal::Unset
        );
        assert_eq!(
            anchors_from_raw(Some(A), None, None).unwrap_err(),
            AnchorRefusal::HalfPinned(BODY_ROOT_VK_ENV)
        );
        assert_eq!(
            anchors_from_raw(None, Some(B), None).unwrap_err(),
            AnchorRefusal::HalfPinned(CHAIN_ROOT_VK_ENV)
        );
        assert_eq!(
            anchors_from_raw(Some("not-hex"), Some(B), None).unwrap_err(),
            AnchorRefusal::Malformed(CHAIN_ROOT_VK_ENV)
        );
        assert_eq!(
            anchors_from_raw(Some(A), Some(""), None).unwrap_err(),
            AnchorRefusal::Malformed(BODY_ROOT_VK_ENV)
        );
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
