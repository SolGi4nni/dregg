//! `dregg-federation`: Multi-node federated revocation attestation.
//!
//! Historically this crate hosted a Morpheus-shaped BFT consensus simulation;
//! the live consensus engine is now `dregg-blocklace` (Cordial Miners DAG +
//! tau ordering). What remains here are the federated revocation primitives
//! (Merkle accumulator, attested roots, quorum signatures) plus the solo /
//! threshold / checkpoint utilities the live node consumes.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Federation (N nodes)                          │
//! │                                                                  │
//! │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐      │
//! │  │  Node 0  │  │  Node 1  │  │  Node 2  │  │  Node 3  │      │
//! │  │          │  │          │  │          │  │          │      │
//! │  │ Merkle   │  │ Merkle   │  │ Merkle   │  │ Merkle   │      │
//! │  │ Tree     │  │ Tree     │  │ Tree     │  │ Tree     │      │
//! │  │          │  │          │  │          │  │          │      │
//! │  │ Consensus│  │ Consensus│  │ Consensus│  │ Consensus│      │
//! │  │ State    │  │ State    │  │ State    │  │ State    │      │
//! │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘      │
//! │       │              │              │              │            │
//! │       └──────────────┴──────────────┴──────────────┘            │
//! │                         │                                        │
//! │              BFT Consensus (blocklace, see dregg-blocklace)      │
//! │              (Propose -> Vote -> Finalize)                       │
//! │                         │                                        │
//! │                    Attested Root                                  │
//! │              (merkle_root, height, quorum_sigs)                   │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # How it works
//!
//! 1. **Revocation submission**: An authority node creates a signed revocation
//!    event for a token ID.
//!
//! 2. **Consensus**: The BFT protocol (propose/vote/finalize, as implemented
//!    by `dregg-blocklace`) agrees on a block of revocations. A quorum (n - f)
//!    of nodes must vote for the block to be finalized.
//!
//! 3. **State update**: After finalization, all nodes apply the revocations
//!    to their local Merkle trees. Since the tree is deterministic and
//!    insertion-order-independent, all nodes converge on the same root.
//!
//! 4. **Attested root**: The resulting `(merkle_root, block_height, timestamp,
//!    quorum_signatures)` tuple is the attested root. Verifiers trust it
//!    because it has signatures from >= threshold federation members.
//!
//! 5. **Non-membership proofs**: A verifier checks that a token is NOT in
//!    the revocation tree by obtaining a non-membership proof against the
//!    attested root.
//!
//! # Modules
//!
//! - [`types`]: Core data types (AttestedRoot, RevocationProof, messages, crypto)
//! - [`revocation`]: Revocation Merkle tree + non-membership proofs
//! - [`node`]: Federation node implementation (includes BFT consensus simulation)

/// Strand admission — the HYBRID (stake-OR-vouch) Sybil-admission gate (closes red-team F-4).
/// The gate IN FRONT of participation/finalization: only admitted strands (seeds, ≥N
/// distinct-rooted-vouched, or ≥`min_bond` bonded) are finalizable; bonded equivocators are
/// slashed. Faithful mirror of the verified Lean `Dregg2.Distributed.StrandAdmission`.
pub mod admission;
/// Randomness beacon (ORGANS §6 weld): the UNIQUE threshold-BLS group signature over a
/// domain-separated `(epoch, height)` message, hashed into 32 bytes of unbiasable public
/// randomness — no member can steer it (uniqueness), no sub-threshold set can compute it early.
/// Includes the deterministic-draw / jury-selection consumer surface.
pub mod beacon;
/// Differential: the verified Lean `Dregg2.Distributed.BlsQuorumCert` model ⟺ this crate's real BLS
/// aggregate-verify. Pins `faultBudget`/`quorumThreshold` against `fault_tolerance`/`quorum_threshold`
/// (exhaustive `0..=512` sweep + `StrictBft ⇔ 3∤n`), and drives the REAL `hints` weighted-threshold
/// aggregation to witness the distributed claims: a corrupt-only set (`|B| ≤ f < quorum`) cannot
/// produce a verifying QC, an honest quorum does, and two quorums over the same committee overlap in
/// more than `f` members (so a shared honest signer exists — the no-equivocation backbone). Test-only.
#[cfg(test)]
mod bls_quorum_diff;
pub mod checkpoint;
/// Differential: the verified Lean `Dregg2.Distributed.CheckpointPrune` model ⟺ this crate's real
/// checkpoint-prune arc (the `RetentionPolicy::would_prune` predicate transcribed from
/// `node/src/config.rs`, the prune/recover keyset reconstruction, and the `Checkpoint::verify`
/// attestation gate driven through genuine Ed25519-signed QCs). Test-only.
#[cfg(test)]
mod checkpoint_prune_diff;
/// The adjudication court (ORGANS §5, CONSENSUS-FLEX §7 items 1–2): the witness-first
/// equivocation court — the `validEquivocation` predicate atom over the blocklace's wire
/// evidence value, the evidence→slash pipe into [`admission::AdmissionRegistry::slash`]
/// (no-double-resolve via burned evidence digests), and the beacon-seeded council
/// selection for the non-certifiable residue.
pub mod court;
pub mod cross_fed_bundle;
/// Distributed key generation (Feldman/JF-DKG) + proactive resharing for the
/// beacon committee — the upgrade `beacon`'s NOTES §1 names: share issuance
/// with NO party ever holding `f(0)`, plus same-`f(0)` resharing for
/// committee rotation. Outputs drop straight into [`beacon`]'s types
/// (`BeaconCommittee` / `BeaconShare`), so `beacon_at` / `verify_beacon`
/// work unchanged over DKG-derived keys. Round messages are transport-
/// agnostic serde structs (the ceremony-as-cell-app lane rides them later).
pub mod dkg;
/// The DKG **ceremony** — the transport + agreement layer over [`dkg`]:
/// signed round messages (authenticated broadcast, attributable hence
/// slashable), seal-pair private shares bound to (ceremony, dealer,
/// recipient), the deterministic common-view accumulator whose round roots
/// the ceremony CELL pins (`dregg_cell::blueprint` DKG section), and the
/// witness-first offense attribution the court/obligation lane slashes on.
pub mod dkg_ceremony;
pub mod epoch;
/// Differential: the verified Lean `Dregg2.Distributed.EpochReconfig` model ⟺ this crate's real
/// `epoch` reconfiguration (quorum threshold, the member-set transform, and the no-safety-gap
/// `verify_epoch_transition` gate with its negative witnesses). Test-only.
#[cfg(test)]
mod epoch_diff;
pub mod federation;
/// FROST (threshold-Schnorr) quorum certificates — the ADDITIVE alternative to
/// [`threshold`]'s BLS path (`docs/FROST-MIGRATION.md`): a t-of-n cert is ONE
/// ed25519-shaped Schnorr signature verified under the federation's group key
/// (`metatheory/Dregg2/Crypto/Frost.lean`), with [`frost::QuorumScheme`] the
/// both-schemes-valid selector over the opaque QC bytes. BLS is untouched.
pub mod frost;
pub mod identity;
pub mod receipt;
pub mod revocation;
pub mod solo;
pub mod threshold;
pub mod threshold_decrypt;
/// Differential: the verified Lean `Dregg2.Distributed.ThresholdDecrypt` model ⟺ this crate's real
/// `threshold_decrypt` (GF(256) field, Shamir/Lagrange reconstruction, the combine gate). Test-only.
#[cfg(test)]
mod threshold_decrypt_diff;
pub mod types;
pub mod verified_gate;
/// Per-agent ECVRF sortition (RFC 9381 ECVRF-EDWARDS25519-SHA512-TAI): each
/// candidate PRIVATELY evaluates `VRF_sk(beacon ‖ role)` and self-selects
/// under a public threshold — nobody can enumerate the jury before members
/// reveal their tickets (the targeting-resistant complement to
/// [`beacon::select_jury`], which computes a public roster). Keys are
/// CURRENT-key-class members of the agent's identity cell, covered by
/// KERI-shaped pre-rotation.
pub mod vrf;

// Re-export primary types.
pub use admission::{
    AdmissionRegistry, Bond, EquivocationEvidence, StrandId as AdmissionStrandId, Vouch,
};
pub use checkpoint::{
    Checkpoint, CheckpointError, DEFAULT_CHECKPOINT_INTERVAL, create_checkpoint,
    finalize_checkpoint, is_checkpoint_height, verify_checkpoint,
};
pub use court::{
    CourtRefusal, CourtVerdict, EquivocationCourt, EquivocationEvidenceVerifier,
    equivocation_predicate_vk, register_equivocation_court, seed_council,
};
pub use verified_gate::{FederationVerifiedGate, register_federation_verified_gate};
// The unified `Federation` type (FEDERATION-UNIFICATION-DESIGN.md §2) —
// the canonical attestation context. The Morpheus-era BFT simulator that
// previously held this name (`node.rs` + `transport.rs`, re-exported as
// `MorpheusFederation`) is DELETED (design §6 step 7): `dregg-blocklace`
// is the live consensus path, and the live hybrid-PQ quorum types live in
// [`types`] (`HybridVote`, `HybridQuorumCertificate`, `ConsensusMessage`)
// with their verifiers in [`frost`].
pub use cross_fed_bundle::CrossFedReceiptBundle;
pub use dregg_types::FederationId;
pub use federation::{Federation, KnownFederations, LocalSeat};
pub use identity::{derive_federation_id, derive_federation_id_with_epoch};
pub use receipt::{FederationReceipt, FederationReceiptBody, ReceiptQc};
pub use revocation::{RevocationTree, RevocationVerification, RevocationVerifier};
pub use solo::{
    NullifierConflict, NullifierLog, NullifierLogEntry, SoloConsensusState, is_solo_committee,
};
pub use threshold::{
    FederationCommittee, MemberSecret, ThresholdError, ThresholdQC, generate_test_committee,
    generate_test_committee_with_seed,
};
pub use threshold_decrypt::{
    DecryptionShare, KeyShare, ThresholdCiphertext, ThresholdDecryptError, ThresholdEncryptionKey,
    combine_shares, generate_epoch_key, produce_decryption_share, threshold_encrypt,
};
pub use types::{
    AttestedRoot, ConsensusMessage, HybridQuorumCertificate, HybridVote, LightClientProof,
    NodeIdentity, PublicKey, QuorumCertificate, RevocationBlock, RevocationEvent, RevocationProof,
    Signature, SigningKey, Token, ViewChangeMessage, Vote, generate_keypair, sign, verify,
    verify_attested_root_with_committee, verify_via_receipt_chain,
};
pub use vrf::{
    SortitionThreshold, SortitionTicket, VrfError, VrfProof, VrfPublicKey, VrfSecretKey,
    sortition_select, verify_sortition,
};

// =============================================================================
// Canonical BFT Threshold Functions
// =============================================================================

/// Canonical BFT quorum threshold: minimum votes needed for safety.
///
/// DELEGATES to [`dregg_blocklace::supermajority_threshold`] — there is
/// exactly ONE quorum formula in the system, the strict supermajority
/// `⌊2n/3⌋ + 1` the Cordial-Miners/Stingray DAG semantics demand. It equals
/// `n − ⌊(n−1)/3⌋` for `n ≥ 1`, so it tolerates `f = ⌊(n−1)/3⌋` Byzantine
/// members with UNCONDITIONAL quorum intersection (two quorums always share
/// more than `f` members).
///
/// - n=1 -> 1, n=2 -> 2, n=3 -> 3, n=4 -> 3, n=6 -> 5, n=7 -> 5, n=10 -> 7
///
/// History: this crate previously used `n − ⌊n/3⌋`, which agreed with the
/// blocklace supermajority everywhere EXCEPT `3 ∣ n` (n=3 gave 2-of-3,
/// n=6 gave 4-of-6 — quorums of exactly `2n/3` whose pairwise intersection
/// can be a single, possibly Byzantine, member). The Lean side
/// (`Dregg2/Distributed/BlsQuorumCert.lean`) carries that exact hole as the
/// explicit `StrictBft` hypothesis ("we carry it explicitly rather than fake
/// a margin that is false at n=3,6,9,…"); unifying on the supermajority
/// closes it for all `n`. The change is STRICTLY SAFE-SIDE relative to the
/// Lean model: this threshold is ≥ the Lean `quorumThreshold n` at every
/// `n`, so every Lean acceptance lower bound still applies, and liveness is
/// preserved because `n − f` honest members still meet it.
///
/// `n = 0` returns 1 (fail-closed): an empty committee can never attest
/// anything, instead of a vacuous threshold of 0 that an empty vote set
/// would satisfy.
pub fn quorum_threshold(n: usize) -> usize {
    dregg_blocklace::supermajority_threshold(n)
}

/// Maximum Byzantine faults tolerable for n validators: `f = ⌊(n−1)/3⌋`
/// (`n ≥ 3f + 1`, the robust-BFT bound).
///
/// This is the budget [`quorum_threshold`] actually protects against:
/// `quorum_threshold n = n − fault_tolerance n` for all `n ≥ 1`, and two
/// quorums always intersect in strictly more than `fault_tolerance n`
/// members. (The historical `⌊n/3⌋` overclaimed by one at `3 ∣ n` — with
/// n=3 it claimed to tolerate 1 fault, which no 3-member BFT system can.)
pub fn fault_tolerance(n: usize) -> usize {
    if n == 0 { 0 } else { (n - 1) / 3 }
}

#[cfg(test)]
mod threshold_tests {
    use super::*;

    /// Boundary-case pins for the ONE unified quorum formula, including the
    /// `3 ∣ n` sizes where the historical federation formula diverged.
    #[test]
    fn test_quorum_threshold() {
        assert_eq!(quorum_threshold(0), 1); // empty committee: fail-closed
        assert_eq!(quorum_threshold(1), 1);
        assert_eq!(quorum_threshold(2), 2);
        assert_eq!(quorum_threshold(3), 3); // was 2 under n − ⌊n/3⌋: the StrictBft hole
        assert_eq!(quorum_threshold(4), 3);
        assert_eq!(quorum_threshold(6), 5); // was 4: same hole
        assert_eq!(quorum_threshold(7), 5);
        assert_eq!(quorum_threshold(10), 7);
    }

    #[test]
    fn test_fault_tolerance() {
        assert_eq!(fault_tolerance(0), 0);
        assert_eq!(fault_tolerance(1), 0);
        assert_eq!(fault_tolerance(2), 0);
        assert_eq!(fault_tolerance(3), 0); // 3 nodes tolerate ZERO faults (n ≥ 3f+1)
        assert_eq!(fault_tolerance(4), 1);
        assert_eq!(fault_tolerance(7), 2);
        assert_eq!(fault_tolerance(10), 3);
    }

    /// The federation quorum IS the blocklace supermajority — the #170
    /// unification: ONE formula, ONE place, both layers consume it.
    #[test]
    fn test_quorum_is_blocklace_supermajority_everywhere() {
        for n in 0..=512usize {
            assert_eq!(
                quorum_threshold(n),
                dregg_blocklace::supermajority_threshold(n),
                "federation and blocklace quorum diverge at n={n}"
            );
            if n >= 1 {
                assert_eq!(
                    quorum_threshold(n),
                    n - fault_tolerance(n),
                    "q = n - f at n={n}"
                );
                assert!(
                    2 * quorum_threshold(n) - n > fault_tolerance(n),
                    "unconditional quorum intersection at n={n}"
                );
            }
        }
    }
}
