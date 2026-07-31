//! # dregg-epoch — the explicit, discoverable epoch handshake
//!
//! The dregg upgrade story is GIT-LOCKSTEP + FAIL-CLOSED: the light-client
//! descriptors, the registry fingerprints ([`WIDE_REGISTRY_STAGED_FP`] +
//! [`WIDE_UMEM_WELD_REGISTRY_FP`] — the two registries the deployed
//! prover/verifiers actually run), the effect-VM geometry, and the
//! slot-caveat tag vocabulary are all compile-time constants. A client's "epoch" is *implicitly* whatever git HEAD it compiled
//! against. When a client and a node were built from different HEADs, the only
//! symptom today is a silent verification mismatch: the client cannot tell
//! *whether* it can talk to a node, or *which* caveat tags that node will use,
//! until a proof fails to verify.
//!
//! This crate converts that implicit lockstep into an EXPLICIT, DISCOVERABLE
//! epoch. An [`EpochManifest`] is a small, self-describing summary of the
//! epoch a binary belongs to, DERIVED from the real baked constants (never a
//! hardcoded duplicate). A node advertises its manifest; a client compares it
//! to its own with [`check_compatibility`] and learns, on connect and BEFORE
//! any proof round-trip, exactly whether it is compatible and — if not — WHY.
//!
//! ## What is real here vs. what is a named seam
//!
//! REAL (this crate): the manifest derived from the constants, and the pure
//! [`check_compatibility`] handshake that returns a typed [`EpochCompat`]
//! verdict (compatible, or a specific, actionable incompatibility).
//!
//! NAMED SEAM (not built here): the transport. Serving the manifest over an
//! HTTP `/epoch` endpoint, fetching it from a peer on connect, and wiring the
//! verdict into the live node-connect path (and into the browser-extension /
//! wasm client) is a deploy wire — the same shape as the receipt-stream and
//! indexer *pure cores* whose HTTP surfaces live elsewhere. The manifest
//! derives `Serialize`/`Deserialize` so that wire can carry it verbatim.
//!
//! ## How this becomes the rollout-observability layer
//!
//! With the manifest in hand a client knows its compatibility BEFORE it fails.
//! That is the substrate the other two upgrade-liveness directions build on:
//! the drift-taxonomy CI gate (#2) classifies a manifest delta as tail-append
//! vs. geometry-widen; genesis-from-snapshot (#3) lets a client that sees a
//! new [`registry_fp`](EpochManifest::registry_fp) discover that its cells
//! survive the re-genesis.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

// The single sources of truth. Everything the manifest advertises is DERIVED
// from these — this crate holds no duplicated fingerprints or tag numbers.
use dregg_circuit::effect_vm::columns::EFFECT_VM_WIDTH;
use dregg_circuit::effect_vm::columns::rotation::caveat::R as ROTATION_R;
use dregg_circuit::effect_vm::pi::{
    SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS, SLOT_CAVEAT_TAG_CHALLENGE_WINDOW,
    SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, SLOT_CAVEAT_TAG_FIELD_DELTA,
    SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED, SLOT_CAVEAT_TAG_FIELD_EQUALS, SLOT_CAVEAT_TAG_FIELD_GTE,
    SLOT_CAVEAT_TAG_FIELD_LTE, SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER, SLOT_CAVEAT_TAG_IMMUTABLE,
    SLOT_CAVEAT_TAG_MONOTONIC, SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE, SLOT_CAVEAT_TAG_RATE_BOUND,
    SLOT_CAVEAT_TAG_SENDER_AUTHORIZED, SLOT_CAVEAT_TAG_SETTLE_ESCROW, SLOT_CAVEAT_TAG_SINCE_EVENT,
    SLOT_CAVEAT_TAG_STRICT_MONOTONIC, SLOT_CAVEAT_TAG_TEMPORAL_GATE, SLOT_CAVEAT_TAG_UNTIL_EVENT,
    SLOT_CAVEAT_TAG_VAULT_DEPOSIT, SLOT_CAVEAT_TAG_WRITE_ONCE,
};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_FP, WIDE_UMEM_WELD_REGISTRY_FP};

/// The wire-protocol version of the epoch handshake ITSELF (the shape of the
/// [`EpochManifest`] on the wire), independent of any circuit rotation. Bump
/// this on a breaking layout change to the manifest struct.
pub const EPOCH_WIRE_VERSION: u32 = 1;

/// The oldest handshake wire version this binary can still talk to. A remote
/// advertising a `wire_version` below this is [`EpochCompat::WireTooOld`]; the
/// window a local accepts is the inclusive range
/// `[EPOCH_MIN_COMPATIBLE_WIRE, EPOCH_WIRE_VERSION]`.
pub const EPOCH_MIN_COMPATIBLE_WIRE: u32 = 1;

/// The human-readable cohort name of the descriptor set. This is a NAME for
/// the epoch (the machine-checkable identity is [`EpochManifest::registry_fp`],
/// which the handshake actually compares); the tag is what an operator says out
/// loud. See `docs/HANDOFF-v13-VK-EPOCH.md`.
pub const DESCRIPTOR_SET_COHORT: &str = "v13-geom";

/// The full set of slot-caveat tags THIS binary knows how to re-evaluate — the
/// vocabulary a light client can verify off-AIR. Built by referencing each
/// `SLOT_CAVEAT_TAG_*` const, so a tag whose value drifts in the circuit is
/// caught by the pin test, and the set is the explicit registry that a
/// new-tag lockstep step must extend (adding a tag = adding it here).
pub fn known_caveat_tags() -> BTreeSet<u32> {
    [
        SLOT_CAVEAT_TAG_FIELD_EQUALS,
        SLOT_CAVEAT_TAG_FIELD_GTE,
        SLOT_CAVEAT_TAG_FIELD_LTE,
        SLOT_CAVEAT_TAG_WRITE_ONCE,
        SLOT_CAVEAT_TAG_IMMUTABLE,
        SLOT_CAVEAT_TAG_MONOTONIC,
        SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
        SLOT_CAVEAT_TAG_FIELD_DELTA,
        SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
        SLOT_CAVEAT_TAG_TEMPORAL_GATE,
        SLOT_CAVEAT_TAG_SENDER_AUTHORIZED,
        SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
        SLOT_CAVEAT_TAG_RATE_BOUND,
        SLOT_CAVEAT_TAG_UNTIL_EVENT,
        SLOT_CAVEAT_TAG_SINCE_EVENT,
        SLOT_CAVEAT_TAG_CHALLENGE_WINDOW,
        SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
        SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED,
        SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER,
    ]
    .into_iter()
    .collect()
}

/// A binary's self-description of the epoch it belongs to. Everything here is
/// DERIVED from baked constants by [`local_manifest`]; a remote binary sends
/// the same struct over the wire (the transport is a named seam).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EpochManifest {
    /// The registry fingerprint — the sha256 fingerprints of the DEPLOYED
    /// effect-VM descriptor registries, `<wide>+<wide-umem-welded>`
    /// ([`WIDE_REGISTRY_STAGED_FP`] + [`WIDE_UMEM_WELD_REGISTRY_FP`] — the two
    /// registries the live producer mints from and the wire/executor verifiers
    /// iterate). This is the LOAD-BEARING identity: two binaries can verify
    /// each other's proofs iff their `registry_fp` match (same VK-epoch). A
    /// geometry-widen or any descriptor change moves this string. (It
    /// previously pinned the bare 1-felt `V3_STAGED_REGISTRY_FP`, which the
    /// deployed proof path no longer resolves from — an S2-class wide flag-day
    /// was INVISIBLE to the handshake while the bare TSV stayed byte-stable.)
    pub registry_fp: String,
    /// The human-readable cohort name plus the effect-VM geometry it was built
    /// with (width + rotation register count), e.g. `"v13-geom/w188/r24"`. The
    /// geometry is folded in from the real constants so a geometry-widen is
    /// visible in the tag as well as in `registry_fp`.
    pub descriptor_set_tag: String,
    /// The slot-caveat tags this binary knows how to re-evaluate.
    pub known_caveat_tags: BTreeSet<u32>,
    /// The handshake wire-protocol version this binary speaks.
    pub wire_version: u32,
    /// The oldest wire version this binary still accepts from a remote.
    pub min_compatible: u32,
}

/// Build the local binary's manifest from the real baked constants.
pub fn local_manifest() -> EpochManifest {
    EpochManifest {
        registry_fp: format!("{WIDE_REGISTRY_STAGED_FP}+{WIDE_UMEM_WELD_REGISTRY_FP}"),
        descriptor_set_tag: format!("{DESCRIPTOR_SET_COHORT}/w{EFFECT_VM_WIDTH}/r{ROTATION_R}"),
        known_caveat_tags: known_caveat_tags(),
        wire_version: EPOCH_WIRE_VERSION,
        min_compatible: EPOCH_MIN_COMPATIBLE_WIRE,
    }
}

/// The typed verdict of a handshake. Exactly one of these tells a client, on
/// connect, whether it can talk to a node — and if not, precisely why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EpochCompat {
    /// Same VK-epoch, wire in range, no unknown tags required — proofs from the
    /// remote will verify locally.
    Compatible,
    /// Different registry fingerprints: a different VK-epoch. The client cannot
    /// verify this node's proofs at all; it must rebuild against the node's
    /// HEAD (a geometry-widen re-genesis, or a descriptor change).
    RegistryFpMismatch { local: String, remote: String },
    /// The remote speaks a handshake wire newer than this binary understands
    /// (`remote > local_max`): the client is behind and must upgrade.
    WireTooNew { local_max: u32, remote: u32 },
    /// The remote speaks a handshake wire older than this binary still accepts
    /// (`remote < local_min`): the node is behind.
    WireTooOld { local_min: u32, remote: u32 },
    /// The remote's epoch uses caveat tags this binary does not know how to
    /// re-evaluate. The client would silently fail to verify any turn carrying
    /// one of these; instead it learns EXACTLY which tags it is missing (the
    /// git-lockstep made discoverable).
    UnknownTags { tags: BTreeSet<u32> },
}

impl EpochCompat {
    /// Whether the verdict is [`EpochCompat::Compatible`].
    pub fn is_compatible(&self) -> bool {
        matches!(self, EpochCompat::Compatible)
    }
}

/// The handshake. Compare the `local` binary's manifest against a `remote`
/// binary's advertised manifest and return a typed verdict. Fails CLOSED: any
/// incompatibility is a specific, actionable reason, never a silent pass.
///
/// The checks run in priority order — the registry fingerprint is the
/// fundamental VK-epoch identity, so a mismatch there is reported first (the
/// wire and tag sets are meaningless across a different VK-epoch); then the
/// wire-version window; then the caveat-tag vocabulary.
pub fn check_compatibility(local: &EpochManifest, remote: &EpochManifest) -> EpochCompat {
    // 1. Same VK-epoch? The load-bearing identity.
    if local.registry_fp != remote.registry_fp {
        return EpochCompat::RegistryFpMismatch {
            local: local.registry_fp.clone(),
            remote: remote.registry_fp.clone(),
        };
    }

    // 2. Is the remote's wire within the window this local accepts?
    if remote.wire_version > local.wire_version {
        return EpochCompat::WireTooNew {
            local_max: local.wire_version,
            remote: remote.wire_version,
        };
    }
    if remote.wire_version < local.min_compatible {
        return EpochCompat::WireTooOld {
            local_min: local.min_compatible,
            remote: remote.wire_version,
        };
    }

    // 3. Does the remote require any caveat tag this local cannot re-evaluate?
    //    (tags the remote knows that the local does not).
    let unknown: BTreeSet<u32> = remote
        .known_caveat_tags
        .difference(&local.known_caveat_tags)
        .copied()
        .collect();
    if !unknown.is_empty() {
        return EpochCompat::UnknownTags { tags: unknown };
    }

    EpochCompat::Compatible
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- The manifest reflects the REAL baked constants (the hard gate) ----

    #[test]
    fn local_manifest_registry_fp_is_the_baked_const() {
        // A future registry regeneration (new VK-epoch) changes the baked
        // fingerprints; this asserts the manifest tracks them rather than a copy.
        assert_eq!(
            local_manifest().registry_fp,
            format!("{WIDE_REGISTRY_STAGED_FP}+{WIDE_UMEM_WELD_REGISTRY_FP}")
        );
        // And the deployed values are the sha256 hexes we expect at this HEAD, so a silent
        // fingerprint drift is caught here. (The manifest previously pinned the bare 1-felt V3 FP —
        // and this test's stale pin proved that gate never re-armed after a bare regen; the wide
        // pins are the deployed truth.)
        //
        // ⚑ ROTATED BY THE LAST-ROW ANCHOR FORGE CLOSURE (2026-07-30), superseding the setField
        // VALUE8 epoch's pins. Every row-local constraint body in all 174 deployed members moved
        // from the transition-domain `gate` to the WHOLE-domain `windowGate { on_transition:
        // false }` (Lean `Dregg2.Circuit.Emit.LastRowFrameHardening.hardenLastRow`), so the LAST
        // row — the row every member pins its published 8-felt AFTER anchor on, the value
        // `ivc_turn_chain` folds as the turn's endpoint — carries algebra instead of nothing.
        // Before it, a prover published an endpoint of its own choosing for the cost of one honest
        // proving run (MEASURED: `circuit/tests/last_row_anchor_forge.rs`).
        //
        // ALL THREE registry fingerprints moved, so this is a NEW VK-EPOCH and a FLAG DAY, not a
        // migration: a binary built before the flip reports `RegistryFpMismatch` against one built
        // after — the old shape REFUSES TO LOAD rather than reinterpreting, which is the intended
        // fail-closed handshake. Every verifier, light client and relayer must be rebuilt. No
        // geometry widened (widths and PI counts are unchanged), so this is NOT a re-genesis.
        assert_eq!(
            WIDE_REGISTRY_STAGED_FP,
            "0c6c402d332b16171b0511ce2df506cc8639c411099dfbc052a0ef828f7135dd"
        );
        assert_eq!(
            WIDE_UMEM_WELD_REGISTRY_FP,
            "a028e25fee2e9c05c941fb4592a7e003ed197fdd3a32996b2e94180d130cc3a5"
        );
    }

    #[test]
    fn known_caveat_tags_are_exactly_the_circuit_tag_set() {
        let tags = known_caveat_tags();
        // The 21 tags the deployed binary knows (contiguous 1..=21 today).
        assert_eq!(tags.len(), 21, "a new SLOT_CAVEAT_TAG must be added here");
        assert_eq!(*tags.iter().min().unwrap(), 1);
        assert_eq!(
            *tags.iter().max().unwrap(),
            SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER
        );
        // The named tags this piece exists to make discoverable map to their
        // circuit consts (a value drift in the circuit is caught here).
        assert_eq!(SLOT_CAVEAT_TAG_SETTLE_ESCROW, 17);
        assert_eq!(SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, 18);
        assert_eq!(SLOT_CAVEAT_TAG_VAULT_DEPOSIT, 19);
        assert_eq!(SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED, 20);
        assert_eq!(SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER, 21);
        for t in [17u32, 18, 19, 20, 21] {
            assert!(tags.contains(&t));
        }
    }

    #[test]
    fn descriptor_set_tag_folds_in_the_real_geometry() {
        let m = local_manifest();
        // The geometry constants are DERIVED, not hardcoded: a geometry-widen
        // (width move) shows up in the human tag as well as in registry_fp.
        assert_eq!(
            m.descriptor_set_tag,
            format!("v13-geom/w{EFFECT_VM_WIDTH}/r{ROTATION_R}")
        );
        assert_eq!(EFFECT_VM_WIDTH, 188);
        assert_eq!(ROTATION_R, 24);
        assert_eq!(m.descriptor_set_tag, "v13-geom/w188/r24");
    }

    // ---- The handshake: every arm non-vacuous, the matching case succeeds ----

    #[test]
    fn matching_manifest_is_compatible() {
        let local = local_manifest();
        let remote = local_manifest();
        assert_eq!(
            check_compatibility(&local, &remote),
            EpochCompat::Compatible
        );
        assert!(check_compatibility(&local, &remote).is_compatible());
    }

    #[test]
    fn mismatched_registry_fp_is_a_different_vk_epoch() {
        let local = local_manifest();
        let mut remote = local_manifest();
        remote.registry_fp = "deadbeef".repeat(8); // a different VK-epoch
        match check_compatibility(&local, &remote) {
            EpochCompat::RegistryFpMismatch {
                local: l,
                remote: r,
            } => {
                assert_eq!(
                    l,
                    format!("{WIDE_REGISTRY_STAGED_FP}+{WIDE_UMEM_WELD_REGISTRY_FP}")
                );
                assert_eq!(r, "deadbeef".repeat(8));
            }
            other => panic!("expected RegistryFpMismatch, got {other:?}"),
        }
    }

    #[test]
    fn remote_requiring_an_unknown_tag_is_reported_exactly() {
        // A newer node whose epoch added tag 22 (a hypothetical future caveat)
        // that this older client does not know how to re-evaluate.
        let local = local_manifest();
        let mut remote = local_manifest();
        remote.known_caveat_tags.insert(22);
        remote.known_caveat_tags.insert(99);
        match check_compatibility(&local, &remote) {
            EpochCompat::UnknownTags { tags } => {
                assert_eq!(tags, BTreeSet::from([22, 99]));
            }
            other => panic!("expected UnknownTags, got {other:?}"),
        }
    }

    #[test]
    fn a_local_that_knows_more_tags_than_the_remote_is_still_compatible() {
        // The client knowing EXTRA tags the node doesn't use is fine — the node
        // will never emit a tag the client can't read. Only the reverse breaks.
        let mut local = local_manifest();
        local.known_caveat_tags.insert(22);
        let remote = local_manifest();
        assert_eq!(
            check_compatibility(&local, &remote),
            EpochCompat::Compatible
        );
    }

    #[test]
    fn remote_wire_newer_than_local_is_too_new() {
        let local = local_manifest();
        let mut remote = local_manifest();
        remote.wire_version = EPOCH_WIRE_VERSION + 1;
        assert_eq!(
            check_compatibility(&local, &remote),
            EpochCompat::WireTooNew {
                local_max: EPOCH_WIRE_VERSION,
                remote: EPOCH_WIRE_VERSION + 1,
            }
        );
    }

    #[test]
    fn remote_wire_older_than_min_compatible_is_too_old() {
        // Raise the local's floor so a same-version remote reads as too old.
        let mut local = local_manifest();
        local.wire_version = 3;
        local.min_compatible = 2;
        let mut remote = local_manifest();
        remote.wire_version = 1;
        assert_eq!(
            check_compatibility(&local, &remote),
            EpochCompat::WireTooOld {
                local_min: 2,
                remote: 1,
            }
        );
    }

    #[test]
    fn registry_mismatch_takes_priority_over_wire_and_tags() {
        // A different VK-epoch is reported even if the wire and tags also differ
        // — the fundamental identity comes first.
        let local = local_manifest();
        let mut remote = local_manifest();
        remote.registry_fp = "0".repeat(64);
        remote.wire_version = 999;
        remote.known_caveat_tags.insert(42);
        assert!(matches!(
            check_compatibility(&local, &remote),
            EpochCompat::RegistryFpMismatch { .. }
        ));
    }

    #[test]
    fn manifest_round_trips_through_serde() {
        // The transport seam carries this struct verbatim.
        let m = local_manifest();
        let json = serde_json::to_string(&m).unwrap();
        let back: EpochManifest = serde_json::from_str(&json).unwrap();
        assert_eq!(m, back);
    }
}
