//! THE NOMAD-LAW analog: an empty committee, an all-zero signature, or zero
//! participants must NEVER verify. (Named for the Nomad bridge hole where a
//! zero/trivial proof was accepted — the light client's floor is that no
//! degenerate input authorizes an update.)

use eth_lightclient::{
    verify_sync_aggregate, BeaconBlockHeader, Error, SyncAggregate, SYNC_COMMITTEE_SIZE,
};

const FORK_VERSION: [u8; 4] = [0x03, 0x00, 0x00, 0x00];
const GVR: [u8; 32] = [0x42u8; 32];

fn header() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: 1,
        proposer_index: 1,
        parent_root: [1u8; 32],
        state_root: [2u8; 32],
        body_root: [3u8; 32],
    }
}

fn full_bits() -> [u8; SYNC_COMMITTEE_SIZE / 8] {
    [0xFFu8; SYNC_COMMITTEE_SIZE / 8]
}

#[test]
fn empty_committee_never_verifies() {
    // Zero-length committee -> WrongCommitteeSize, regardless of the aggregate.
    let agg = SyncAggregate {
        sync_committee_bits: full_bits(),
        sync_committee_signature: [0u8; 96],
    };
    assert_eq!(
        verify_sync_aggregate(&header(), &agg, &[], FORK_VERSION, GVR),
        Err(Error::WrongCommitteeSize { got: 0 })
    );
}

#[test]
fn all_zero_signature_never_verifies() {
    // A full-participation bitfield but an all-zero signature: 96 zero bytes are
    // not a valid compressed G2 point -> BadSignature (never accepted).
    let committee = vec![[0x01u8; 48]; SYNC_COMMITTEE_SIZE]; // committee content irrelevant here
    let agg = SyncAggregate {
        sync_committee_bits: full_bits(),
        sync_committee_signature: [0u8; 96],
    };
    let r = verify_sync_aggregate(&header(), &agg, &committee, FORK_VERSION, GVR);
    // Either BadPubkey (0x01.. is not on-curve) or BadSignature — the point is it
    // is an Err, never Ok. Assert specifically it is not Ok.
    assert!(
        r.is_err(),
        "all-zero signature must never verify, got {r:?}"
    );
}

#[test]
fn zero_participants_never_verifies() {
    // A valid-length committee but an all-zero bitfield -> NoParticipants.
    // (Uses the real KAT-style committee content is unnecessary; participation is
    // checked before any point work.)
    let committee = vec![[0x01u8; 48]; SYNC_COMMITTEE_SIZE];
    let agg = SyncAggregate {
        sync_committee_bits: [0u8; SYNC_COMMITTEE_SIZE / 8],
        sync_committee_signature: [0u8; 96],
    };
    assert_eq!(
        verify_sync_aggregate(&header(), &agg, &committee, FORK_VERSION, GVR),
        Err(Error::NoParticipants)
    );
}

#[test]
fn zero_pubkeys_with_full_participation_never_verifies() {
    // Committee of all-zero pubkeys (48 zero bytes is not a valid encoding) with
    // full participation -> must fail closed on pubkey decode.
    let committee = vec![[0x00u8; 48]; SYNC_COMMITTEE_SIZE];
    let agg = SyncAggregate {
        sync_committee_bits: full_bits(),
        sync_committee_signature: [0xC0u8; 96],
    };
    let r = verify_sync_aggregate(&header(), &agg, &committee, FORK_VERSION, GVR);
    assert!(
        r.is_err(),
        "all-zero committee pubkeys must never verify, got {r:?}"
    );
}
