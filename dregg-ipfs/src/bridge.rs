//! `bridge` — the **verify-don't-trust** read over a decentralized transport.
//!
//! This is the payoff the [`crate::cid`] alignment buys: a dregg content-addressed
//! object can be pinned on, and fetched from, *any* IPFS node, and a reader
//! re-witnesses it against the same content commitment with **no trust in the node**
//! it fetched from. Two independent checks compose:
//!
//! 1. **content-addressing** ([`fetch_verified`]): the fetched bytes must hash to the
//!    CID they were fetched under. A node that flips a byte moves the hash and is
//!    refused — this is intrinsic to IPFS and needs no dregg machinery.
//! 2. **the dregg receipt** (the caller's existing trustless read): the cell commits
//!    the CID (it is bound into the cell's `content_root` and the signed publish /
//!    put receipt), so the reader checks that the CID it fetched under is the one the
//!    owner committed — caught by the storage bucket-commitment trustless read
//!    (`storage::bucket_commitment::verify_opening`) over the committed cell.
//!
//! Together: *which* bytes (the CID, by content-addressing) AND *whose/authorized*
//! bytes (the receipt, by the owner-signed cell). IPFS gives a decentralized, any-node
//! transport; dregg adds the authorized, receipted, cap-gated commitment IPFS alone
//! does not have. (Contrast Fleek: git→IPFS, trust the pin/gateway — no operation
//! receipt, no cap-gate, no verifiable cell.)

use crate::cid::{CODEC_DAG_CBOR, CODEC_RAW, Cid};
use crate::client::{IpfsClient, IpfsError};

/// The CID a raw blob will be pinned under — `raw(blake3(bytes))`, the dregg content
/// commitment. Computing it locally lets a caller commit the CID in the cell
/// *before* (or independently of) pinning.
pub fn blob_cid(bytes: &[u8]) -> Cid {
    Cid::raw_blake3(bytes)
}

/// Wrap a `dregg-merge` delta's 32-byte blake3 content id as a CID (default
/// `dag-cbor` codec — a delta is a structured IPLD node). The CID's digest IS the
/// delta id, so fetching a delta by this CID and recomputing its id re-witnesses it.
/// This is the cleanest alignment in the system: the merge runtime's content id and
/// its IPFS address are the same 32 bytes.
pub fn delta_cid(delta_id: [u8; 32]) -> Cid {
    Cid::from_blake3_digest(CODEC_DAG_CBOR, delta_id)
}

/// Pin `bytes` to `client` and return the CID, asserting the node agreed on the
/// content address (a node that returns a CID other than `raw(blake3(bytes))` is
/// refused — it computed the address differently / dishonestly).
pub fn pin_blob<C: IpfsClient>(client: &C, bytes: &[u8]) -> Result<Cid, IpfsError> {
    let expected = blob_cid(bytes);
    let got = client.put_raw(bytes)?;
    if got != expected {
        return Err(IpfsError::CidMismatch {
            requested: expected.to_string_cid(),
            got: got.to_string_cid(),
        });
    }
    Ok(got)
}

/// **The trustless fetch.** Fetch the bytes addressed by `cid` from `client` and
/// re-witness them by content-addressing: recompute `blake3` and require it equals
/// the CID's embedded digest. A lying node that serves tampered bytes is refused with
/// [`IpfsError::CidMismatch`].
///
/// Only whole-blob **raw blake3** CIDs are flat-verifiable here (a chunked dag-pb
/// root cannot be checked by a flat re-hash — see [`crate::cid`]); a non-raw CID is
/// refused with [`IpfsError::NotVerifiableByFlatHash`] rather than silently trusted.
pub fn fetch_verified<C: IpfsClient>(client: &C, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
    if cid.codec != CODEC_RAW || !cid.is_raw_blake3() {
        return Err(IpfsError::NotVerifiableByFlatHash(cid.to_string_cid()));
    }
    let bytes = client.get(cid)?;
    let recomputed = Cid::raw_blake3(&bytes);
    if &recomputed != cid {
        return Err(IpfsError::CidMismatch {
            requested: cid.to_string_cid(),
            got: recomputed.to_string_cid(),
        });
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::MockIpfs;

    #[test]
    fn pin_then_fetch_verified_round_trips() {
        let node = MockIpfs::new();
        let bytes = b"<h1>hello from a dregg cell</h1>";
        let cid = pin_blob(&node, bytes).unwrap();
        // The CID is the dregg content commitment of the blob.
        assert_eq!(cid, blob_cid(bytes));
        // Fetched + re-witnessed against the CID with no trust in the node.
        assert_eq!(fetch_verified(&node, &cid).unwrap(), bytes);
    }

    #[test]
    fn a_tampered_fetch_is_refused() {
        let node = MockIpfs::new();
        let cid = pin_blob(&node, b"the authorized bytes").unwrap();
        // The node turns malicious and serves different bytes under the same CID.
        node.tamper(&cid, b"OWNED BY THE NODE");
        let err = fetch_verified(&node, &cid).unwrap_err();
        assert!(matches!(err, IpfsError::CidMismatch { .. }), "got {err:?}");
    }

    #[test]
    fn a_chunked_dag_root_is_not_flat_verifiable() {
        let node = MockIpfs::new();
        // A dag-pb CID over some digest is refused by the flat verifier (rather than
        // trusted) — it must be checked through the chunker, not a flat re-hash.
        let dag = Cid::from_blake3_digest(crate::cid::CODEC_DAG_PB, [7u8; 32]);
        let err = fetch_verified(&node, &dag).unwrap_err();
        assert!(
            matches!(err, IpfsError::NotVerifiableByFlatHash(_)),
            "got {err:?}"
        );
    }

    #[test]
    fn delta_cid_carries_the_exact_delta_id() {
        // A dregg-merge delta id (32-byte blake3) re-encodes to a CID with the SAME
        // digest — fetch-by-CID + recompute-id re-witnesses the delta.
        let id = *blake3::hash(b"a delta").as_bytes();
        let cid = delta_cid(id);
        assert_eq!(cid.blake3_digest().unwrap(), id);
        assert_eq!(cid.codec, CODEC_DAG_CBOR);
    }
}
