//! `dregg-ipfs` — the IPFS bridge: **a dregg content commitment is an IPFS CID.**
//!
//! (Ported dregg-native from the retired operated layer's `dregg-ipfs` crate; the
//! verified core is unchanged.)
//!
//! dregg already content-addresses everything it stores and serves: a hosted site
//! and a storage bucket are dregg cells with a committed content root over
//! content-addressed assets/objects (`storage::bucket_commitment`), and the
//! offchain merge runtime's deltas are content-addressed by a 32-byte blake3 id
//! (`dregg-merge`). IPFS is content-addressed too — and, crucially, **IPFS CIDs
//! carry a blake3 multihash**. So a dregg blake3 content commitment, re-encoded
//! with the blake3 multicodec under a CIDv1, simply *is* the content's IPFS
//! address. No bridge hashing, no second identity.
//!
//! That alignment makes IPFS a natural backing for these dregg surfaces:
//!
//! - **storage / hosting** — pin object/asset bytes on IPFS, commit the CID in the
//!   cell. The bytes are then served from *any* node or gateway, not just the edge,
//!   and a visitor re-witnesses them against the CID (content-addressing) AND the
//!   dregg receipt (the cell commits the CID, owner-signed) — verify-don't-trust over
//!   a decentralized transport.
//! - **the merge runtime** — distribute the I-confluent `dregg-merge` deltas (a
//!   content-addressed grow-set, the Merkle-CRDT shape) over IPFS, the natural
//!   transport for content-addressed deltas.
//!
//! ## What is in this crate
//!
//! - [`cid`] — the CID alignment: [`Cid`] (CIDv1 encode/decode), [`Cid::raw_blake3`]
//!   (a blob's CID = its blake3 commitment), [`Cid::from_blake3_digest`] (wrap an
//!   existing dregg blake3 commitment, no re-hash).
//! - [`client`] — the injected transport seam [`IpfsClient`], the in-process
//!   [`MockIpfs`], and the real [`KuboClient`] (a pure Kubo-RPC formatter over an
//!   injected [`HttpPost`]; [`StdHttpPost`] is a std-only local transport).
//! - [`bridge`] — [`pin_blob`] / [`fetch_verified`] (the trustless fetch) /
//!   [`delta_cid`].
//!
//! ## Real here vs reviewed-go (honest)
//!
//! Real + tested in-process: the CID↔commitment bridge, the `IpfsClient` seam, the
//! `MockIpfs` round-trip + tamper-refusal, and the real Kubo client's RPC formatting
//! (exercised over a recording transport). Reviewed-go (ops, not code): running a
//! live IPFS daemon / pinning service, and a public gateway serving — those are a
//! deployment decision, behind the same injected seam.

pub mod bridge;
pub mod cid;
pub mod client;

pub use bridge::{blob_cid, delta_cid, fetch_verified, pin_blob};
pub use cid::{BLAKE3_LEN, CODEC_DAG_CBOR, CODEC_DAG_PB, CODEC_RAW, Cid, CidError, MH_BLAKE3};
pub use client::{HttpPost, IpfsClient, IpfsError, KuboClient, MockIpfs, StdHttpPost};
