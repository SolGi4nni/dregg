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
//! - [`cid`] — the CID alignment: [`Cid`] (CIDv1 encode/decode, plus legacy CIDv0
//!   `Qm…` parse for interop), [`Cid::raw_blake3`] (a blob's CID = its blake3
//!   commitment), [`Cid::from_blake3_digest`] (wrap an existing dregg blake3
//!   commitment, no re-hash). base32 decoding is canonical-strict so CID parsing is
//!   injective.
//! - [`client`] — the injected transport seam [`IpfsClient`], the in-process
//!   [`MockIpfs`], and the real network clients over an injected [`HttpPost`]
//!   (method-verb + header aware): [`KuboClient`] (Kubo RPC add/block/pin),
//!   [`GatewayClient`] (a trustless-gateway `?format=raw` block read that composes with
//!   the verified fetch), and [`PinningServiceClient`] (the IPFS Pinning Service API,
//!   the durability layer). [`StdHttpPost`] is a std-only local transport with
//!   timeouts (no TLS).
//! - [`unixfs`] — **chunked content**: a UnixFS/dag-pb file DAG builder
//!   ([`build_file_dag`] / [`pin_file`]) and the verified DAG-walk read
//!   ([`fetch_cat`]) that re-witnesses every block against its own CID. Closes the
//!   single-block-only hole. Plus **directories**: [`build_dir_dag`] / [`pin_dir`]
//!   (one dag-pb `Type=Directory` node over named file entries, links canonically
//!   name-sorted) and the verified [`fetch_dir`] that re-witnesses the directory
//!   node + every file block and returns the named entries.
//! - [`car`] — **CAR v1** export/import ([`export_car`] / [`import_car`] /
//!   [`import_car_into`]): a root + its block closure as one byte stream, every
//!   block re-witnessed against its CID on import (plus root-presence + dag-pb
//!   closure checks) — a tampered CAR is a named refusal, never a partial ingest.
//!   The fixed-shape header dag-cbor is hand-encoded (documented in the module).
//! - [`bridge`] — [`pin_blob`] (single-block, size-guarded) / [`fetch_verified`] (the
//!   trustless flat fetch) / [`fetch_authorized`] (both halves in code: the
//!   owner-receipt [`ReceiptCheck`] AND content-addressing) / [`delta_cid`].
//!
//! ## Real here vs reviewed-go (honest)
//!
//! Real + tested in-process: the CID↔commitment bridge (incl. strict base32 + CIDv0
//! parse), the `IpfsClient` seam, the `MockIpfs` round-trip + tamper-refusal, the
//! UnixFS chunker + verified DAG walk (multi-level round-trip, tamper + missing-block
//! refusal), the directory builder + verified [`fetch_dir`] (same polarities), the
//! CAR v1 codec (round-trip; exhaustive single-byte-tamper refusal; root-presence +
//! closure refusals), the receipt-composed [`fetch_authorized`], and the network
//! clients' RPC formatting (Kubo add/get/pin/block-put, gateway raw read,
//! pinning-service add) — each exercised over a recording transport. Reviewed-go
//! (ops, not code): a *live* round-trip against a running daemon / gateway / pinning
//! provider, TLS (supplied by an injected reqwest transport), **byte-exact CID
//! parity** with a live `ipfs add`'s default chunker/layout (this builder emits a
//! valid, self-consistent, fully-verifiable blake3 UnixFS DAG that [`fetch_cat`]
//! round-trips; matching go-ipfs's exact block boundaries is a deployment-time
//! concern behind the same seam), and likewise byte-exact parity of a CAR with `ipfs
//! dag export` (this CAR is a valid v1 stream per the spec; go's exact block order is
//! not canonicalized by the spec).

pub mod bridge;
pub mod car;
pub mod cid;
pub mod client;
pub mod unixfs;

pub use bridge::{
    CommittedCids, MAX_SINGLE_BLOCK, ReceiptCheck, blob_cid, delta_cid, fetch_authorized,
    fetch_verified, pin_blob,
};
pub use car::{CarContents, CarError, export_car, import_car, import_car_into};
pub use cid::{
    BLAKE3_LEN, CODEC_DAG_CBOR, CODEC_DAG_PB, CODEC_RAW, Cid, CidError, MH_BLAKE3, MH_SHA2_256,
};
pub use client::{
    GatewayClient, HttpPost, HttpRequest, HttpResponse, IpfsClient, IpfsError, KuboClient,
    MockIpfs, PinStatus, PinningServiceClient, StdHttpPost,
};
pub use unixfs::{
    Block, DirDag, FileDag, build_dir_dag, build_file_dag, fetch_cat, fetch_dir, pin_dir, pin_file,
};
