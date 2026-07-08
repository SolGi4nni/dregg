//! deos-homeserver — continuwuity embedded as a library, the grain body for the
//! self-hosted membrane (see `docs/deos/GRAIN-HOMESERVER.md`).
//!
//! The embed seam (`conduwuit::run_with_args(&Args)`) boots a real Matrix
//! homeserver in-process. This crate wraps that into an `EmbeddedHomeserver`
//! (loopback config + graceful shutdown) so a dregg grain can host the membrane
//! its co-driven cards ride, instead of an external Docker Conduit.
//!
//! Step 1 (this crate): boot it in-process + prove it serves the CS API a Matrix
//! client needs. Step 2/3 (design-first): the confined spawn + the one
//! `grant_read_write` firmament door for the RocksDB dir.

// The EmbeddedHomeserver + its CS-API proof land here.
