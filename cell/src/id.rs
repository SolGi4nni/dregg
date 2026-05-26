/// Re-export `CellId` from the canonical `dregg-types` crate.
///
/// The cell crate uses `CellId::derive_raw(&[u8;32], &[u8;32])` for agent cell
/// derivation. This uses domain-separated BLAKE3 hashing.
pub use dregg_types::CellId;
