//! # `seated` — re-export of THE ONE seat-claiming multiway-tug adapter.
//!
//! The seat-claiming `SeatedTug` (claim-first-free-seat for derived identities, seat-mapped
//! hidden-hand fog, spectator refusal — changing NOTHING in `dregg-multiway-tug`) used to live
//! here as a byte-peer of the web/wechat/discord copies. It now has ONE home —
//! [`dreggnet_catalog::seated`], beside the shared catalog that registers it under the `"tug"`
//! key (docs/BOT-SHARED-BACKEND-DESIGN.md, Phase B) — and this module is the compatibility
//! re-export, so `crate::seated::SeatedTug` keeps meaning what it always did.

pub use dreggnet_catalog::seated::{SeatedTug, SeatedTugSession};
