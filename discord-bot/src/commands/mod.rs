//! Slash command modules.
//!
//! The bot's command surface was trimmed in the post-relocation cleanup:
//! commands that depended on apps deleted from the workspace (the AMM
//! `defi.rs`, the orderbook `orderbook.rs`, and the standalone
//! stablecoin/lending/dao-treasury/prediction-market surfaces) were
//! retired rather than degraded to placeholders. The remaining commands
//! either route to apps still in the workspace (gallery, identity,
//! governed-namespace, nameservice) or to bot-local features (presence,
//! captp, queue, federation, cclerk, transfer, status, social).

pub mod cipherclerk;
pub mod explorer;
pub mod gallery;
pub mod identity;
pub mod presence;
pub mod social;
pub mod status;
pub mod transfer;

// ─── CapTP integration commands ─────────────────────────────────────────────
pub mod bounty;
pub mod captp;
// `/card` — the interactive ViewNode card inside Discord: its buttons fire real
// cap-gated verified dregg turns and the embed re-renders from the new committed state
// (`crate::viewnode_applet`).
pub mod card;
pub mod dashboard;
// The deos surface inside Discord — cap-gated affordance buttons (progressive
// attenuation), live transclusion into embeds, and dregg:// what-links-here.
pub mod deos;
pub mod federation;
pub mod governance;
pub mod handoff;
pub mod intent;
pub mod names;
pub mod polis;
pub mod queue;
