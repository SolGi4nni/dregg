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

// `/channel` — claim a semi-private DreggNet Cloud channel to drive your Hermes
// (`crate::channels` + `crate::hermes_channel`).
pub mod channel;
// `/key` — port in / rotate / revoke YOUR OWN LLM provider key (encrypted at
// rest, metered + permissioned by dregg). See `crate::key_vault` +
// `crate::llm_provider` + `crate::hermes_channel`.
pub mod cipherclerk;
pub mod explorer;
pub mod gallery;
// `credential` is retired from the slash surface (→ `/dregg` Identity panel); the
// handlers are kept so the capability can be re-exposed without re-implementing.
#[allow(dead_code)]
pub mod key;
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
// `/coordinate` — two channel-agents cooperate over the promise-pipeline and
// settle ATOMICALLY (`crate::coordinate_flow`): a producer hands a promise, the
// consumer pipelines its payment against it, the round settles all-or-nothing
// through the verified executor.
pub mod coordinate;
pub mod federation;
// `/dungeon` — a whole channel plays a shared, AI-narrated, on-chain dungeon: buttons are
// write-once ballots (attributed to each voter's derived dregg identity), the plurality winner
// resolves through the attested `GameSession`, and `/dungeon verify` re-checks the hash chain.
// See `crate::commands::fiction` (consumes the committed `attested-dm` engine).
pub mod fiction;
// The gov-* / name-* / queue-* slash families are retired (→ `/dregg` dashboard
// Governance / Names / Subscription panels, which build the same actions). The
// handlers are kept so the capability can be re-exposed without re-implementing.
#[allow(dead_code)]
pub mod handoff;
pub mod intent;
// ─── DreggNet Cloud offerings, served through ONE generic Discord frontend ───
// `offering` is the generic adapter: any `dreggnet_offerings::Offering` becomes a Discord
// surface (its deos `ViewNode` render → an embed; its cap-gated `Action`s → buttons/modals;
// a press → ONE real `advance` attributed to the presser's derived dregg identity; `verify`
// surfaced honestly). `/council` and `/market` are its first two consumers; `/dungeon`
// (`fiction`) still carries its own bespoke ballot frontend and could adopt this next.
pub mod council;
pub mod market;
pub mod offering;
// `/buy-credits` + `/balance` — the $DREGG earning surface: issue the caller's deterministic
// deposit address + price, and show their persisted run-credit balance. A paid /dungeon run
// spends one credit for a real-AI (Bedrock) narration. See `crate::pay`.
#[allow(dead_code)]
pub mod pay;
pub mod polis;
#[allow(dead_code)]
// `/start` + `/help` — the Telegram-style front door: onboarding, a button menu
// for the common actions, and a funnel into the conversational channel. The
// buttons fire the same real cap-gated turns the slash commands did. See
// `crate::commands::start` + `discord-bot/UX-REDESIGN.md`.
pub mod start;
