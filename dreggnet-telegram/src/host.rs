//! # `TelegramHost` — the MULTI-OFFERING Telegram layer over the ONE offering core.
//!
//! [`crate::TelegramFrontend`] is offering #0's Telegram surface: it plays a single
//! [`DungeonOffering`](dreggnet_offerings::dungeon::DungeonOffering). This module gives the
//! dungeon (and every other offering) a SECOND live surface — the same "all offerings, any
//! surface" the web catalog ([`dreggnet_web::CatalogState`]) got — by driving the
//! frontend-agnostic [`OfferingHost`] through the Telegram frontend:
//!
//! - **list** — [`TelegramHost::list_offerings`] / [`TelegramHost::present_offerings_menu`]: a
//!   `/offerings`-style control message whose inline keyboard is one button per registered
//!   offering (a press opens that offering in the chat);
//! - **open** — [`TelegramHost::open`]: open a session per `(offering, chat)` on the host and
//!   present the offering's [`Surface`] on that offering's OWN message in the chat (several
//!   offerings coexist per chat; a press routes by the message it was pressed on);
//! - **advance** — [`TelegramHost::press`]: a button press → [`TelegramFrontend::collect`] the
//!   typed [`Action`] → [`OfferingHost::advance`] ONE real turn on the substrate → re-present;
//! - **verify** — [`TelegramHost::verify`]: re-verify an offering session's committed chain; ALSO
//!   routed through [`TelegramHost::press`] as the reserved [`TURN_VERIFY`] verb, so a shell's
//!   `/verify` input (or a pinned button) reaches the real re-verifier through the ONE router.
//!
//! ## The `!Send` host + the [`HostThread`] handle (mirrors `dreggnet-web`)
//! The [`OfferingHost`] owns heterogeneous offering sessions, some `!Send` (a
//! `CouncilOffering` session holds `Rc`-backed ballot caps).
//! So the host cannot be shared behind a plain `Send` handle; it lives on ONE owning thread and
//! every access is a job shipped to it — only the job's plain-data result (a [`Surface`], an
//! [`Outcome`], a [`VerifyReport`], a `Vec<OfferingInfo>`, all `Send`) crosses back. The
//! [`TelegramFrontend`] itself (the affordance-renderer + the injected transport) stays on the
//! calling thread; it never holds an offering session. This is exactly `dreggnet-web`'s
//! [`HostThread`](dreggnet_web) pattern reused for Telegram.
//!
//! ## Who reads the surface decides which projection it carries
//! A **DM** is read by one person; a **group / forum topic** is read by everyone in it, and its
//! session is ONE message that every re-present EDITS in place. So a per-viewer projection
//! ([`OfferingHost::render_for`] — a hidden hand, a sealed move) is served only in a DM; a shared
//! chat always gets the viewer-blind [`OfferingHost::render`]. On top of that structural rule, an
//! offering that DECLARES hidden information
//! ([`dreggnet_offerings::Offering::hidden_information`] — tug, automatafl) is not hosted in a
//! shared chat at all: it is refused at open ([`OpenError::HiddenInSharedChat`]) with a legible
//! redirect to a DM / the Mini App, because a public-only projection is not a playable hand.
//!
//! ## Surface → keyboard mapping
//! An offering's [`Surface`] is a deos view-tree; its cap-gated [`Action`]s are the moves. The
//! text half of the surface renders to the message body ([`crate::render::render_surface_text`]);
//! the [`Action`]s render to the inline keyboard, one button per affordance, each button's
//! `callback_data` carrying its `{turn, arg}` ([`crate::api::build_present_request`]) — identical
//! to offering #0's mapping, now driven for ANY offering. The offerings menu is a host-level
//! control keyboard whose buttons carry [`TURN_OPEN`] `{turn:"open", arg: offering index}`.
//!
//! ## Honest scope — what a live Telegram deploy adds
//! Everything here is driven at the logic level with [`crate::transport::MockTransport`] (NO
//! token, NO network). A live deploy adds only: a bot token + a reqwest-backed
//! [`HttpPost`](crate::transport::HttpPost) under [`RawBotApi`](crate::transport::RawBotApi); the
//! update loop / webhook that turns real `CallbackQuery`/`Message` updates into
//! [`TelegramHost::press`] / [`TelegramHost::open`] calls; and a durable session store (this host
//! keeps sessions in memory on its owning thread, seeded deterministically from the chat id, so a
//! restart re-derives the SAME replay-verifiable session but loses in-flight state). WeChat adopts
//! this SAME [`OfferingHost`] next — the host is unchanged; only this thin surface layer differs.

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};

use base64::Engine as _;
use deos_view::ViewNode;
use dreggnet_catalog::{
    CatalogConfig, GameActionRef, GameAffordance, GameAudience, GameCommand, GameEpochLedger,
    GameHostIncarnation, GameKind, GameOperationRef, GameReceipt, GameResult, PlayerWorlds,
    PublicGameReceipt, execute_bound_asserted_game_command, execute_bound_asserted_game_turn,
    game_kind, inspect_bound_game_session, is_rpg_key, project_public_game_receipt,
};
use dreggnet_offerings::shelf::{self, ShelfEntry, ShelfSurface};
use dreggnet_offerings::{
    Action, Audience, BinaryOperationDescriptor, BinaryOperationReceipt, ChatBinaryOperationPolicy,
    DreggIdentity, Frontend, HostError, OfferingHost, OfferingInfo, Outcome, SessionId,
    SessionPolicy, Surface, SystemClock, VerifyReport, preflight_chat_binary_operation,
};

use crate::cipherclerk::TelegramCipherclerk;
use crate::transport::{MessageId, Transport};
use crate::{ChatId, ChatKind, TelegramFrontend, TelegramUserId};

#[cfg(feature = "shielded-crown-controller")]
mod shielded_crown;
#[cfg(feature = "shielded-crown-controller")]
pub use shielded_crown::{
    ShieldedCrownAuthorityCustody, ShieldedCrownAuthorityStore, TelegramShieldedCrownError,
    TelegramShieldedCrownRequest,
};

/// The affordance verb the offerings-menu buttons carry — a host-level control (open the offering
/// at `arg` in this chat), distinct from any offering's own turn verbs.
pub const TURN_OPEN: &str = "open";

/// Stable companion-message slot carrying the full binary-operation descriptors. The guide is
/// deliberately not an action surface: its message ids are never eligible callback routes.
pub const OPERATION_GUIDE_SLOT: &str = "proof-operations";

/// The one binary operation whose payload is intentionally public and whose verifier binds the
/// authenticated uploader to the exact live group roster/session. This is not a general group
/// document exception and never confers bearer authority.
const PRIVATE_RAID_KEY: &str = "private-raid";
const PRIVATE_RAID_ASSIGN_OPERATION: &str = "party.private-raid-assignment.v1";

fn shared_operation_allowed(key: &str, operation: &str) -> bool {
    key == PRIVATE_RAID_KEY && operation == PRIVATE_RAID_ASSIGN_OPERATION
}

/// Telegram callback wire for one exact bound game action. `g.` plus a full
/// base64url-no-pad BLAKE3 digest is 45 bytes, below Telegram's 64-byte ceiling.
fn bound_game_callback(reference: &GameActionRef) -> String {
    format!(
        "g.{}",
        base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(reference.routing_preimage_id())
    )
}

/// **THE ADVANCE WARNING for a shelf painted into a shared chat** — `None` when every advertised
/// offering plays right here (which is every DM, and a group whose whole shelf is
/// full-information).
///
/// A dimmed button with no explanation is a mystery, and a mystery reads as a broken bot. This is
/// the sentence that turns the dim row into a lesson plus a route: WHICH games are inert, WHY (the
/// shared-surface constraint, in the player's words, authored once in
/// [`shelf::ShelfBlock::why`]), the exact gesture that fixes it, and what still plays here.
///
/// ⚑ Every name and every key is READ OFF the shelf, which read them off
/// [`dreggnet_offerings::Offering::hidden_information`]. Nothing here names a game, so it cannot
/// name the wrong one when a game changes its declaration — including the case where ALL of them
/// do, which this says outright rather than pointing at an empty group shelf.
fn shelf_note_for(rows: &[ShelfEntry]) -> Option<String> {
    let blocked = shelf::blocked(rows);
    let first = blocked.first()?;
    let names: Vec<&str> = blocked.iter().map(|e| e.name()).collect();
    let routes: Vec<String> = blocked
        .iter()
        .map(|e| format!("/open {}", e.info.key))
        .collect();
    // ONE reason for the whole group of them: they are blocked for the same declared reason, so
    // repeating it per game would be noise. `why` names a game, so it takes the first — and the
    // list right before it says who else it covers.
    let mut note = format!(
        "🔒 Dimmed above, and refused if you press it here: {}. {} \
         To play: DM me and send {} — or /play there for the richer Mini App (Telegram allows \
         those in a private chat only).",
        shelf::name_list(&names),
        first
            .block
            .expect("a blocked row carries its block")
            .why(first.name()),
        routes.join(" · "),
    );
    let playable = shelf::playable(rows);
    if playable.is_empty() {
        // Not a hypothetical to leave unsaid: if every shipped game declares hidden information,
        // a group chat has NOTHING on the shelf, and the menu must say so instead of presenting a
        // wall of locks as if one of them might work.
        note.push_str(
            " Nothing else on the shelf plays in a group chat either — every game we ship keeps \
             per-player state, so a DM is where all of them play.",
        );
    } else {
        let live: Vec<&str> = playable.iter().map(|e| e.name()).collect();
        note.push_str(&format!(
            " Playable right here in the group: {}.",
            shelf::name_list(&live)
        ));
    }
    Some(note)
}

/// Select the only projection a Telegram message with this readership may
/// carry. The offering key is deliberately irrelevant: a personal RPG world
/// may be selected by identity at the storage/router layer, but its message is
/// still viewer-blind when the chat has multiple readers.
fn audience_for_message(shared: bool, viewer: &DreggIdentity) -> Audience {
    if shared {
        Audience::Shared
    } else {
        Audience::private(viewer.clone())
    }
}

/// The RESERVED host-level verify verb — re-exported here for the runtime and existing callers.
/// [`crate::verify_control`] owns its exact callback wire and standing button.
pub use crate::verify_control::TURN_VERIFY;

/// A metadata-preflighted ordinary Telegram document upload.
///
/// The route contains no bytes: the runtime obtains this value before calling Telegram `getFile`,
/// so an unknown operation, an ineligible shared-chat upload, or a declared oversize object is
/// refused without a download. [`TelegramHost::apply_operation`] re-checks the live descriptor,
/// shared eligibility, and actual length atomically on the host thread.
#[derive(Clone, Debug)]
pub struct TelegramOperationRoute {
    /// The offering owning the active surface.
    pub key: String,
    /// The chat-scoped offering session.
    pub session: SessionId,
    /// The authenticated Telegram actor's derived dregg identity.
    pub actor: DreggIdentity,
    /// Exact descriptor plus the effective ordinary-chat byte cap.
    pub policy: ChatBinaryOperationPolicy,
    /// Whether the authenticated update came from a multi-reader chat. Kept private so external
    /// callers cannot manufacture a DM-classified route around the shared-document gate.
    shared: bool,
    /// Exact authority- and state-head-bound route for a catalog game operation. Non-game
    /// offering operations retain their established direct host path.
    game_reference: Option<GameOperationRef>,
}

/// Result of applying one Telegram document operation at the chat-readership boundary.
///
/// A direct receipt is returned only to a single-reader/non-game route. A multi-reader game
/// route can return only the catalog's viewer-blind publication (or an explicit publication
/// failure with no receipt body); its raw operation name, fields, actor, payload and state heads
/// are therefore unrepresentable to the caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TelegramAppliedOperation {
    Direct(BinaryOperationReceipt),
    SharedGame(PublicGameReceipt),
    SharedGameUnpublished,
}

/// A frontend-neutral account of the game session currently addressed by a Telegram chat.
///
/// The concrete game keeps its own rules and state type. This is deliberately only the common
/// operation spine: exact `(offering, session)` address, audience boundary, currently presented
/// action/operation counts, and the live replay verdict. It is what `/status` renders across
/// Descent, the dungeon, the Dark Bazaar crawl, and the proof-assigned raid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TelegramGameStatus {
    /// Catalog route of the concrete game.
    pub key: String,
    /// Shared rule-family vocabulary from `dreggnet-catalog::game_spine`.
    pub kind: String,
    /// Exact host session handle. The offering key remains a separate part of the address.
    pub session: SessionId,
    /// Stable authority incarnation of the durable Telegram game host.
    pub host_incarnation: GameHostIncarnation,
    /// Monotone generation of this exact `(offering, session)` address.
    pub session_generation: u64,
    /// Whether Telegram selected the single-reader projection.
    pub private_projection: bool,
    /// Whether the game declares that its private projection may reveal player-only state.
    pub hidden_information: bool,
    /// Ordinary executor-refereed moves on the current projection.
    pub turn_affordances: usize,
    /// Exact names of the currently advertised opaque proof/attestation operations.
    pub proof_operations: Vec<String>,
    /// Exact names of the currently advertised read-only binary artifacts.
    pub artifacts: Vec<String>,
    /// The live offering verifier's result.
    pub verified: bool,
    /// Number of turns the verifier replayed.
    pub verified_turns: usize,
    /// The verifier's own account.
    pub verification_detail: String,
    /// Landed ordinary moves plus journaled binary operations after genesis.
    pub landed_steps: usize,
    /// Whether the host has a complete replay recipe for the live state. This does not by itself
    /// claim that the process has a durable store mounted.
    pub replay_recipe: bool,
    /// Most recent landed receipt that crossed the catalog's audited viewer-blind publication
    /// boundary in this host process. Raw execution receipts are never stored here.
    pub latest_public_receipt: Option<PublicGameReceipt>,
}

/// Counts of the three public action families a shared game surface currently offers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TelegramPublicGameAffordances {
    pub ordinary_turns: usize,
    pub shielded_operations: usize,
    pub read_only_artifacts: usize,
}

/// The only game-status object a multi-reader Telegram message may render.
///
/// This type deliberately cannot carry a raw session id, host incarnation, actor, operation or
/// artifact name, verification diagnostic, private result value, action payload, or state head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TelegramSharedGameStatus {
    pub kind: GameKind,
    pub verified: bool,
    pub verified_turns: usize,
    pub landed_steps: usize,
    pub affordances: TelegramPublicGameAffordances,
    pub replay_recipe: bool,
    pub latest_receipt: Option<PublicGameReceipt>,
}

/// A fail-closed refusal at Telegram's multi-reader status boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TelegramSharedGameStatusError {
    PrivateProjection,
    UnknownGameKind,
    InconsistentGameKind,
    InvalidReceiptBinding,
    InconsistentReceiptKind,
}

impl std::fmt::Display for TelegramSharedGameStatusError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("shared game status failed its viewer-blind consistency checks")
    }
}

impl std::error::Error for TelegramSharedGameStatusError {}

impl TelegramGameStatus {
    /// Reduce the host-rich inspection object to the no-viewer grammar used in a group or forum
    /// topic. A private projection or mismatched receipt refuses instead of being best-effort
    /// redacted after formatting.
    pub fn shared_projection(
        &self,
    ) -> Result<TelegramSharedGameStatus, TelegramSharedGameStatusError> {
        if self.private_projection {
            return Err(TelegramSharedGameStatusError::PrivateProjection);
        }
        let kind = game_kind(&self.key).ok_or(TelegramSharedGameStatusError::UnknownGameKind)?;
        if kind.as_str() != self.kind {
            return Err(TelegramSharedGameStatusError::InconsistentGameKind);
        }
        if let Some(receipt) = &self.latest_public_receipt {
            receipt
                .validate()
                .map_err(|_| TelegramSharedGameStatusError::InvalidReceiptBinding)?;
            if receipt.kind != kind {
                return Err(TelegramSharedGameStatusError::InconsistentReceiptKind);
            }
        }
        Ok(TelegramSharedGameStatus {
            kind,
            verified: self.verified,
            verified_turns: self.verified_turns,
            landed_steps: self.landed_steps,
            affordances: TelegramPublicGameAffordances {
                ordinary_turns: self.turn_affordances,
                shielded_operations: self.proof_operations.len(),
                read_only_artifacts: self.artifacts.len(),
            },
            replay_recipe: self.replay_recipe,
            latest_receipt: self.latest_public_receipt.clone(),
        })
    }
}

/// A refusal at the ordinary Telegram operation attachment boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TelegramOperationError {
    /// Documents are chat messages, so a group upload would publish the receipt
    /// (and, for selective openings, its opening material) to every reader.
    PrivateChatRequired,
    /// No playable offering is active in this chat.
    NoSession,
    /// A multi-reader game operation failed. Host/verifier diagnostics stay on the private audit
    /// side of the adapter rather than becoming a group message.
    SharedGameRefused,
    /// The host could not discover or invoke the addressed operation.
    Refused(String),
}

impl std::fmt::Display for TelegramOperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PrivateChatRequired => write!(
                f,
                "proof receipts are accepted only in a private bot chat; a Telegram group document is visible to every member (the sole exception is the exact live private-raid assignment proof, whose verifier binds session, roster, and claimant)"
            ),
            Self::NoSession => write!(
                f,
                "no offering is active in this chat; open one before attaching a receipt"
            ),
            Self::SharedGameRefused => write!(
                f,
                "the shared game operation was refused; no private verifier diagnostic was published"
            ),
            Self::Refused(reason) => write!(f, "{reason}"),
        }
    }
}

impl std::error::Error for TelegramOperationError {}

/// The sentinel "active key" a chat carries while it is showing the offerings menu (not yet
/// playing an offering). Not a registered offering key, so it never collides.
const MENU_KEY: &str = "@menu";

/// **How long an ARMED free-text slot stays armed.** Pressing a `wants_text` affordance arms the
/// chat's text slot and the NEXT plain message fills it. Without an expiry that arm is immortal:
/// a chat that armed a slot and then walked away has every later message swallowed into an
/// offering forever, with no input able to clear it (a re-present clears the arm, but a chat
/// whose surface never moves never re-presents). A bounded arm cannot wedge a chat; /cancel
/// clears it immediately.
pub const TEXT_ARM_TTL: std::time::Duration = std::time::Duration::from_secs(15 * 60);

/// A free-text affordance a surface has ARMED, with the moment it was armed (see
/// [`TEXT_ARM_TTL`]).
#[derive(Debug, Clone)]
struct ArmedText {
    action: Action,
    at: std::time::Instant,
}

impl ArmedText {
    fn now(action: Action) -> ArmedText {
        ArmedText {
            action,
            at: std::time::Instant::now(),
        }
    }

    fn expired(&self) -> bool {
        self.at.elapsed() > TEXT_ARM_TTL
    }
}

/// A unit of work run ON the host's owning thread, against the live [`OfferingHost`].
type HostJob = Box<dyn FnOnce(&mut OfferingHost) + Send + 'static>;

/// **A thread-confined [`OfferingHost`] handle** — the `dreggnet-web` [`HostThread`] pattern reused
/// for Telegram. The host owns `!Send` offering sessions, so it lives on ONE owning thread; every
/// access is a job shipped to it and only the (`Send`) result crosses back. The handle is just a
/// channel sender, so it is `Send + Sync`.
pub struct HostThread {
    jobs: SyncSender<HostJob>,
}

impl HostThread {
    /// Spawn the owning thread and BUILD the host on it (`build` runs on the thread, so the
    /// registered offerings + their sessions are born there and never cross a thread boundary).
    pub fn spawn(build: impl FnOnce() -> OfferingHost + Send + 'static) -> HostThread {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("telegram-offering-host".to_string())
            .spawn(move || {
                let mut host = build();
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .expect("spawn the telegram offering host thread");
        HostThread { jobs }
    }

    /// Fallible production form of [`spawn`](Self::spawn). The `!Send` host is
    /// still constructed on its owning thread, while a one-shot startup
    /// channel reports durable-store failure before the handle is published.
    pub fn try_spawn(
        build: impl FnOnce() -> Result<OfferingHost, String> + Send + 'static,
    ) -> Result<HostThread, String> {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        let (started, startup) = sync_channel::<Result<(), String>>(1);
        std::thread::Builder::new()
            .name("telegram-offering-host".to_string())
            .spawn(move || {
                let mut host = match build() {
                    Ok(host) => host,
                    Err(error) => {
                        let _ = started.send(Err(error));
                        return;
                    }
                };
                if started.send(Ok(())).is_err() {
                    return;
                }
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .map_err(|error| format!("could not spawn Telegram offering-host thread: {error}"))?;
        startup
            .recv()
            .map_err(|_| "Telegram offering-host thread exited during startup".to_string())??;
        Ok(HostThread { jobs })
    }

    /// Run `f` against the host on the owning thread and hand back its (`Send`) result. Blocks the
    /// caller until the job returns — one short, CPU-bound offering turn.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |host| {
                let _ = tx.send(f(host));
            }))
            .expect("the telegram offering host thread is alive");
        rx.recv()
            .expect("the telegram offering host thread answered")
    }
}

/// A unit of work run ON the per-identity RPG worlds' owning thread, against the live
/// [`PlayerWorlds`] registry.
type PlayerJob = Box<dyn FnOnce(&mut PlayerWorlds) + Send + 'static>;

/// **A thread-confined [`PlayerWorlds`] handle** — the [`HostThread`] pattern for the per-identity
/// RPG worlds. A [`PlayerWorlds`] owns one `!Send` [`OfferingHost`] per derived identity, so it
/// lives on ONE owning thread and every access is a job shipped to it; only the (`Send`) result
/// crosses back. The handle is just a channel sender — `Send + Sync`.
pub struct PlayerHostThread {
    jobs: SyncSender<PlayerJob>,
}

impl PlayerHostThread {
    /// Spawn the owning thread and BUILD the registry on it (`build` runs on the thread, so every
    /// per-identity host and its `!Send` sessions are born there and never cross a boundary).
    pub fn spawn(build: impl FnOnce() -> PlayerWorlds + Send + 'static) -> PlayerHostThread {
        let (jobs, rx) = sync_channel::<PlayerJob>(64);
        std::thread::Builder::new()
            .name("telegram-player-worlds".to_string())
            .spawn(move || {
                let mut worlds = build();
                while let Ok(job) = rx.recv() {
                    job(&mut worlds);
                }
            })
            .expect("spawn the telegram player-worlds thread");
        PlayerHostThread { jobs }
    }

    /// Run `f` against the registry on the owning thread and hand back its (`Send`) result.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut PlayerWorlds) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |worlds| {
                let _ = tx.send(f(worlds));
            }))
            .expect("the telegram player-worlds thread is alive");
        rx.recv()
            .expect("the telegram player-worlds thread answered")
    }
}

/// **Why an open did not happen** — the host's refusal, or this SURFACE's own refusal to host the
/// offering at all.
#[derive(Debug)]
pub enum OpenError {
    /// The [`OfferingHost`] refused (unknown key, a policy gate, a failed deploy / resume).
    Host(HostError),
    /// The durable game host could not establish or recover the exact
    /// incarnation/session-generation authority for this address.
    Epoch(String),
    /// **The chat is SHARED and the offering hides per-player state**
    /// ([`dreggnet_offerings::Offering::hidden_information`]). A group / forum-topic session paints
    /// ONE message that every member reads (a re-present EDITS it in place), so there is no way to
    /// serve a per-viewer projection there without serving it to the whole room. Nothing was
    /// opened; `why` is the legible redirect the player is shown.
    HiddenInSharedChat {
        /// The offering that will not be hosted here.
        key: String,
        /// The human redirect (DM / Mini App) — this is what the player reads.
        why: String,
    },
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenError::Host(e) => write!(f, "{e}"),
            OpenError::Epoch(e) => write!(f, "{e}"),
            OpenError::HiddenInSharedChat { why, .. } => write!(f, "{why}"),
        }
    }
}

impl std::error::Error for OpenError {}

impl From<HostError> for OpenError {
    fn from(e: HostError) -> Self {
        OpenError::Host(e)
    }
}

impl OpenError {
    /// The human reply for a `/open <key>` that did not open. A host failure keeps the familiar
    /// "Cannot open <key>: …" shape; a shared-chat refusal IS its own message (it is a redirect,
    /// not a malfunction, and prefixing it would bury the instruction).
    pub fn human(&self, key: &str) -> String {
        match self {
            OpenError::Host(e) => format!("Cannot open {key}: {e}"),
            OpenError::Epoch(e) => format!("Cannot bind {key} to durable game authority: {e}"),
            OpenError::HiddenInSharedChat { why, .. } => why.clone(),
        }
    }
}

/// The outcome of a [`TelegramHost::press`] — a button press routed through the host.
#[derive(Debug)]
pub enum HostPress {
    /// A menu press opened the named offering in the chat (its surface is now presented).
    Opened(String),
    /// A play press advanced the active offering by one real turn (the [`Outcome`] is the
    /// substrate's — a real landed receipt, or a real executor refusal / anti-ghost).
    Advanced {
        /// The offering key the press advanced.
        key: String,
        /// The real substrate outcome.
        outcome: Outcome,
    },
    /// A [`TURN_VERIFY`] press re-verified the active offering's committed chain and hands back
    /// the REAL [`VerifyReport`] (`None` if the offering exposes no verifier) — verify-don't-trust
    /// routed through the same router every play press takes. Read-only: the presented surface is
    /// untouched, so the next press still resolves against the live keyboard.
    Verified {
        /// The offering key whose chain was re-checked.
        key: String,
        /// The re-verification report, replayed just now on the host thread.
        report: Option<VerifyReport>,
    },
    /// A press SELECTED a free-text affordance (one whose [`Action::wants_text`] is set, e.g. a
    /// document INSERT/set-title, a Hermes prompt, a names register, a compute settle) — it ARMS
    /// the chat's text slot instead of advancing (a text affordance carries no content on a bare
    /// press). The NEXT plain-text message the chat receives is routed into THIS armed affordance
    /// as its [`Action::text`] payload ([`TelegramHost::press_text`]). Nothing committed yet — the
    /// arm is a pure selection.
    TextArmed {
        /// The offering key the armed affordance belongs to.
        key: String,
        /// The armed affordance (its `{turn, arg}` + human label — the text slot now selected).
        action: Action,
    },
    /// A menu press asked for a HIDDEN-INFORMATION offering in a SHARED chat, and this surface
    /// will not host one ([`OpenError::HiddenInSharedChat`]). Nothing opened, nothing rendered;
    /// `why` is the legible redirect to a DM / the Mini App.
    OpenRefused {
        /// The offering that will not be hosted here.
        key: String,
        /// The human redirect the presser is shown.
        why: String,
    },
    /// The press did not match any affordance currently on the chat's surface — an honest
    /// frontend-level refusal, BEFORE the substrate (the executor is never reached).
    NotOffered,
    /// No session is active in that chat (nothing was opened / presented yet).
    NoSession,
}

/// **The multi-offering Telegram host.** Bundles the thread-confined [`OfferingHost`] (the registry
/// of offerings + their live sessions) with the [`TelegramFrontend`] (the affordance-renderer over
/// the injected transport), and routes chat button-presses to the right `(offering, session)`.
///
/// Generic over the injected [`Transport`] `T`, so the whole thing drives token- and network-free
/// with [`crate::transport::MockTransport`] in a test and over a live `RawBotApi` in production.
pub struct TelegramHost<T: Transport> {
    /// The bot master secret — the root of every user's derived identity (and of the council
    /// electorate this host registers).
    bot_secret: [u8; 32],
    /// The offering registry, confined to its owning thread. The SHARED tables — the games and
    /// service offerings — live here (a council with one voter per host is not a council).
    host: HostThread,
    /// The per-identity RPG worlds, confined to their own owning thread. The eight [`is_rpg_key`]
    /// surfaces (trade / inventory / craft / …) are per-player by nature, so every RPG-key session
    /// operation routes to the PRESSER's own [`OfferingHost`] here
    /// ([`run_offering`](Self::run_offering)), keyed by their derived identity — two Telegram users
    /// therefore have ISOLATED inventories. The shared-layer form of the split Discord already runs.
    players: PlayerHostThread,
    /// Deployment incarnation and monotone per-address game generations.
    /// This is frontend routing authority; concrete game state remains owned
    /// by `host`.
    game_epochs: GameEpochLedger,
    /// The Telegram affordance-renderer over the transport (records what each chat last presented).
    frontend: TelegramFrontend<T>,
    /// **The chat's MOST RECENT surface's offering** (or [`MENU_KEY`] while browsing) — keyed by
    /// the chat-scoped [`SessionId`].
    ///
    /// This is no longer "the one offering this chat may play": each offering now owns its OWN
    /// message in the chat ([`TelegramFrontend::surface_id`]), so several coexist and a press
    /// routes by the message it was pressed on. `active` is the fallback for a press that names no
    /// message (a `/act` / `/verify` command, a Mini App round-trip) and the referent of "this
    /// chat's session" for the single-offering UX — which is exactly what it always meant in a
    /// chat with one offering open.
    active: HashMap<SessionId, String>,
    /// Latest identity-free, viewer-blind receipt publication for each live game address. This
    /// cache is presentation state, not execution authority; after restart it remains empty until
    /// a new command lands, while the durable game journal itself remains intact.
    public_game_receipts: HashMap<(String, SessionId), PublicGameReceipt>,
    /// **The chat's ARMED free-text affordance, if one is selected.** A press on a
    /// [`Action::wants_text`] affordance records it here (see [`HostPress::TextArmed`]); the next
    /// plain-text message routes into it ([`Self::pending_text_action`] / [`Self::press_text`]).
    /// This is the gate that keeps free-text capture DELIBERATE — with nothing armed, a chat's
    /// plain messages are ordinary chatter (never swallowed into an offering). Cleared on any
    /// advance / re-present (the surface moved on). Keyed by SURFACE
    /// ([`TelegramFrontend::surface_id`]), so arming a document's text slot does not disarm the
    /// tug board open beside it in the same chat. Each arm carries the moment it was made and
    /// expires after [`TEXT_ARM_TTL`], so a forgotten arm cannot swallow a chat's messages
    /// forever.
    armed: HashMap<SessionId, ArmedText>,
    /// **Why the last present painted nothing** (`None` = it really was sent). A surface that
    /// cannot be projected or cannot be sent used to vanish silently: `open` answered `Ok`, the
    /// ack said "Opened …", and the chat got no message at all — the single most convincing way
    /// for a working bot to look dead. Recorded here and taken by the command surface
    /// ([`Self::take_paint_failure`]), which answers with it.
    last_paint_failure: Option<String>,
    /// The Mini App base URL (the public funnel), when the deploy arms the `web_app` launch
    /// tier ([`Self::with_webapp_base`]). `None` = launch buttons off; the inline-button tier
    /// is unaffected either way.
    webapp_base: Option<String>,
    /// Retains the exact configured private-Bazaar registry and durable XP
    /// adapter for as long as this Telegram host is live. The ordinary build
    /// has no fabricated deployment and leaves this absent.
    #[cfg(feature = "private-bazaar-live")]
    private_bazaar_deployment: Option<dreggnet_catalog::PrivateBazaarLiveDeployment>,
}

impl<T: Transport> TelegramHost<T> {
    /// Build a host over the FULL shared catalog (the same 23 offerings every frontend exposes —
    /// see [`telegram_default_host`]), sending through `transport`, with the council electorate
    /// derived from `council_member_uids` (Telegram user ids whose derived identities are
    /// registered as council members — so those users can really vote).
    pub fn new(bot_secret: [u8; 32], transport: T, council_member_uids: &[TelegramUserId]) -> Self {
        // Derive the council electorate on THIS thread (a pure derivation → `[u8; 32]` pubkeys,
        // Send), then move it into the host-thread build closure. The member identity a proposal /
        // vote is attributed to is `hex(pubkey)` — exactly the identity `identity(uid)` derives, so
        // a Telegram member's press matches the registered council member.
        let members: Vec<[u8; 32]> = council_member_uids
            .iter()
            .map(|uid| TelegramCipherclerk::derive(&bot_secret, *uid).public_key_bytes())
            .collect();
        let host = HostThread::spawn(move || telegram_default_host(members));
        TelegramHost {
            bot_secret,
            host,
            players: PlayerHostThread::spawn(PlayerWorlds::new),
            game_epochs: GameEpochLedger::in_memory_random()
                .expect("operating-system randomness is available for the game host incarnation"),
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            public_game_receipts: HashMap::new(),
            armed: HashMap::new(),
            last_paint_failure: None,
            webapp_base: None,
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        }
    }

    /// Build the full Telegram catalog plus one explicitly configured private
    /// Bazaar raid. Generic `/offerings` and press routing then open and drive
    /// the same payload-free hosted lifecycle as web; policy and durability
    /// stay in `deployment`, never in callback data.
    #[cfg(feature = "private-bazaar-live")]
    pub fn with_private_bazaar(
        bot_secret: [u8; 32],
        transport: T,
        council_member_uids: &[TelegramUserId],
        deployment: dreggnet_catalog::PrivateBazaarLiveDeployment,
    ) -> Self {
        let members: Vec<[u8; 32]> = council_member_uids
            .iter()
            .map(|uid| TelegramCipherclerk::derive(&bot_secret, *uid).public_key_bytes())
            .collect();
        let mounted = deployment.clone();
        let host = HostThread::spawn(move || {
            dreggnet_catalog::full_catalog_host_with_private_bazaar(
                // Live day binding, as `telegram_default_host` — see `arm_todays_descent_day`.
                &CatalogConfig::live(members),
                &mounted,
            )
            // Bounded session lifecycle, as `telegram_default_host` — never born unbounded.
            .with_policy(resolve_telegram_policy(), SystemClock)
        });
        TelegramHost {
            bot_secret,
            host,
            players: PlayerHostThread::spawn(PlayerWorlds::new),
            game_epochs: GameEpochLedger::in_memory_random()
                .expect("operating-system randomness is available for the game host incarnation"),
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            public_game_receipts: HashMap::new(),
            armed: HashMap::new(),
            last_paint_failure: None,
            webapp_base: None,
            private_bazaar_deployment: Some(deployment),
        }
    }

    #[cfg(feature = "private-bazaar-live")]
    pub fn private_bazaar_deployment(
        &self,
    ) -> Option<&dreggnet_catalog::PrivateBazaarLiveDeployment> {
        self.private_bazaar_deployment.as_ref()
    }

    /// Build a host over a caller-provided offering registry (the offerings are registered inside
    /// `build`, which runs on the owning thread), with an IN-MEMORY per-identity RPG worlds
    /// registry. Lets a deployment register its own shared offering set; the RPG worlds stay
    /// in-memory (the tests' path — see [`with_hosts`](Self::with_hosts) for the durable pair).
    pub fn with_host(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
    ) -> Self {
        Self::with_hosts(bot_secret, transport, build, PlayerWorlds::new)
    }

    /// Build a host over a caller-built shared registry AND a caller-built per-identity RPG worlds
    /// registry — the durable production seam (the bin passes the `TELEGRAM_SESSION_DIR`-resolved
    /// pair, so both the shared game sessions and each player's RPG world survive a restart by
    /// move-log replay). Both `build` closures run on their own owning threads.
    pub fn with_hosts(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
    ) -> Self {
        let game_epochs = GameEpochLedger::in_memory_random()
            .expect("operating-system randomness is available for the game host incarnation");
        Self::with_hosts_and_game_epochs(bot_secret, transport, build, build_players, game_epochs)
    }

    /// Build the production host pair with caller-supplied durable game epoch
    /// custody. The ledger must be opened before the host threads are spawned;
    /// corrupt or missing authority state is therefore a boot failure, not an
    /// in-memory downgrade.
    pub fn with_hosts_and_game_epochs(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
        game_epochs: GameEpochLedger,
    ) -> Self {
        TelegramHost {
            bot_secret,
            host: HostThread::spawn(build),
            players: PlayerHostThread::spawn(build_players),
            game_epochs,
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            public_game_receipts: HashMap::new(),
            armed: HashMap::new(),
            last_paint_failure: None,
            webapp_base: None,
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        }
    }

    /// Fallible production constructor for a durable shared host.
    ///
    /// `OfferingHost` is intentionally `!Send`, so `build` executes on the
    /// owning thread. Durable-store initialization is acknowledged over a
    /// startup channel before this returns; an error cannot degrade to an
    /// empty in-memory host hidden behind a live Telegram handle.
    pub fn try_with_hosts_and_game_epochs(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> Result<OfferingHost, String> + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
        game_epochs: GameEpochLedger,
    ) -> Result<Self, String> {
        Ok(TelegramHost {
            bot_secret,
            host: HostThread::try_spawn(build)?,
            players: PlayerHostThread::spawn(build_players),
            game_epochs,
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            public_game_receipts: HashMap::new(),
            armed: HashMap::new(),
            last_paint_failure: None,
            webapp_base: None,
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        })
    }

    /// Fallible production constructor for a host whose build closure already
    /// registered and boot-resumed this exact private Bazaar deployment. The
    /// retained handle keeps its worker registry and durable consequence
    /// adapter reachable after the owning host thread starts.
    #[cfg(feature = "private-bazaar-live")]
    pub fn try_with_private_bazaar_hosts_and_game_epochs(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> Result<OfferingHost, String> + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
        game_epochs: GameEpochLedger,
        deployment: dreggnet_catalog::PrivateBazaarLiveDeployment,
    ) -> Result<Self, String> {
        Ok(TelegramHost {
            bot_secret,
            host: HostThread::try_spawn(build)?,
            players: PlayerHostThread::spawn(build_players),
            game_epochs,
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            public_game_receipts: HashMap::new(),
            armed: HashMap::new(),
            last_paint_failure: None,
            webapp_base: None,
            private_bazaar_deployment: Some(deployment),
        })
    }

    /// **Route a `(key, session)`-scoped host job to the host that OWNS it for `viewer`.** An
    /// [`is_rpg_key`] offering runs against the viewer's own per-identity RPG world (their isolated
    /// inventory); everything else — the shared games, party, and services — runs against the ONE catalog
    /// host. This ONE routing decision is why two Telegram users never share an inventory while a
    /// council / tug stays a single shared table.
    fn run_offering<R: Send + 'static>(
        &self,
        key: &str,
        viewer: &DreggIdentity,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        if is_rpg_key(key) {
            let id = viewer.0.clone();
            self.players.run(move |worlds| f(worlds.host_mut(&id)))
        } else {
            self.host.run(f)
        }
    }

    /// **Arm the Mini App launch tier**: `base` is the public HTTPS funnel the web `/tg` Mini
    /// App routes are served from ([`crate::webapp::webapp_base_from_env`] resolves it in the
    /// bin). With a base set, a DM's presented offering surface carries a trailing
    /// "🕹 Play in the app" `web_app` row deep-linking THAT offering + session, and
    /// [`present_play_menu`](Self::present_play_menu) (the `/play` command) works. An empty
    /// base disarms. Group chats never get `web_app` buttons — Telegram refuses them there
    /// ([`crate::webapp::web_app_allowed`]); the inline-button tier is their (full) surface.
    pub fn with_webapp_base(mut self, base: impl Into<String>) -> Self {
        let base = base.into().trim().trim_end_matches('/').to_string();
        self.webapp_base = (!base.is_empty()).then_some(base);
        self
    }

    /// The armed Mini App base URL, if any.
    pub fn webapp_base(&self) -> Option<&str> {
        self.webapp_base.as_deref()
    }

    /// **The FULL registry** — every mounted offering, advertised or not. The inventory view; a
    /// MENU wants [`list_advertised_offerings`](Self::list_advertised_offerings).
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
    }

    /// **The SHELF** — the offerings on `dreggnet_catalog::SHIPPED_KEYS`. Everything a Telegram
    /// user browses (`/offerings`, `/play`) paints THIS, and presses resolve against it, so the
    /// painted button and the index it carries can never disagree.
    ///
    /// An offering that is off the shelf is still openable with `/open <key>` — the ship list is
    /// what we advertise, not what we allow.
    pub fn list_advertised_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_advertised_offerings())
    }

    /// **Does the offering under `key` hide per-viewer state?** — the declaration
    /// ([`dreggnet_offerings::Offering::hidden_information`]) this adapter's shared-chat rules are
    /// built on, answered without a session. `None` for an unregistered key.
    ///
    /// Exposed so a caller (and the crate's tests) can read the same signal the shelf and the open
    /// gate read, instead of re-listing which games are which — a list that goes stale the first
    /// time a game changes its mind.
    pub fn hidden_information(&self, key: &str) -> Option<bool> {
        let key = key.to_string();
        self.host.run(move |h| h.hidden_information(&key))
    }

    /// **The advertised shelf for THIS chat, with the audience gate applied** — one row per shipped
    /// offering, each carrying its stable full-list index and whether this chat may host it
    /// ([`dreggnet_offerings::shelf::advertised_shelf`]).
    ///
    /// A group / forum topic is a shared surface, so a row declaring hidden information comes back
    /// blocked; a DM is single-reader and nothing is blocked there. Computed in ONE hop to the
    /// host's owning thread so the whole shelf is a consistent reading.
    pub fn chat_shelf(&self, chat_id: ChatId, topic: Option<i64>) -> Vec<ShelfEntry> {
        let surface = ShelfSurface::shared_if(ChatKind::classify(chat_id, topic).is_collective());
        self.host.run(move |h| shelf::advertised_shelf(h, surface))
    }

    /// **The advance warning this chat's shelf needs** — `None` when every shipped offering plays
    /// here. Naming which rows are inert, why, and the gesture that fixes it (the private
    /// `shelf_note_for` authors the copy).
    ///
    /// `/offerings` folds it into the menu message; `/help` appends it, because a help text that
    /// says "`/open tug`" in a group is a route to a refusal.
    pub fn shelf_note(&self, chat_id: ChatId, topic: Option<i64>) -> Option<String> {
        shelf_note_for(&self.chat_shelf(chat_id, topic))
    }

    /// Derive `uid`'s frontend-agnostic dregg identity (the presser attribution).
    pub fn identity(&self, uid: TelegramUserId) -> dreggnet_offerings::DreggIdentity {
        self.frontend.identity(uid)
    }

    /// The council-member public key a Telegram user id derives to — register these as a
    /// council electorate ([`CatalogConfig::council_members`]) so those users can vote.
    /// Pure; no host needed.
    pub fn council_member_pubkey(bot_secret: &[u8; 32], uid: TelegramUserId) -> [u8; 32] {
        TelegramCipherclerk::derive(bot_secret, uid).public_key_bytes()
    }

    /// Borrow the frontend (e.g. a test's [`crate::transport::MockTransport`] via
    /// [`TelegramFrontend::transport`], or the last-presented surface of a chat).
    pub fn frontend(&self) -> &TelegramFrontend<T> {
        &self.frontend
    }

    /// **Does `(chat, key)` already have a live surface MESSAGE in this process?** — what the
    /// command surface needs to know to answer honestly when a re-open will be an in-place edit
    /// of a message the user may have scrolled far past (a collective chat, where the ONE shared
    /// message is deliberate). In a DM an open reposts, so this is only advisory there.
    pub fn has_live_surface(&self, chat_id: ChatId, topic: Option<i64>, key: &str) -> bool {
        let surface = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
        self.frontend
            .surface_slot(&surface)
            .is_some_and(|slot| slot.message_id.is_some())
    }

    /// The offering currently active in the chat session `sid` (`None` if nothing is open, or the
    /// sentinel while the offerings menu is showing).
    pub fn active_offering(&self, sid: &SessionId) -> Option<&str> {
        self.active
            .get(sid)
            .map(String::as_str)
            .filter(|k| *k != MENU_KEY)
    }

    /// Inspect the active game through the shared, frontend-neutral game-session spine.
    ///
    /// This is an explicit operation (`/status`), so replay verification happens on demand rather
    /// than on every render. The audience passed into the spine is derived from who can read the
    /// Telegram message: DMs may select one private reader; groups never carry a viewer identity.
    /// No concrete game transition or legality rule is duplicated here.
    pub fn game_status(
        &self,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<TelegramGameStatus, String> {
        let session = TelegramFrontend::<T>::session_id(chat_id, topic);
        let key = self
            .active_offering(&session)
            .ok_or_else(|| "No game session is active in this chat.".to_string())?
            .to_string();
        if game_kind(&key).is_none() {
            return Err(format!(
                "`{key}` uses the offering protocol but is not a game surface; /verify still checks its committed record."
            ));
        }
        let actor = self.frontend.identity(uid);
        let audience = if ChatKind::classify(chat_id, topic).is_collective() {
            GameAudience::Shared
        } else {
            // The Telegram update authenticates the platform user; the common spine records only
            // that this adapter asserted the derived viewer label, not a cryptographic claim that
            // the label is bound into every underlying binary receipt.
            GameAudience::AssertedPrivate(actor.clone())
        };
        let reference = self
            .game_epochs
            .bound_session(&key, &session)
            .map_err(|error| error.to_string())?;
        let host_incarnation = self.game_epochs.host_incarnation();
        let session_generation = self
            .game_epochs
            .current_generation(&key, &session)
            .map_err(|error| error.to_string())?;
        let latest_public_receipt = self
            .public_game_receipts
            .get(&(key.clone(), session.clone()))
            .cloned();
        let status = {
            let routed_key = key.clone();
            self.run_offering(&key, &actor, move |host| {
                inspect_bound_game_session(
                    host,
                    host_incarnation,
                    session_generation,
                    reference,
                    &audience,
                )
                .map(|view| {
                    let mut turn_affordances = 0usize;
                    let mut proof_operations = Vec::new();
                    for affordance in &view.affordances {
                        match affordance {
                            GameAffordance::Turn { .. } => turn_affordances += 1,
                            GameAffordance::Operation { reference, .. } => {
                                proof_operations.push(reference.operation.clone());
                            }
                        }
                    }
                    TelegramGameStatus {
                        key: routed_key,
                        kind: view.kind.as_str().to_string(),
                        session: view.session.session_id().clone(),
                        host_incarnation,
                        session_generation,
                        private_projection: view.projection.private,
                        hidden_information: view.projection.hidden_information,
                        turn_affordances,
                        proof_operations,
                        artifacts: view
                            .artifacts
                            .iter()
                            .map(|artifact| artifact.reference.artifact.clone())
                            .collect(),
                        verified: view.verification.verified,
                        verified_turns: view.verification.turns,
                        verification_detail: view.verification.detail,
                        landed_steps: view.landed_steps,
                        replay_recipe: view.replay_journal_present,
                        latest_public_receipt,
                    }
                })
            })
        };
        // The derived identity participates only in audience/routing selection. Host-rich
        // diagnostics remain available to a DM; a multi-reader `/status` must cross
        // `TelegramGameStatus::shared_projection`, which cannot carry them.
        status.map_err(|error| error.to_string())
    }

    /// **Present the `/offerings` control message** in `chat_id` — a message whose inline keyboard
    /// is one button per ADVERTISED offering (a press opens that offering in the chat). Records the
    /// chat as "browsing the menu". Returns the chat-scoped [`SessionId`] and, if the send
    /// FAILED, the transport's own reason — so the command surface can say so instead of
    /// answering nothing at all.
    ///
    /// ⚑ The shelf is `dreggnet_catalog::SHIPPED_KEYS`; everything else stays openable with
    /// `/open <key>`.
    ///
    /// ⚑ **In a GROUP the shelf is HONEST BEFORE THE PRESS.** A hidden-information offering cannot
    /// be hosted on a shared surface ([`hidden_in_shared_chat`](Self::hidden_in_shared_chat)), so
    /// its row is painted INERT (`enabled: false` → a dim [`crate::api::LOCK_GLYPH`] label) and
    /// [`shelf_note`](Self::shelf_note) says why and where to go instead. It is not FILTERED: a
    /// game missing from the menu reads as one that does not exist, while a dimmed one teaches the
    /// constraint. The row keeps its full-list index and its `callback_data`, so pressing it
    /// anyway still reaches the SAME refusal it always did — this adds the warning, not the gate.
    pub fn present_offerings_menu_result(
        &mut self,
        chat_id: ChatId,
        topic: Option<i64>,
    ) -> (SessionId, Option<String>) {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        // ⚑ PAINT FROM THE FULL LIST, SKIP THE UNADVERTISED, KEEP THE FULL-LIST INDEX. A button's
        // callback arg is a POSITION, and the press router resolves it against this same full
        // list — so filtering the list before enumerating would renumber every button and make an
        // in-flight press from an older keyboard open the WRONG offering. Skipping instead keeps
        // every index it ever minted valid, which also means a callback captured before an
        // offering left the shelf still opens exactly what it always did. Unlisted, not deleted.
        //
        // `advertised_shelf` does exactly that AND takes the audience verdict per row, so the two
        // filters stay visibly separate: the ROWS are the ship list, the LIVENESS is the shelf
        // gate. Same reason the index is the full-list one — this gate reshapes the shelf PER
        // CHAT, which is precisely the renumbering hazard a stable index exists to survive.
        let rows = self.chat_shelf(chat_id, topic);
        let actions: Vec<Action> = rows
            .iter()
            .map(|entry| {
                let label = match entry.block {
                    None => format!("▶ Play {}", entry.info.title),
                    // The presentation layer prepends the lock glyph to any `!enabled` label (so
                    // 🔒 stands where ▶ stands on a live row), and this carries the one thing the
                    // glyph cannot: that there IS a place this works and it is not here. The SHORT
                    // name, not the full tagline — a row whose whole job is to say "not here" must
                    // not bury that under a sentence of ad copy.
                    Some(block) => format!("Play {} — {}", entry.name(), block.tag()),
                };
                Action::new(
                    label,
                    TURN_OPEN,
                    i64::try_from(entry.catalog_index)
                        .expect("the bounded offering catalog fits the callback wire"),
                    entry.live(),
                )
            })
            .collect();
        // Descent really is in this catalog now, alongside the dungeon, the honestly-labelled
        // Dark Bazaar crawl and the proof-assigned raid. They share the game-session protocol,
        // not a second Telegram rule engine.
        let continuation = if self.webapp_base.is_some() {
            "Open a session here with the buttons below. In a DM, /play opens that same addressed game in the richer Mini App surface."
        } else {
            "Open a session here with the buttons below; the inline surface is fully playable without a web view."
        };
        let mut children = vec![
            ViewNode::Text(dreggnet_catalog::flagship_pointer().to_string()),
            ViewNode::Text(
                "One addressed session and receipt protocol; different games keep their own rulebooks, proof systems, and mood."
                    .to_string(),
            ),
            ViewNode::Text(dreggnet_catalog::shelf_intro().to_string()),
            ViewNode::Text(continuation.to_string()),
        ];
        // A dim button alone is a mystery. The note names which rows are inert, why, and the ONE
        // gesture that fixes it — derived from the shelf, so it cannot name the wrong games.
        if let Some(note) = shelf_note_for(&rows) {
            children.push(ViewNode::Text(note));
        }
        let surface = Surface(ViewNode::Section {
            title: "🧪 Dregg games & operations".to_string(),
            tag: "accent".to_string(),
            children,
        });
        // The menu gets its OWN surface too ([`MENU_KEY`] is not a registered offering key, so it
        // never collides). That keeps the menu message live and pressable AFTER an offering is
        // opened beside it — pressing it again opens a SECOND offering, instead of the press being
        // read as a stale move on whatever was opened last.
        let menu_surface = TelegramFrontend::<T>::surface_id(chat_id, topic, MENU_KEY);
        self.frontend.spin_session(menu_surface.clone());
        // `/offerings` is an EXPLICIT request for the menu right now, so it must post a fresh
        // message at the bottom of the chat. Editing the previous menu message in place — which
        // is what a re-present does, and what this used to do — leaves a long chat with NO
        // visible response at all: the edit lands wherever the old menu scrolled to, and the
        // command itself sends no reply. That is the whole "menus completely break" experience.
        self.frontend.repost_next(&menu_surface);
        // The FALLIBLE present, so a send that fails is REPORTED. `Frontend::present` is
        // infallible by signature and swallows the error into `last_send_error`, which no
        // command surface ever read — so an over-long surface, a refused callback payload or a
        // Bot API error made `/offerings` reply absolutely nothing and look like a dead bot,
        // while the audit still recorded the command as "routed". Silence is the one answer a
        // command must never give.
        let sent = self
            .frontend
            .present_result(&menu_surface, &surface, &actions);
        self.active.insert(sid.clone(), MENU_KEY.to_string());
        (sid, sent.err().map(|e| e.to_string()))
    }

    /// [`present_offerings_menu_result`](Self::present_offerings_menu_result) discarding the
    /// send outcome — for callers that only want the chat's session id.
    pub fn present_offerings_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> SessionId {
        self.present_offerings_menu_result(chat_id, topic).0
    }

    /// **Present the `/play` Mini App launch menu** in `chat_id` — one `web_app` button per
    /// registered offering, each opening the rich web surface for that offering at this chat's
    /// session id ([`crate::webapp::build_play_menu_request`]). A control message OUTSIDE the
    /// session-slot bookkeeping (`web_app` buttons produce no callbacks to match), so the
    /// chat's active offering / presented keyboard are untouched.
    ///
    /// ⚑ **No shelf gate here, and none is needed**: this menu exists ONLY in a private chat
    /// (Telegram honors `web_app` inline buttons nowhere else — the `web_app_allowed` guard below
    /// is the first thing it checks), and the Mini App it launches renders in the launching user's
    /// own web view. Every surface it can reach is single-reader
    /// ([`ShelfSurface::Private`](dreggnet_offerings::shelf::ShelfSurface::Private)), so every
    /// advertised offering is legitimately live. `Err` carries the honest
    /// human reply when the tier cannot serve here: no base armed, a non-private chat
    /// (Telegram refuses `web_app` inline buttons in groups), or a transport failure.
    pub fn present_play_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> Result<(), String> {
        let Some(base) = self.webapp_base.clone() else {
            return Err(
                "The Mini App tier is not configured on this deploy — the inline buttons \
                 (/offerings) still play everything."
                    .to_string(),
            );
        };
        if !crate::webapp::web_app_allowed(chat_id, topic) {
            return Err(format!(
                "Mini App buttons only work in a private chat (Telegram's rule) — DM me and \
                 send /play. The web surface lives at {base}/tg."
            ));
        }
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let offerings = self.list_advertised_offerings();
        let req = crate::webapp::build_play_menu_request(chat_id, topic, &base, &sid, &offerings);
        self.frontend
            .send_raw(&req)
            .map(|_| ())
            .map_err(|e| format!("Could not send the play menu: {e}"))
    }

    /// Present the **`/link` identity-ceremony launch button** — a `web_app` button opening
    /// `<base>/tg/link` where the user signs a cross-platform link claim with their root key.
    /// Private chats only (Telegram honors `web_app` inline buttons only in DMs).
    pub fn present_link_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> Result<(), String> {
        let Some(base) = self.webapp_base.clone() else {
            return Err(
                "Linking needs the Mini App tier, which is not configured on this deploy."
                    .to_string(),
            );
        };
        if !crate::webapp::web_app_allowed(chat_id, topic) {
            return Err(format!(
                "Linking opens a web page, so it works in a private chat only (Telegram's rule) — \
                 DM me and send /link. The page lives at {base}/tg/link."
            ));
        }
        let req = crate::webapp::build_link_request(chat_id, topic, &base);
        self.frontend
            .send_raw(&req)
            .map(|_| ())
            .map_err(|e| format!("Could not send the link button: {e}"))
    }

    /// **Would hosting `key` in this chat leak?** — the gate in front of every open.
    ///
    /// A DM is a single-reader surface: a per-viewer projection there reaches exactly the person
    /// it is about. A group or forum topic is not — its session is ONE message that every member
    /// reads, and a re-present EDITS that message in place, so whatever is painted into it is
    /// painted for the whole room. An offering that DECLARES hidden information
    /// ([`dreggnet_offerings::Offering::hidden_information`]) therefore cannot be hosted on a
    /// shared surface at all, and this returns the legible redirect.
    ///
    /// The declared signal is what makes this decidable *before* opening: at that moment no seat
    /// is claimed and no card is dealt, so the per-viewer projection is still byte-identical to
    /// the public one — a render differential would answer "safe" and only start disagreeing after
    /// the first hand is dealt, which is one turn too late. `None` = safe to host here.
    fn hidden_in_shared_chat(
        &self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
    ) -> Option<String> {
        if !ChatKind::classify(chat_id, topic).is_collective() {
            return None;
        }
        let (hidden, title) = {
            let k = key.to_string();
            self.host.run(move |h| {
                (
                    h.hidden_information(&k).unwrap_or(false),
                    h.list_offerings()
                        .into_iter()
                        .find(|o| o.key == k)
                        .map(|o| o.title),
                )
            })
        };
        if !hidden {
            return None;
        }
        let title = title.unwrap_or_else(|| key.to_string());
        Some(format!(
            "🔒 {title} hides per-player state — your hand is yours alone. This chat is a group, \
             and a group's surface is ONE message every member reads (each move edits it in \
             place), so painting your own cards there would deal them to the whole table. I will \
             not do that. DM me and send `/open {key}` to play it privately — or `/play` for the \
             Mini App (Telegram allows those in DMs only). Full-information offerings \
             (`/offerings`) play here in the group as usual."
        ))
    }

    /// **Open an offering session for `(key, chat)`** — ensure a host session is live under the
    /// chat-scoped [`SessionId`] (seeded deterministically from it) and present the offering's
    /// current [`Surface`] on its OWN message in the chat.
    ///
    /// In a DM the surface is projected FOR the opening user `uid` (the per-viewer view — a
    /// hidden-hand / cap-dimmed offering paints the opener's own hand). In a group / forum topic
    /// it is the viewer-blind projection, and a hidden-information offering is REFUSED outright
    /// ([`OpenError::HiddenInSharedChat`]) rather than half-served — see
    /// [`hidden_in_shared_chat`](Self::hidden_in_shared_chat). Returns the chat-scoped session id.
    pub fn open(
        &mut self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<SessionId, OpenError> {
        if let Some(why) = self.hidden_in_shared_chat(key, chat_id, topic) {
            return Err(OpenError::HiddenInSharedChat {
                key: key.to_string(),
                why,
            });
        }
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let viewer = self.frontend.identity(uid);
        self.open_into(key, &sid, &viewer)?;
        Ok(sid)
    }

    /// Ensure a host session is live under `sid` (seeded from it) and present the offering's current
    /// surface on its own message, recording it as the chat's most recent. The shared opener behind
    /// [`open`](Self::open) and a menu-open press — BOTH of which check
    /// [`hidden_in_shared_chat`](Self::hidden_in_shared_chat) first.
    fn open_into(
        &mut self,
        key: &str,
        sid: &SessionId,
        viewer: &DreggIdentity,
    ) -> Result<(), OpenError> {
        let newly_opened = {
            let k = key.to_string();
            let s = sid.clone();
            // RPG keys open in the VIEWER's own per-identity world (isolated inventory); the shared
            // tables (games + services) open on the ONE catalog host.
            self.run_offering(key, viewer, move |h| h.ensure_open(&k, &s))?
        };
        if game_kind(key).is_some() {
            if let Err(error) = self.game_epochs.bind_after_ensure(key, sid, newly_opened) {
                // A fresh session without a persisted generation is not a
                // routable game. Roll the host/store mutation back before
                // reporting the epoch failure.
                if newly_opened {
                    let k = key.to_string();
                    let s = sid.clone();
                    self.run_offering(key, viewer, move |h| {
                        h.close(&k, &s);
                    });
                }
                return Err(OpenError::Epoch(error.to_string()));
            }
            if newly_opened {
                self.public_game_receipts
                    .remove(&(key.to_string(), sid.clone()));
            }
        }
        // Spin THIS offering's surface slot, not a bare chat-level one — a stray chat-keyed slot
        // would shadow the offering's own surface for every caller that looks a chat up.
        if let Some((chat_id, topic)) = TelegramFrontend::<T>::chat_of(sid) {
            let surface = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
            self.frontend.spin_session(surface.clone());
            // OPENING reposts; PLAYING edits in place. An open is an explicit "show me this
            // now" (a `/open`, a menu press, a post-restart rebind), and the offering's previous
            // message may be far up the scrollback — editing it there is invisible. A turn
            // landing still edits the live surface in place, which is what keeps one live
            // message per offering.
            //
            // DMs ONLY. A group / forum topic's session is deliberately ONE message that every
            // member reads and every re-present edits in place — that invariant is what the
            // audience rule rests on (see `present_offering`), so a repost there would be a
            // privacy-adjacent design change, not a UX fix. A collective chat keeps the edit;
            // the command surface answers in words instead
            // ([`has_live_surface`](Self::has_live_surface)).
            if !ChatKind::classify(chat_id, topic).is_collective() {
                self.frontend.repost_next(&surface);
            }
        }
        // A present that paints NOTHING is the one failure the command surface used to answer with
        // silence: `open` returned `Ok`, the ack said "Opened …", and no message ever appeared.
        // Record why, so the caller can say it ([`take_paint_failure`](Self::take_paint_failure)).
        self.last_paint_failure = self.present_offering(key, sid, viewer);
        Ok(())
    }

    /// Re-derive `(key, sid)`'s current surface + actions from the live host session and present
    /// them on THIS offering's own message in the chat, recording it as the chat's most recent.
    ///
    /// **Which projection depends on who can read the message, and that is the whole privacy
    /// rule:**
    /// - a **DM** is read by one person, so it gets the viewer-aware
    ///   [`OfferingHost::render_for`] / [`OfferingHost::actions_for`] — a hidden-hand tug or a
    ///   per-region document cap paints the surface for the specific Telegram user who is looking;
    /// - a **group / forum topic** is read by everyone in it, and its session is ONE message that
    ///   every re-present EDITS in place, so it gets the viewer-blind [`OfferingHost::render`] /
    ///   [`OfferingHost::actions`] — the PUBLIC projection, the only thing a shared message can
    ///   honestly carry.
    ///
    /// The rule is structural, not a heuristic: on a shared surface `render_for` is never called
    /// at all, so no offering — declared hidden or not, today's or a future one — can have a
    /// private projection edited into a message a group reads. (`hidden_information` offerings
    /// additionally never reach here in a group: they are refused at open, because a public-only
    /// projection is not a playable hand.) It also fixes an incoherence: a group keyboard used to
    /// be whichever member pressed last: now the shared message shows one shared board with one
    /// shared keyboard, and the executor stays the sole referee of what any presser may land.
    ///
    /// **Returns why NOTHING was painted**, or `None` when a message really went out. Every exit
    /// from this function used to be a bare `return`, so a surface that could not be projected (a
    /// game whose epoch generation is unrecoverable) or could not be sent (over Telegram's 4096
    /// characters, a callback over its 64-byte ceiling, a Bot API error) left the chat with no
    /// message and the caller with no idea — `open` still answered `Ok` and the user saw silence.
    fn present_offering(
        &mut self,
        key: &str,
        sid: &SessionId,
        viewer: &DreggIdentity,
    ) -> Option<String> {
        let Some((chat_id, topic)) = TelegramFrontend::<T>::chat_of(sid) else {
            return Some(format!("{} is not a telegram chat session", sid.0));
        };
        let shared = ChatKind::classify(chat_id, topic).is_collective();
        // `run_offering` already selects an RPG player's own host. That does NOT make a group
        // message single-reader: even a personal character sheet is painted with the offering's
        // viewer-blind projection in a collective chat. Only a DM is allowed to carry an identity
        // into the projection selector.
        let audience = audience_for_message(shared, viewer);
        let surface_sid = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
        // The surface is (re)painted fresh — any previously-armed text slot is now stale
        // (the affordance moved on), so drop it. Arming a text slot ([`Self::press`]) returns
        // BEFORE this, so the arm survives until the next advance / open / re-present.
        self.armed.remove(&surface_sid);
        let projection = if game_kind(key).is_some() {
            let Ok(reference) = self.game_epochs.bound_session(key, sid) else {
                return Some(format!(
                    "{key}'s durable routing epoch could not be bound for this chat"
                ));
            };
            let incarnation = self.game_epochs.host_incarnation();
            let Ok(generation) = self.game_epochs.current_generation(key, sid) else {
                return Some(format!(
                    "{key}'s current game generation could not be recovered for this chat"
                ));
            };
            let game_audience = if shared {
                GameAudience::Shared
            } else {
                GameAudience::AssertedPrivate(viewer.clone())
            };
            self.run_offering(key, viewer, move |host| {
                inspect_bound_game_session(host, incarnation, generation, reference, &game_audience)
                    .ok()
                    .map(|view| {
                        let mut callbacks = Vec::new();
                        let mut operations = Vec::new();
                        for affordance in &view.affordances {
                            match affordance {
                                GameAffordance::Turn { reference, .. } => {
                                    callbacks.push(bound_game_callback(reference));
                                }
                                GameAffordance::Operation { descriptor, .. } => {
                                    operations.push(descriptor.clone());
                                }
                            }
                        }
                        (view.projection, operations, Some(callbacks))
                    })
            })
        } else {
            let k = key.to_string();
            let s = sid.clone();
            self.run_offering(key, viewer, move |h| {
                h.project(&k, &s, &audience).map(|projection| {
                    let operations = h.binary_operations(&k, &s).unwrap_or_default();
                    (projection, operations, None)
                })
            })
        };
        if let Some((mut projection, operations, callbacks)) = projection {
            let private_projection = projection.private;
            let hidden_information = projection.hidden_information;
            append_game_session_record(
                &mut projection.surface,
                key,
                private_projection,
                hidden_information,
                operations.len(),
            );
            let guide_pages = operation_guide_pages(key, &operations, shared);
            // Host controls follow the offering's own actions. Re-verification is always
            // visible, including at terminal states; it is read-only and never recorded among
            // the presented offering Actions. In a DM, the Mini App launch follows it.
            let mut controls = vec![crate::verify_control::button()];
            let play = self.webapp_base.as_deref().and_then(|base| {
                let (chat_id, topic) = TelegramFrontend::<T>::chat_of(sid)?;
                crate::webapp::web_app_allowed(chat_id, topic)
                    .then(|| crate::webapp::play_button(base, key, sid))
            });
            if let Some(play) = play {
                controls.push(play);
            }
            // Onto THIS offering's own message — a second offering opened in the chat gets its
            // own, instead of stealing this one's.
            // Paint the non-interactive guide first so the interactive game surface remains the
            // chat's latest routable surface. When operations disappear, this neutralizes any
            // surplus guide messages instead of leaving stale upload instructions behind.
            self.frontend
                .present_companion_pages(&surface_sid, OPERATION_GUIDE_SLOT, &guide_pages);
            // The FALLIBLE present, so a message that never went out is REPORTED rather than
            // swallowed into `last_send_error` (which no caller read).
            let sent = if let Some(callbacks) = callbacks {
                self.frontend.present_result_with_callback_data(
                    &surface_sid,
                    &projection.surface,
                    &projection.actions,
                    &callbacks,
                    &controls,
                )
            } else {
                self.frontend.present_result_with(
                    &surface_sid,
                    &projection.surface,
                    &projection.actions,
                    &controls,
                )
            };
            // The session IS open either way, so the chat stays bound to it — a retry (`/open`,
            // a press) then re-paints instead of reporting "no session".
            self.active.insert(sid.clone(), key.to_string());
            sent.err().map(|e| e.to_string())
        } else {
            Some(format!(
                "{key} produced no surface to paint here (no live session for this chat, or its \
                 view could not be projected)"
            ))
        }
    }

    /// **Why the last open/advance painted NOTHING**, taken (cleared) by the caller. `None` means
    /// the surface really was sent. The command surface answers with this instead of silence —
    /// see [`present_offering`](Self::present_offering).
    pub fn take_paint_failure(&mut self) -> Option<String> {
        self.last_paint_failure.take()
    }

    /// Resolve and cheaply preflight an ordinary Telegram document operation.
    ///
    /// This must run before `getFile`: it resolves the active offering/session and actor, selects
    /// the exact live descriptor, and rejects declared oversize attachments. Ordinarily the
    /// document must be in a single-reader DM. The sole shared-chat exception is the public
    /// private-raid assignment proof: its offering verifier binds the authenticated uploader to
    /// proof seat zero, the exact ordered roster, and the session-derived proof id. No body bytes
    /// are accepted or allocated here.
    pub fn preflight_operation(
        &self,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
        name: &str,
        declared_bytes: usize,
    ) -> Result<TelegramOperationRoute, TelegramOperationError> {
        let shared = ChatKind::classify(chat_id, topic).is_collective();
        let session = TelegramFrontend::<T>::session_id(chat_id, topic);
        let key = self
            .active_offering(&session)
            .ok_or(TelegramOperationError::NoSession)?
            .to_string();
        let actor = self.frontend.identity(uid);
        let (operations, game_reference) = if game_kind(&key).is_some() {
            let view = self
                .bound_game_view(&key, &session, &actor, shared)
                .map_err(|reason| {
                    if shared {
                        TelegramOperationError::SharedGameRefused
                    } else {
                        TelegramOperationError::Refused(reason)
                    }
                })?;
            let mut operations = Vec::new();
            let mut selected = None;
            for affordance in view.affordances {
                if let GameAffordance::Operation {
                    reference,
                    descriptor,
                } = affordance
                {
                    if descriptor.name == name {
                        if selected.is_some() {
                            return Err(if shared {
                                TelegramOperationError::SharedGameRefused
                            } else {
                                TelegramOperationError::Refused(
                                    "the game advertised an ambiguous operation route".to_string(),
                                )
                            });
                        }
                        selected = Some(reference);
                    }
                    operations.push(descriptor);
                }
            }
            (operations, selected)
        } else {
            let routed_key = key.clone();
            let routed_session = session.clone();
            let operations = self
                .run_offering(&key, &actor, move |host| {
                    host.binary_operations(&routed_key, &routed_session)
                })
                .map_err(|error| TelegramOperationError::Refused(error.to_string()))?;
            (operations, None)
        };
        let policy = preflight_chat_binary_operation(&operations, name, declared_bytes).map_err(
            |error| {
                if shared {
                    TelegramOperationError::SharedGameRefused
                } else {
                    TelegramOperationError::Refused(error.to_string())
                }
            },
        )?;
        if game_kind(&key).is_some() && game_reference.is_none() {
            return Err(if shared {
                TelegramOperationError::SharedGameRefused
            } else {
                TelegramOperationError::Refused(
                    "the operation is not an exact bound game affordance".to_string(),
                )
            });
        }
        if shared && !shared_operation_allowed(&key, &policy.descriptor.name) {
            return Err(TelegramOperationError::PrivateChatRequired);
        }
        Ok(TelegramOperationRoute {
            key,
            session,
            actor,
            policy,
            shared,
            game_reference,
        })
    }

    /// Apply a preflighted document to the same live operation, then repaint its exact chat from
    /// committed state. Descriptor selection, shared-chat eligibility, and actual-length
    /// validation are repeated, closing state/metadata races between preflight and the Telegram
    /// CDN download.
    pub fn apply_operation(
        &mut self,
        route: TelegramOperationRoute,
        payload: Vec<u8>,
    ) -> Result<TelegramAppliedOperation, TelegramOperationError> {
        let TelegramOperationRoute {
            key,
            session,
            actor,
            policy,
            shared,
            game_reference,
        } = route;
        let name = policy.descriptor.name.clone();
        if shared && !shared_operation_allowed(&key, &name) {
            return Err(TelegramOperationError::PrivateChatRequired);
        }
        let declared_bytes = policy.declared_bytes;
        let actual_bytes = payload.len();
        let game_epoch = if game_reference.is_some() {
            Some((
                self.game_epochs.host_incarnation(),
                self.game_epochs
                    .current_generation(&key, &session)
                    .map_err(|error| {
                        if shared {
                            TelegramOperationError::SharedGameRefused
                        } else {
                            TelegramOperationError::Refused(error.to_string())
                        }
                    })?,
            ))
        } else {
            None
        };
        let result = {
            let routed_key = key.clone();
            let routed_session = session.clone();
            let routed_actor = actor.clone();
            self.run_offering(&key, &actor, move |host| {
                let operations = host
                    .binary_operations(&routed_key, &routed_session)
                    .map_err(|error| error.to_string())?;
                let current = preflight_chat_binary_operation(&operations, &name, declared_bytes)
                    .map_err(|error| error.to_string())?;
                current
                    .validate_body_len(actual_bytes)
                    .map_err(|error| error.to_string())?;
                if let (Some(reference), Some((incarnation, generation))) =
                    (game_reference, game_epoch)
                {
                    let game_session = reference.session.clone();
                    match execute_bound_asserted_game_command(
                        host,
                        incarnation,
                        generation,
                        &game_session,
                        GameCommand::Operation { reference, payload },
                        routed_actor,
                    )
                    .map_err(|error| error.to_string())?
                    {
                        GameResult::Landed(receipt) => {
                            let direct = match &receipt {
                                GameReceipt::Operation {
                                    operation,
                                    inner_receipt_id,
                                    public_fields,
                                    ..
                                } if !shared => Some(BinaryOperationReceipt {
                                    operation: operation.operation.clone(),
                                    receipt_id: *inner_receipt_id,
                                    public_fields: public_fields.clone(),
                                }),
                                GameReceipt::Operation { .. } => None,
                                GameReceipt::Turn { .. } => {
                                    return Err("game operation returned an ordinary-turn receipt"
                                        .to_string());
                                }
                            };
                            Ok((direct, Some(receipt)))
                        }
                        GameResult::Refused { reason, .. } => Err(reason),
                    }
                } else {
                    host.invoke_binary_operation(
                        &routed_key,
                        &routed_session,
                        &name,
                        &payload,
                        routed_actor,
                    )
                    .map(|receipt| (Some(receipt), None))
                    .map_err(|error| error.to_string())
                }
            })
        };
        match result {
            Ok((direct_receipt, game_receipt)) => {
                let public_receipt = if let Some(game_receipt) = game_receipt {
                    self.remember_public_game_result(
                        &key,
                        &session,
                        &GameResult::Landed(game_receipt),
                    )
                } else {
                    None
                };
                self.last_paint_failure = self.present_offering(&key, &session, &actor);
                if shared {
                    Ok(match public_receipt {
                        Some(receipt) => TelegramAppliedOperation::SharedGame(receipt),
                        None => TelegramAppliedOperation::SharedGameUnpublished,
                    })
                } else {
                    direct_receipt
                        .map(TelegramAppliedOperation::Direct)
                        .ok_or_else(|| {
                            TelegramOperationError::Refused(
                                "private operation omitted its direct receipt".to_string(),
                            )
                        })
                }
            }
            Err(reason) => Err(if shared {
                TelegramOperationError::SharedGameRefused
            } else {
                TelegramOperationError::Refused(reason)
            }),
        }
    }

    /// Inspect one Telegram-addressed game through the exact live authority
    /// epoch. All game rendering and action collection share this path, so a
    /// frontend cannot accidentally mint a callback from a legacy-unbound
    /// projection.
    fn bound_game_view(
        &self,
        key: &str,
        session: &SessionId,
        viewer: &DreggIdentity,
        shared: bool,
    ) -> Result<dreggnet_catalog::GameSessionView, String> {
        let reference = self
            .game_epochs
            .bound_session(key, session)
            .map_err(|error| error.to_string())?;
        let incarnation = self.game_epochs.host_incarnation();
        let generation = self
            .game_epochs
            .current_generation(key, session)
            .map_err(|error| error.to_string())?;
        let audience = if shared {
            GameAudience::Shared
        } else {
            GameAudience::AssertedPrivate(viewer.clone())
        };
        self.run_offering(key, viewer, move |host| {
            inspect_bound_game_session(host, incarnation, generation, reference, &audience)
                .map_err(|error| error.to_string())
        })
    }

    /// Retain only the catalog-audited public projection of a newly landed game receipt. A
    /// projection failure clears the presentation cache for this address; the raw receipt never
    /// becomes a fallback shared payload.
    fn remember_public_game_result(
        &mut self,
        key: &str,
        session: &SessionId,
        result: &GameResult,
    ) -> Option<PublicGameReceipt> {
        let Some(receipt) = result.receipt() else {
            return None;
        };
        let address = (key.to_string(), session.clone());
        match project_public_game_receipt(receipt) {
            Ok(publication) if publication.validate().is_ok() => {
                self.public_game_receipts
                    .insert(address, publication.clone());
                Some(publication)
            }
            Ok(_) | Err(_) => {
                self.public_game_receipts.remove(&address);
                None
            }
        }
    }

    /// **Route a button press.** Resolve WHICH of the chat's live surfaces the press addresses,
    /// decode its `callback_data` into `{turn, arg}`, check the turn is among the affordances that
    /// surface presented (offered), and:
    /// - if the addressed surface is the offerings menu, OPEN the offering the pressed button names;
    /// - otherwise ADVANCE that surface's offering by ONE real turn on the substrate and re-present.
    ///
    /// **Surface resolution** — a chat may hold several live offerings at once, each on its own
    /// message. A real press carries the message it was pressed on
    /// ([`crate::CallbackQuery::message_id`]), which names its surface exactly; a synthesized press
    /// that carries none (a `/act` or `/verify` command, a Mini App `sendData` round-trip) falls
    /// back to the chat's most recently presented surface. So the offerings menu stays live and
    /// usable to open a SECOND offering, and a press on the first offering's message still reaches
    /// the first offering.
    ///
    /// The matching is TURN-offered (mirroring the web catalog's `post_offering_act`): an index move
    /// (a dungeon choice, a council proposal) carries its index in the button, while a value-taking
    /// move (a market `list` reserve / `bid` value) carries a value the press supplies — on a live
    /// bot the value rides a follow-up numeric reply; here the [`crate::CallbackQuery`] carries it.
    /// The executor stays the sole referee of what LANDS (a below-reserve bid, a double-vote, a
    /// killing blow are all real substrate refusals); a press for a turn the surface never offered
    /// is [`HostPress::NotOffered`] (refused BEFORE the substrate); a press in a chat with nothing
    /// open is [`HostPress::NoSession`].
    pub fn press(&mut self, ev: crate::CallbackQuery) -> HostPress {
        // The HOST session id stays chat-scoped: `(key, sid)` already names a host session, so two
        // offerings in one chat are already two sessions. Only the SURFACE needed splitting.
        let sid = TelegramFrontend::<T>::session_id(ev.chat_id, ev.message_thread_id);
        // Which surface is being pressed: the press's own message names it; a press that names no
        // message means the chat's most recent surface.
        let surface_sid = match ev.message_id {
            Some(message_id) => match self.frontend.surface_of_message(
                ev.chat_id,
                ev.message_thread_id,
                MessageId(message_id),
            ) {
                Some(surface) => surface.clone(),
                // A press on a KNOWN companion page (a proof-operation guide) is refused
                // outright: a guide is never an action surface, and must never fall through to
                // the chat's latest game keyboard.
                None if self.frontend.is_companion_message(
                    ev.chat_id,
                    ev.message_thread_id,
                    MessageId(message_id),
                ) =>
                {
                    return HostPress::NotOffered;
                }
                // A message this PROCESS has never presented. After a restart that is EVERY
                // button in the chat — the message index is in-memory and the surfaces were
                // never repainted. Refusing here made every pre-restart button permanently dead
                // and made the documented restart-resume path (which only fires on `NoSession`)
                // unreachable for real presses, since a real press always names its message.
                // Fall back to the chat's live surface if this process has one, else report
                // `NoSession` so the caller can resume the durable session and re-present.
                None => match self.frontend.latest_surface(&sid) {
                    Some(surface) => surface.clone(),
                    None => return HostPress::NoSession,
                },
            },
            None => match self.frontend.latest_surface(&sid) {
                Some(surface) => surface.clone(),
                None => sid.clone(),
            },
        };
        // …and which offering that surface belongs to. A surface id carries its own offering; a
        // bare chat-scoped surface is the chat-level one (the offerings menu).
        let active = match TelegramFrontend::<T>::offering_of(&surface_sid) {
            Some(k) => k.to_string(),
            None => match self.active.get(&sid).cloned() {
                Some(k) => k,
                None => return HostPress::NoSession,
            },
        };
        // The acting Telegram user's derived identity — the viewer every re-present is projected FOR
        // (the same identity the play turn is attributed to), so a per-viewer offering paints the
        // presser their own surface.
        let viewer = self.frontend.identity(ev.from_user_id);
        // Generic/menu controls use the historical `{turn, arg}` codec. Game
        // messages use an opaque digest of the complete bound reference and
        // therefore intentionally do not decode here.
        let decoded = crate::api::decode_callback(&ev.data);
        // The exact reserved host-level verify control bypasses the offered-action check.
        // Read-only: the presented surface and player attribution stay exactly as they were.
        if decoded
            .as_ref()
            .is_some_and(|(turn, arg)| crate::verify_control::is_verify_callback(turn, *arg))
        {
            if active == MENU_KEY {
                return HostPress::NotOffered;
            }
            // Re-verify the PRESSER's own chain — for an RPG key that is a session in their own
            // world, so verify must route to the same world its turns landed in.
            let report = {
                let k = active.clone();
                let s = sid.clone();
                self.run_offering(&active, &viewer, move |h| h.verify(&k, &s))
            };
            return HostPress::Verified {
                key: active,
                report,
            };
        }
        if decoded
            .as_ref()
            .is_some_and(|(turn, _)| turn == TURN_VERIFY)
        {
            // Reserve the whole verb namespace: a forged argument must never fall through to a
            // future offering that accidentally reuses the host-control verb.
            return HostPress::NotOffered;
        }
        if active == MENU_KEY {
            let Some((turn, arg)) = decoded else {
                return HostPress::NotOffered;
            };
            let offered = self
                .frontend
                .session(&surface_sid)
                .map(|slot| slot.presented.iter().any(|action| action.turn == turn))
                .unwrap_or(false);
            if !offered {
                return HostPress::NotOffered;
            }
            // A menu press: open the offering the button names (by stable catalog index).
            //
            // ⚑ Resolved against the FULL list, exactly as `present_offerings_menu_result` paints
            // it — the index is a position in `list_offerings()`, and it must stay one. Resolving
            // against the advertised subset here would silently reinterpret every arg the moment
            // the ship list changed.
            if turn != TURN_OPEN {
                return HostPress::NotOffered;
            }
            let offerings = self.list_offerings();
            let Ok(index) = usize::try_from(arg) else {
                return HostPress::NotOffered;
            };
            let Some(info) = offerings.get(index) else {
                return HostPress::NotOffered;
            };
            let key = info.key.clone();
            // The SAME gate `/open` faces: a hidden-information offering is not hosted on a
            // surface a whole group reads — refused here, before anything is rendered.
            if let Some(why) = self.hidden_in_shared_chat(&key, ev.chat_id, ev.message_thread_id) {
                return HostPress::OpenRefused { key, why };
            }
            // Open the offering's host session (seeded from the chat) + present its surface on its
            // own message.
            if self.open_into(&key, &sid, &viewer).is_err() {
                return HostPress::NotOffered;
            }
            return HostPress::Opened(key);
        }

        let key = active;

        if game_kind(&key).is_some() {
            let shared = ChatKind::classify(ev.chat_id, ev.message_thread_id).is_collective();
            let Ok(view) = self.bound_game_view(&key, &sid, &viewer, shared) else {
                return HostPress::NotOffered;
            };
            let selected = if ev.data.starts_with("g.") {
                view.affordances.iter().find_map(|affordance| {
                    let GameAffordance::Turn {
                        reference, action, ..
                    } = affordance
                    else {
                        return None;
                    };
                    (bound_game_callback(reference) == ev.data)
                        .then(|| (reference.clone(), action.clone()))
                })
            } else if ev.message_id.is_none() {
                // `/act` and Mini-App round trips name a value-taking turn,
                // rather than replaying a Telegram message button. Preserve
                // that compatibility by requiring the turn template to be
                // live, then bind the caller-supplied final argument and the
                // current observed head into a fresh exact reference.
                decoded.and_then(|(turn, arg)| {
                    let template = view.affordances.iter().find_map(|affordance| {
                        let GameAffordance::Turn {
                            reference, action, ..
                        } = affordance
                        else {
                            return None;
                        };
                        (reference.turn == turn).then_some(action)
                    })?;
                    let action =
                        if template.wants_text && template.text.is_none() && template.arg == arg {
                            template.clone()
                        } else {
                            Action::new(turn.clone(), turn, arg, true)
                        };
                    let reference = GameActionRef::new(
                        view.session.clone(),
                        &action,
                        view.surface_commitment.clone(),
                    );
                    Some((reference, action))
                })
            } else {
                // A real game-message callback must carry a bound opaque token;
                // accepting `{turn,arg}` here would let a captured old button
                // be reinterpreted in a later session generation.
                None
            };
            let Some((reference, action)) = selected else {
                return HostPress::NotOffered;
            };
            if action.wants_text && action.text.is_none() {
                self.armed
                    .insert(surface_sid, ArmedText::now(action.clone()));
                return HostPress::TextArmed { key, action };
            }
            let incarnation = self.game_epochs.host_incarnation();
            let Ok(generation) = self.game_epochs.current_generation(&key, &sid) else {
                return HostPress::NotOffered;
            };
            let session = view.session;
            let actor = viewer.clone();
            let execution = self.run_offering(&key, &viewer, move |host| {
                execute_bound_asserted_game_turn(
                    host,
                    incarnation,
                    generation,
                    &session,
                    reference,
                    action,
                    actor,
                )
            });
            return match execution {
                Ok(execution) => {
                    let _ = self.remember_public_game_result(&key, &sid, &execution.result);
                    self.last_paint_failure = self.present_offering(&key, &sid, &viewer);
                    HostPress::Advanced {
                        key,
                        outcome: execution.outcome,
                    }
                }
                Err(_) => HostPress::NotOffered,
            };
        }

        let Some((turn, arg)) = decoded else {
            return HostPress::NotOffered;
        };
        let offered = self
            .frontend
            .session(&surface_sid)
            .map(|slot| slot.presented.iter().any(|action| action.turn == turn))
            .unwrap_or(false);
        if !offered {
            return HostPress::NotOffered;
        }

        // A play press on a FREE-TEXT affordance (a `wants_text` template — a document
        // insert/set-title, a Hermes prompt, a names register, a compute settle) carries no
        // content, so it does not advance: it ARMS the chat's text slot, and the next plain-text
        // message fills it ([`Self::press_text`]). Matched on the EXACT (turn, arg) the press
        // names, so a document's four distinct text templates are each selectable — not just the
        // first (the old `find(wants_text)` made the doc silently append-only).
        // Bound to a `let` first so the immutable `self.frontend` borrow ends before the mutable
        // `self.armed` insert below.
        let text_affordance = self.frontend.session(&surface_sid).and_then(|slot| {
            slot.presented
                .iter()
                .find(|a| a.turn == turn && a.arg == arg && a.wants_text && a.text.is_none())
                .cloned()
        });
        if let Some(text_affordance) = text_affordance {
            self.armed
                .insert(surface_sid.clone(), ArmedText::now(text_affordance.clone()));
            return HostPress::TextArmed {
                key,
                action: text_affordance,
            };
        }

        // A non-text move: the CORE resolves the typed action on the real substrate — one turn.
        // Label + enabled are decoration; the executor resolves the typed (turn, arg). Routed to
        // the presser's own world for an RPG key.
        let actor = viewer.clone();
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = {
            let k = key.clone();
            let s = sid.clone();
            self.run_offering(&key, &viewer, move |h| h.advance(&k, &s, action, actor))
        };
        match outcome {
            Some(outcome) => {
                // Re-present the (possibly-advanced) committed state so the next press resolves
                // against the current surface, projected for the pressing user.
                self.last_paint_failure = self.present_offering(&key, &sid, &viewer);
                HostPress::Advanced { key, outcome }
            }
            // The host had no such session (should not happen: `active` implies a live session).
            None => HostPress::NoSession,
        }
    }

    /// **The chat's ARMED text affordance, if one is selected** — the "this slot wants text"
    /// signal the free-text router keys on. Returns the affordance the chat has ARMED (by a
    /// button press on a [`Action::wants_text`] template — see [`HostPress::TextArmed`]), or
    /// `None` when the chat has no active offering (or is browsing the menu), or nothing is armed.
    ///
    /// The selection is DELIBERATE, not automatic: a press RECORDS the chosen `(turn, arg)`
    /// text affordance ([`Self::press`]), and only THEN does a plain-text message route into it.
    /// This is what keeps free-text capture honest — with nothing armed, a chat's plain messages
    /// are ordinary chatter, never swallowed into an offering (the old `find(wants_text)`
    /// captured EVERY message the moment any text offering was open, and always into the FIRST
    /// text affordance — making a document silently append-only and a group chat's every message
    /// an offering input). A stale arm (the surface moved on, so the affordance is no longer
    /// presented) is dropped.
    pub fn pending_text_action(&self, sid: &SessionId) -> Option<Action> {
        // Resolve the SURFACE: `sid` may already name one (`tg:-5#doc`), or be the chat-scoped id,
        // in which case the chat's most recent offering owns the text slot. Only a real offering
        // (not the offerings menu) solicits text.
        let key = match TelegramFrontend::<T>::offering_of(sid) {
            Some(k) => k.to_string(),
            None => self.active_offering(sid)?.to_string(),
        };
        let (chat_id, topic) = TelegramFrontend::<T>::chat_of(sid)?;
        let surface_sid = TelegramFrontend::<T>::surface_id(chat_id, topic, &key);
        // The chat must have ARMED a text affordance on THAT surface (a deliberate press) …
        let armed = self.armed.get(&surface_sid)?;
        // … recently enough. An arm older than [`TEXT_ARM_TTL`] has been forgotten by whoever
        // made it; honouring it would swallow an unrelated message hours later into an offering.
        if armed.expired() {
            return None;
        }
        let armed = &armed.action;
        // Belt-and-suspenders: the armed affordance must still be the presented surface's own
        // (a stale arm — after a re-present that changed the affordances — is not honoured).
        let slot = self.frontend.session(&surface_sid)?;
        slot.presented
            .iter()
            .any(|a| a.turn == armed.turn && a.arg == armed.arg && a.wants_text)
            .then(|| armed.clone())
    }

    /// Backdate every armed free-text slot by `by` — the seam a test uses to drive the
    /// [`TEXT_ARM_TTL`] expiry without sleeping for fifteen minutes.
    #[doc(hidden)]
    pub fn backdate_arms(&mut self, by: std::time::Duration) {
        for armed in self.armed.values_mut() {
            armed.at = armed.at.checked_sub(by).unwrap_or(armed.at);
        }
    }

    /// **Route free text into the chat's pending text affordance** — the in-chat driver for a
    /// text-input offering (a document EDIT's prose, a set-title's value). Finds the chat's
    /// [`pending_text_action`](Self::pending_text_action), attaches `text` as its
    /// [`Action::text`] payload, and ADVANCES it as one real turn on the substrate, attributed to
    /// `uid`'s derived identity — exactly the path a button press takes ([`Self::press`]), only
    /// the affordance's string is supplied by the message instead of a callback arg. The executor
    /// stays the sole referee: an ill-formed / unauthorized / conflicting edit lands a real
    /// [`Outcome::Refused`] (nothing committed), never a silent accept.
    ///
    /// [`HostPress::NoSession`] if nothing is open in the chat; [`HostPress::NotOffered`] if the
    /// chat's surface has no text affordance pending (the caller should have checked
    /// [`pending_text_action`](Self::pending_text_action) first, so this is a belt-and-suspenders
    /// refusal, not a normal path). Re-presents the (possibly-advanced) surface on success.
    pub fn press_text(
        &mut self,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
        text: &str,
    ) -> HostPress {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let Some(key) = self.active_offering(&sid).map(str::to_string) else {
            return HostPress::NoSession;
        };
        let Some(pending) = self.pending_text_action(&sid) else {
            return HostPress::NotOffered;
        };
        // The acting user's derived identity — the viewer every re-present is projected FOR and
        // the actor the edit is attributed to (the same as a play press).
        let viewer = self.frontend.identity(uid);
        let action = pending.clone().with_text(text.to_string());
        let (outcome, game_result) = if game_kind(&key).is_some() {
            let shared = ChatKind::classify(chat_id, topic).is_collective();
            let Ok(view) = self.bound_game_view(&key, &sid, &viewer, shared) else {
                return HostPress::NotOffered;
            };
            let still_offered = view.affordances.iter().any(|affordance| {
                matches!(
                    affordance,
                    GameAffordance::Turn { action: template, .. }
                        if template.turn == pending.turn
                            && template.arg == pending.arg
                            && template.wants_text
                            && template.text.is_none()
                )
            });
            if !still_offered {
                return HostPress::NotOffered;
            }
            let reference = GameActionRef::new(
                view.session.clone(),
                &action,
                view.surface_commitment.clone(),
            );
            let incarnation = self.game_epochs.host_incarnation();
            let Ok(generation) = self.game_epochs.current_generation(&key, &sid) else {
                return HostPress::NotOffered;
            };
            let session = view.session;
            let actor = viewer.clone();
            match self.run_offering(&key, &viewer, move |host| {
                execute_bound_asserted_game_turn(
                    host,
                    incarnation,
                    generation,
                    &session,
                    reference,
                    action,
                    actor,
                )
            }) {
                Ok(execution) => (Some(execution.outcome), Some(execution.result)),
                Err(_) => return HostPress::NotOffered,
            }
        } else {
            let actor = viewer.clone();
            let k = key.clone();
            let s = sid.clone();
            // Routed to the acting user's own world for an RPG key (a per-player document/craft edit).
            (
                self.run_offering(&key, &viewer, move |h| h.advance(&k, &s, action, actor)),
                None,
            )
        };
        if let Some(result) = &game_result {
            let _ = self.remember_public_game_result(&key, &sid, result);
        }
        match outcome {
            Some(outcome) => {
                self.last_paint_failure = self.present_offering(&key, &sid, &viewer);
                HostPress::Advanced { key, outcome }
            }
            None => HostPress::NoSession,
        }
    }

    /// **Rebind a chat to its durably RESUMED offering after a process restart.** A restarted
    /// host (built over a resume store — [`crate::runtime::durable_telegram_host`]) reopens every
    /// persisted session by move-log replay on boot, but this surface layer's in-memory routing
    /// (`active`, the presented keyboard) starts empty, so the first press in a chat answers
    /// [`HostPress::NoSession`]. This looks the chat's session id up among the LIVE host sessions:
    /// if some offering has `sid` open (i.e. it was resumed), it is recorded active again and its
    /// key returned — the caller then re-presents via [`open`](Self::open) (idempotent: the
    /// resumed session is kept, only the surface is repainted). `None` if no resumed session
    /// exists for the chat. If a chat had MULTIPLE offerings' sessions persisted (it re-opened
    /// across offerings), the first in registry order is chosen — `/open <key>` overrides.
    pub fn resume_chat(&mut self, sid: &SessionId) -> Option<String> {
        self.resume_chat_all(sid, None).into_iter().next()
    }

    /// **Every durably-resumed offering this chat owns**, rebound to it — the honest form of
    /// [`resume_chat`](Self::resume_chat).
    ///
    /// `resume_chat` used to pick the FIRST open key in the registry's `BTreeMap` order, i.e. the
    /// alphabetically-first offering the chat ever opened. With `craft` and `doc` both persisted
    /// for one chat, EVERY post-restart press was rebound to `craft` regardless of which
    /// message it was pressed on — so a `doc` button routed into `craft`'s keyboard, matched
    /// nothing, and read as dead. Worse, if that arbitrary winner is a session no affordance can
    /// advance, the chat is pinned to it across every restart. Resuming ALL of them and letting
    /// the pressed message pick removes the arbitrary choice entirely.
    ///
    /// `viewer` is the acting user's derived identity. It is REQUIRED to find an
    /// [`is_rpg_key`] session: those live in the presser's own per-identity world
    /// ([`durable_player_worlds`](crate::runtime::durable_player_worlds) writes them under
    /// `<dir>/players/<hash>`), which the shared catalog host cannot see at all. Without it, a
    /// chat whose only durable sessions are RPG surfaces — a `craft`, an `inventory` — resumes
    /// as EMPTY after a restart and every button in it answers "no session in this chat yet",
    /// which is strictly worse than the arbitrary rebind it replaced.
    ///
    /// The returned keys are in catalog order (shared first, then the viewer's own); the first
    /// is recorded as the chat's `active` fallback for command-minted presses that name no
    /// message.
    pub fn resume_chat_all(
        &mut self,
        sid: &SessionId,
        viewer: Option<&DreggIdentity>,
    ) -> Vec<String> {
        let mut keys: Vec<String> = {
            let s = sid.clone();
            self.host.run(move |h| {
                let mut open = Vec::new();
                for key in h.keys() {
                    if h.is_open(&key, &s) {
                        open.push(key);
                    }
                }
                open
            })
        };
        if let Some(viewer) = viewer {
            let id = viewer.0.clone();
            let s = sid.clone();
            let mut mine: Vec<String> = self.players.run(move |worlds| {
                let world = worlds.host_mut(&id);
                let mut open = Vec::new();
                for key in world.keys() {
                    if world.is_open(&key, &s) {
                        open.push(key);
                    }
                }
                open
            });
            mine.retain(|key| !keys.contains(key));
            keys.append(&mut mine);
        }
        // A game whose durable routing epoch cannot be recovered is not a routable session.
        keys.retain(|key| {
            game_kind(key).is_none() || self.game_epochs.current_generation(key, sid).is_ok()
        });
        // An already-bound offering stays the chat's fallback (the caller's own `active` choice
        // wins over catalog order).
        if let Some(bound) = self
            .active
            .get(sid)
            .filter(|k| k.as_str() != MENU_KEY)
            .cloned()
        {
            if let Some(at) = keys.iter().position(|k| *k == bound) {
                keys.swap(0, at);
            }
        }
        if let Some(first) = keys.first() {
            self.active.insert(sid.clone(), first.clone());
        }
        keys
    }

    /// **The always-available escape** (`/cancel`) — unstick a chat WITHOUT discarding anything
    /// committed.
    ///
    /// Drops the chat's presentation state: every live surface, the message-routing index for
    /// this chat, its companion guide pages, its "latest surface" pointer, its armed free-text
    /// slot, and its `active` offering. Host sessions and their durable move-logs are untouched —
    /// `/open <key>` brings any of them straight back, receipts intact. Returns the surface ids
    /// that were live, so the caller can say what it cleared.
    ///
    /// This exists because every previous way out of a wedged chat was implicit: a stale arm was
    /// cleared only by a re-present, a mis-bound `active` only by a successful open, and a chat
    /// whose surfaces were all unroutable had no input at all that could fix it.
    pub fn cancel_chat(&mut self, chat_id: ChatId, topic: Option<i64>) -> Vec<String> {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let cleared = self.frontend.teardown_chat(&sid);
        let mut keys: Vec<String> = cleared
            .iter()
            .filter_map(|surface| TelegramFrontend::<T>::offering_of(surface))
            .filter(|key| *key != MENU_KEY)
            .map(str::to_string)
            .collect();
        keys.sort();
        keys.dedup();
        for surface in &cleared {
            self.armed.remove(surface);
        }
        // Any arm keyed to this chat's surfaces, including one whose slot was already replaced.
        self.armed.retain(|surface, _| {
            TelegramFrontend::<T>::chat_session_of(surface).as_ref() != Some(&sid)
        });
        self.active.remove(&sid);
        keys
    }

    /// **End `key`'s session in this chat and DISCARD its durable move-log** (`/close <key>`) —
    /// the destructive escape, for a session that can no longer advance. `Ok(false)` = nothing was
    /// open under that key; `Err` = the close was attempted and something refused, which the
    /// command surface must say rather than reporting "nothing was open".
    /// [`cancel_chat`](Self::cancel_chat) is the non-destructive one; this is the only path that
    /// forgets committed history, and the command surface requires the key explicitly so it
    /// cannot be fired by reflex.
    ///
    /// A CATALOG GAME routes through [`close_game`](Self::close_game), which additionally RETIRES
    /// the session's epoch generation. Closing a game without that leaves the epoch ledger holding
    /// an `active` generation for an address with no session behind it — an escape hatch has no
    /// business leaving new inconsistency behind it.
    pub fn close_offering(
        &mut self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<bool, String> {
        if game_kind(key).is_some() {
            let closed = self.close_game(key, chat_id, topic, uid)?;
            if closed {
                // `close_game` drops the epoch + attribution state; the SURFACE is this escape's
                // own concern (a dead keyboard left in the chat is half the wedge).
                self.frontend
                    .teardown(&TelegramFrontend::<T>::surface_id(chat_id, topic, key));
            }
            return Ok(closed);
        }
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let viewer = self.frontend.identity(uid);
        let closed = {
            let k = key.to_string();
            let s = sid.clone();
            self.run_offering(key, &viewer, move |h| h.close(&k, &s))
        };
        if closed {
            let surface = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
            self.frontend.teardown(&surface);
            self.armed.remove(&surface);
            self.public_game_receipts
                .remove(&(key.to_string(), sid.clone()));
            if self.active.get(&sid).map(String::as_str) == Some(key) {
                self.active.remove(&sid);
            }
        }
        Ok(closed)
    }

    /// Close one addressed game and retire its current generation.
    ///
    /// The concrete host/store is closed first. Epoch retirement follows; if
    /// that persistence fails, a later genuinely fresh open still increments
    /// from the retained generation and therefore cannot revive old action
    /// references.
    pub fn close_game(
        &mut self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<bool, String> {
        if game_kind(key).is_none() {
            return Err(format!("{key} is not a catalog game"));
        }
        let session = TelegramFrontend::<T>::session_id(chat_id, topic);
        let viewer = self.frontend.identity(uid);
        let routed_key = key.to_string();
        let routed_session = session.clone();
        let removed = self.run_offering(key, &viewer, move |host| {
            host.close(&routed_key, &routed_session)
        });
        if !removed {
            return Ok(false);
        }
        self.game_epochs
            .mark_closed(key, &session)
            .map_err(|error| error.to_string())?;
        self.public_game_receipts
            .remove(&(key.to_string(), session.clone()));
        if self
            .active
            .get(&session)
            .is_some_and(|active| active == key)
        {
            self.active.remove(&session);
        }
        let surface = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
        self.armed.remove(&surface);
        Ok(true)
    }

    /// Re-verify `(key, sid)`'s committed chain by the offering's own proof (`None` if absent).
    pub fn verify(&self, key: &str, sid: &SessionId) -> Option<VerifyReport> {
        let key = key.to_string();
        let sid = sid.clone();
        self.host.run(move |h| h.verify(&key, &sid))
    }

    /// The bot master secret (for a deploy to sign on a user's behalf; the frontend attributes with
    /// the public identity alone).
    pub fn bot_secret(&self) -> &[u8; 32] {
        &self.bot_secret
    }
}

/// Add the small piece of common chrome every catalog game receives.
///
/// This is intentionally protocol language, not game language: it says which family is mounted,
/// which audience projection Telegram selected, and where receipt/proof status lives. Concrete
/// rules, action labels, and scene prose remain entirely owned by the offering.
fn append_game_session_record(
    surface: &mut Surface,
    key: &str,
    private_projection: bool,
    hidden_information: bool,
    proof_operations: usize,
) {
    let Some(kind) = game_kind(key) else {
        return;
    };
    let audience = if private_projection {
        "private single-reader projection"
    } else {
        "shared viewer-blind projection"
    };
    let mut children = vec![ViewNode::Text(format!(
        "{} · {audience} · accepted moves append receipts; /status inspects the record.",
        kind.as_str()
    ))];
    if proof_operations > 0 {
        children.push(ViewNode::Text(format!(
            "{proof_operations} proof operation(s) are described in the non-interactive companion guide."
        )));
    }
    if private_projection && hidden_information {
        children.push(ViewNode::Text(
            "This message may contain player-only state. Do not forward it.".to_string(),
        ));
    }
    let record = ViewNode::Section {
        title: "Session record".to_string(),
        tag: "genuine".to_string(),
        children,
    };
    match &mut surface.0 {
        ViewNode::Section { children, .. } => children.push(record),
        root => {
            let original = root.clone();
            *root = ViewNode::Section {
                title: "Game".to_string(),
                tag: "genuine".to_string(),
                children: vec![original, record],
            };
        }
    }
}

/// Render the complete operation contract into stable, non-interactive Telegram companion pages.
/// Keeping descriptor prose out of the keyboard-bearing message means a rich game surface does not
/// compete with five long cryptographic disclosures for Telegram's 4096-character ceiling.
fn operation_guide_pages(
    key: &str,
    operations: &[BinaryOperationDescriptor],
    shared: bool,
) -> Vec<String> {
    if operations.is_empty() {
        return Vec::new();
    }
    let intro = if shared {
        "Group documents are public. Upload is disabled unless an operation below explicitly says it binds this exact group session and authenticated claimant. /status inspects the resulting record."
            .to_string()
    } else {
        "This is a single-reader chat. Attach a canonical receipt document with the exact caption shown below; /status inspects the resulting record."
            .to_string()
    };
    let mut blocks = vec![intro];
    for operation in operations {
        let maximum = operation
            .max_input_bytes
            .min(dreggnet_offerings::MAX_CHAT_BINARY_OPERATION_BYTES);
        let allowed_here = !shared || shared_operation_allowed(key, &operation.name);
        let mut block = operation.title.clone();
        block.push('\n');
        if allowed_here {
            block.push_str("Caption: /operation ");
            block.push_str(&operation.name);
            block.push('\n');
            if shared {
                block.push_str(
                    "Shared-session exception: the document is public; the live verifier binds the Telegram uploader, exact ordered raid roster, and session-derived proof id. It is not a bearer proof.\n",
                );
            }
        } else {
            block.push_str("Upload here: disabled (use a DM)\n");
        }
        block.push_str("Media type: ");
        block.push_str(&operation.input_media_type);
        block.push_str("\nMaximum: ");
        block.push_str(&maximum.to_string());
        block.push_str(" bytes\nDisclosure: ");
        block.push_str(&operation.disclosure);
        blocks.push(block);
    }

    // Preserve whole descriptor blocks whenever possible; only an individually enormous field is
    // split. Leave ample room for the page number even at absurdly high page counts. Counting and
    // slicing by chars, rather than bytes, matches Telegram's documented Unicode ceiling.
    const BODY_CHARS: usize = 3_900;
    let mut raw_pages = Vec::new();
    let mut current = String::new();
    for block in blocks {
        let block_characters = block.chars().collect::<Vec<_>>();
        if block_characters.len() <= BODY_CHARS {
            let separator = usize::from(!current.is_empty()) * 5;
            if current.chars().count() + separator + block_characters.len() <= BODY_CHARS {
                if !current.is_empty() {
                    current.push_str("\n\n—\n");
                }
                current.push_str(&block);
                continue;
            }
        }
        if !current.is_empty() {
            raw_pages.push(std::mem::take(&mut current));
        }
        for chunk in block_characters.chunks(BODY_CHARS) {
            let part = chunk.iter().collect::<String>();
            if chunk.len() == BODY_CHARS {
                raw_pages.push(part);
            } else {
                current = part;
            }
        }
    }
    if !current.is_empty() {
        raw_pages.push(current);
    }
    let total = raw_pages.len();
    raw_pages
        .into_iter()
        .enumerate()
        .map(|(index, page)| {
            format!(
                "Proof operations · page {}/{}\n\n{}",
                index + 1,
                total,
                page
            )
        })
        .collect()
}

/// **The default Telegram catalog host** — the FULL shared portfolio, from the ONE registrar
/// every frontend builds through ([`dreggnet_catalog::build_full_catalog`]): the nine games
/// (native Descent · Descent campaign · dungeon · council · market · Dark Bazaar · multiway-tug · automatafl · private raid,
/// `tug` wrapped in the shared
/// seat-claiming [`crate::seated::SeatedTug`] adapter), the nine do-once RPG feature surfaces
/// (trade · inventory · cheevos · guild · craft · companion · quest · tavern · party), and the five
/// service offerings (doc · names · compute · grain · hermes) — the same 23 the web catalog
/// (`dreggnet_web::demo_host`) serves, by construction rather than by a duplicated list
/// (docs/BOT-SHARED-BACKEND-DESIGN.md). Call it on the host's owning thread (inside
/// [`HostThread::spawn`]'s build closure) so each offering's `!Send` internals stay confined.
///
/// `council_members` is the electorate (member public keys — a Telegram user whose derived
/// identity is one of these can vote); pass the [`TelegramHost::council_member_pubkey`] of each
/// voter's Telegram id. Every other catalog knob (quorum 2, the two candidate proposals, grain
/// budget 1000) is [`CatalogConfig`]'s deployed default.
///
/// ⚑ THE DAY BINDING: built through [`CatalogConfig::live`], so the Descent (and the campaign
/// over it) mints its banked relics under the CURRENT verified drand day, re-resolved at every
/// open — a live run's relic ids could not exist before that round was revealed. The day is
/// published by [`arm_todays_descent_day`] (boot + periodic refresh); until one is published the
/// Descent REFUSES to open rather than serving the pre-computable seed-derived provenance root.
pub fn telegram_default_host(council_members: Vec<[u8; 32]>) -> OfferingHost {
    dreggnet_catalog::full_catalog_host(&CatalogConfig::live(council_members))
        .with_policy(resolve_telegram_policy(), SystemClock)
}

/// Env knob: the cap on LIVE game sessions per offering the Telegram host holds. Overrides
/// [`DEFAULT_TELEGRAM_MAX_SESSIONS`]. See [`resolve_telegram_policy`].
pub const TELEGRAM_MAX_SESSIONS_ENV: &str = "DREGGNET_TELEGRAM_MAX_SESSIONS";
/// Env knob: idle seconds before the TTL sweep evicts a Telegram game session. Overrides
/// [`DEFAULT_TELEGRAM_SESSION_TTL_SECS`].
pub const TELEGRAM_SESSION_TTL_ENV: &str = "DREGGNET_TELEGRAM_SESSION_TTL_SECS";
/// Env knob: live sessions ONE attributed Telegram opener may hold fresh-minted. Overrides
/// [`DEFAULT_TELEGRAM_OPENS_PER_USER`].
pub const TELEGRAM_OPENS_PER_USER_ENV: &str = "DREGGNET_TELEGRAM_OPENS_PER_USER";

/// Default cap on live sessions per offering (per `(offering, chat)` mint). Bounds the durable
/// session count — and thus memory + disk — under a flood of chats opening games.
pub const DEFAULT_TELEGRAM_MAX_SESSIONS: usize = 256;
/// Default idle TTL: a session untouched this long is swept (and, with the bot's durable store
/// attached, resumes losslessly from its move-log on the next touch).
pub const DEFAULT_TELEGRAM_SESSION_TTL_SECS: u64 = 3_600;
/// Default per-opener fresh-mint quota (bites only on the attributed-open path).
pub const DEFAULT_TELEGRAM_OPENS_PER_USER: usize = 32;

/// **Build the Telegram [`SessionPolicy`] from an env-shaped getter** — the pure seam
/// [`resolve_telegram_policy`] feeds real env vars through; tests feed fixed pairs through (process
/// env is global — tests must not mutate it). Mirrors `dreggnet_web::web_policy_from`, with ONE
/// deliberate difference: the web knobs fall back to `None` (unbounded), but every Telegram knob
/// falls back to a SANE BOUNDED DEFAULT. The Telegram host must never be born unbounded — an
/// anonymous user opening games across chats would otherwise mint durable sessions (memory AND
/// disk) without limit ([`admit_fresh_open`](dreggnet_offerings::OfferingHost) skips every gate on
/// an unbounded policy). An env var only overrides its default; an unparseable value warns and
/// keeps the default (never silently unbounds a gate).
pub fn telegram_policy_from(get: impl Fn(&str) -> Option<String>) -> SessionPolicy {
    fn parse_or<T: std::str::FromStr>(name: &str, v: Option<String>, default: T) -> T {
        match v {
            None => default,
            Some(v) => match v.parse::<T>() {
                Ok(n) => n,
                Err(_) => {
                    eprintln!(
                        "WARN: unparseable session-policy env {name}={v:?} — keeping the bounded default"
                    );
                    default
                }
            },
        }
    }
    SessionPolicy {
        max_sessions_per_offering: Some(parse_or(
            TELEGRAM_MAX_SESSIONS_ENV,
            get(TELEGRAM_MAX_SESSIONS_ENV),
            DEFAULT_TELEGRAM_MAX_SESSIONS,
        )),
        max_opens_per_actor: Some(parse_or(
            TELEGRAM_OPENS_PER_USER_ENV,
            get(TELEGRAM_OPENS_PER_USER_ENV),
            DEFAULT_TELEGRAM_OPENS_PER_USER,
        )),
        idle_ttl_secs: Some(parse_or(
            TELEGRAM_SESSION_TTL_ENV,
            get(TELEGRAM_SESSION_TTL_ENV),
            DEFAULT_TELEGRAM_SESSION_TTL_SECS,
        )),
        min_open_interval_secs: None,
        // Telegram sessions are ephemeral WITHOUT a durable store (a restart re-derives the
        // deterministic genesis anyway), so under the cap/TTL shedding the coldest beats unbounded
        // growth. WITH the bot's `FileResumeStore` attached, eviction stays LOSSLESS regardless
        // (the move-log resumes on next touch) and this flag is moot — the `evict`/sweep paths
        // take the store branch. Mirrors `dreggnet_web`'s store-less lossy-eviction reasoning.
        evict_unpersisted: true,
    }
}

/// [`telegram_policy_from`] over the real process environment — the deployed Telegram host's
/// bounded session-lifecycle policy.
pub fn resolve_telegram_policy() -> SessionPolicy {
    telegram_policy_from(|k| std::env::var(k).ok().filter(|v| !v.is_empty()))
}

/// **Arm (and re-arm) the day this bot's Descent mints relics under** — fetch today's drand
/// round, BLS-verify it, publish it for [`dreggnet_catalog::DescentDayBinding::Live`]. Blocking; run it
/// from `spawn_blocking` at boot and on a timer, since a rolled UTC day makes the published day
/// stale and every Descent open then refuses (fail-closed, by design). The returned
/// [`dreggnet_catalog::BeaconSource`] says whether the day is today's live round or the
/// explicitly-labeled pinned round standing in for a transport outage — log it.
pub fn arm_todays_descent_day()
-> Result<dreggnet_catalog::BeaconSource, dreggnet_catalog::FetchError> {
    dreggnet_catalog::refresh_todays_descent_day(dreggnet_catalog::DRAND_API_BASE)
}

#[cfg(test)]
mod audience_tests {
    use super::*;

    #[test]
    fn collective_rpg_messages_are_viewer_blind_too() {
        let viewer = DreggIdentity("telegram:alice".to_string());

        // RPG sessions are routed to a per-player host, but a group message still has multiple
        // readers. This canary prevents the old `shared || is_rpg_key` exception from returning:
        // the key may choose storage, never the audience of the rendered message.
        assert!(is_rpg_key("inventory"), "canary must exercise an RPG key");
        assert_eq!(audience_for_message(true, &viewer), Audience::Shared);
        assert_eq!(
            audience_for_message(false, &viewer),
            Audience::private(viewer)
        );
    }
}
