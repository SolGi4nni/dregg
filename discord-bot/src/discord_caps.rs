//! Bidirectional integration: Discord actions as capabilities, Discord events as turns.
//!
//! This module defines:
//! 1. `DiscordCapability` — capabilities that, when exercised via CapTP, trigger Discord actions.
//! 2. Event handlers that emit dregg turns when Discord events occur.
//!
//! ## The guild-write engine, and who drives it
//!
//! Every write this bot makes to a guild's *structure* (create a channel, file it
//! under a category, open a thread, assign a role, archive a surface) goes through
//! exactly one place: [`DiscordCapRegistry::exercise`]. A caller does not call
//! serenity directly — it [`DiscordCapRegistry::register`]s a [`DiscordCapability`]
//! (which names the write) and then exercises it by cell id. That indirection is
//! the point: the write is a *capability* with a cell id and a sturdy ref, so it
//! can be held, delegated, revoked ([`DiscordCapRegistry::unregister`]) and driven
//! from CapTP, not just from a slash-command handler.
//!
//! The layer that actually drives it for a *session* — the per-session
//! channel/thread/category/role lifecycle DreggNet Cloud's offerings share — is
//! [`orchestration`]. Read that module for the lifecycle; read this one for the
//! primitive writes it composes.
//!
//! The serenity request each capability builds is constructed by a **pure**
//! `build_*_request` function ([`build_channel_request`] and friends), separate
//! from the live HTTP call. That split is what makes the guild-write surface
//! testable without a Discord token: the tests assert the *shape of the request*
//! we would send.

use std::collections::HashMap;
use std::sync::Arc;

use serenity::all::{
    ChannelId, ChannelType, CreateChannel, CreateThread, EditChannel, EditThread, GuildId, Http,
    Message, MessageId, PermissionOverwrite, RoleId, UserId,
};
use tokio::sync::RwLock;
use tracing::{debug, info, warn};

// The per-session channel/thread lifecycle that DRIVES this engine.
//
// NOTE FOR THE MAIN LOOP: this `#[path]` declaration is a placeholder so the
// module compiles (and its tests run) without touching `main.rs`, which the main
// loop owns. When `main.rs` gains `pub mod orchestration;`, DELETE these two lines
// — `orchestration.rs` uses only absolute `crate::…` paths, so it needs no edit to
// move from `crate::discord_caps::orchestration` to `crate::orchestration`.
#[path = "orchestration.rs"]
pub mod orchestration;

// =============================================================================
// Discord capabilities (dregg → Discord direction)
// =============================================================================

/// The kind of Discord channel to create.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ChannelKind {
    Text,
    Voice,
    Forum,
    Announcement,
    /// A channel *group* — the container a per-offering set of session channels is
    /// filed under. Categories hold no messages; they carry the permission
    /// baseline their children inherit.
    Category,
}

impl ChannelKind {
    /// The serenity `ChannelType` this kind denotes. Total — no fallback arm, so
    /// adding a `ChannelKind` variant is a compile error until it is mapped.
    pub fn channel_type(&self) -> ChannelType {
        match self {
            ChannelKind::Text => ChannelType::Text,
            ChannelKind::Voice => ChannelType::Voice,
            ChannelKind::Forum => ChannelType::Forum,
            ChannelKind::Announcement => ChannelType::News,
            ChannelKind::Category => ChannelType::Category,
        }
    }
}

/// Capabilities that, when exercised via CapTP, trigger Discord actions.
/// Each variant is a cell with a sturdy ref. Someone holding the capability
/// can trigger the action by exercising the cap via CapTP from any dregg client.
///
/// Every variant is plain data (ids, strings, flags) — deliberately: a capability
/// must round-trip through serde to be a sturdy ref, so no serenity builder or
/// permission type is stored here. The overwrites a session channel needs are
/// *derived* at exercise time from `(guild_id, owner_id, admin_id, private)` by
/// [`crate::channels::plan_private_overwrites`], which keeps ONE definition of the
/// semi-private posture for both `/channel` and every session surface.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DiscordCapability {
    /// Send a message to a channel.
    SendMessage { channel_id: u64, content: String },
    /// Assign a role to a user.
    AssignRole {
        guild_id: u64,
        user_id: u64,
        role_id: u64,
    },
    /// Remove a role from a user — the counterpart of [`Self::AssignRole`], so a
    /// session role granted for the duration of a run can be handed back at teardown
    /// (a run-scoped role that outlives its run is a lingering grant).
    RemoveRole {
        guild_id: u64,
        user_id: u64,
        role_id: u64,
    },
    /// Create a channel in a guild.
    CreateChannel {
        guild_id: u64,
        name: String,
        kind: ChannelKind,
    },
    /// Create the per-offering CATEGORY that a set of session channels is filed
    /// under (e.g. one `dreggnet-dungeon` category holding every dungeon run).
    CreateCategory { guild_id: u64, name: String },
    /// Create a per-SESSION channel: optionally under a category, carrying the
    /// semi-private overwrite plan when `private`.
    ///
    /// This is [`Self::CreateChannel`] plus everything a *session* needs — the
    /// parent category, the topic, and the participants whose access the overwrite
    /// plan is derived from.
    CreateSessionChannel {
        guild_id: u64,
        name: String,
        kind: ChannelKind,
        topic: Option<String>,
        /// The parent category, once resolved. `None` = a top-level channel.
        category_id: Option<u64>,
        /// The session's owner — allowed to view + post when `private`.
        owner_id: u64,
        /// The pinned admin (`config.admin_discord_id`) — allowed the same, and by
        /// design sees every session.
        admin_id: Option<u64>,
        /// `true` = semi-private (deny `@everyone` VIEW_CHANNEL);
        /// `false` = guild-visible (a collective run the whole server can watch).
        private: bool,
    },
    /// Open a THREAD for a session under an existing channel — the lighter-weight
    /// session surface (no new channel in the sidebar; archivable natively).
    CreateSessionThread {
        channel_id: u64,
        name: String,
        /// A private thread is visible only to invited members; a public one to
        /// anyone who can see the parent channel.
        private: bool,
    },
    /// TEARDOWN of a thread session: archive it (and lock it, so an archived run
    /// cannot be revived by a stray reply).
    ArchiveThread { channel_id: u64 },
    /// TEARDOWN of a channel session: rename it with the archive prefix, file it
    /// under the archive category if one is given, and re-apply the participants'
    /// rights as a READ-ONLY tombstone
    /// ([`crate::channels::plan_archived_overwrites`]).
    ArchiveChannel {
        guild_id: u64,
        channel_id: u64,
        archived_name: String,
        owner_id: u64,
        admin_id: Option<u64>,
        /// Where completed runs are filed. `None` = leave it where it is.
        archive_category_id: Option<u64>,
    },
    /// Pin a message.
    PinMessage { channel_id: u64, message_id: u64 },
    /// React to a message.
    AddReaction {
        channel_id: u64,
        message_id: u64,
        emoji: String,
    },
}

// =============================================================================
// Pure request builders — the guild-write surface, testable without a token
// =============================================================================
//
// `exercise()` does exactly two things per capability: build a serenity request,
// and send it. The build half lives here as pure functions so the tests can assert
// the EXACT request we would put on the wire (every serenity builder below derives
// `Serialize`, so a test can compare the serialized body field-for-field) without
// a Discord token, a guild, or a network.

/// Build the `CreateChannel` request for a plain channel.
pub fn build_channel_request<'a>(
    name: &str,
    kind: &ChannelKind,
    reason: &'a str,
) -> CreateChannel<'a> {
    CreateChannel::new(name)
        .kind(kind.channel_type())
        .audit_log_reason(reason)
}

/// Build the `CreateChannel` request for a per-offering CATEGORY.
///
/// A category is just a channel of type `Category`; it takes no topic and no
/// parent (Discord does not nest categories).
pub fn build_category_request<'a>(name: &str, reason: &'a str) -> CreateChannel<'a> {
    CreateChannel::new(name)
        .kind(ChannelType::Category)
        .audit_log_reason(reason)
}

/// Build the `CreateChannel` request for a per-SESSION channel: the kind, the
/// topic, the parent category (when the offering groups its runs), and the
/// permission overwrites that gate it.
///
/// The overwrites are passed in rather than computed here so that the ONE
/// definition of the semi-private posture ([`crate::channels`]) stays the only
/// one — this function just places them in the request.
pub fn build_session_channel_request<'a>(
    name: &str,
    kind: &ChannelKind,
    topic: Option<&str>,
    category_id: Option<u64>,
    overwrites: Vec<PermissionOverwrite>,
    reason: &'a str,
) -> CreateChannel<'a> {
    let mut req = CreateChannel::new(name)
        .kind(kind.channel_type())
        .audit_log_reason(reason);
    if let Some(topic) = topic {
        req = req.topic(topic);
    }
    if let Some(category_id) = category_id {
        req = req.category(ChannelId::new(category_id));
    }
    if !overwrites.is_empty() {
        req = req.permissions(overwrites);
    }
    req
}

/// Build the `CreateThread` request for a session thread.
pub fn build_session_thread_request<'a>(
    name: &str,
    private: bool,
    reason: &'a str,
) -> CreateThread<'a> {
    let kind = if private {
        ChannelType::PrivateThread
    } else {
        ChannelType::PublicThread
    };
    CreateThread::new(name).kind(kind).audit_log_reason(reason)
}

/// Build the `EditThread` request that TEARS DOWN a thread session.
///
/// Both flags matter: `archived` files the run away, and `locked` is what stops a
/// stray reply from silently un-archiving it (Discord un-archives a thread on new
/// activity unless it is locked). An archive that any passer-by can reopen is not
/// a teardown.
pub fn build_archive_thread_request<'a>(reason: &'a str) -> EditThread<'a> {
    EditThread::new()
        .archived(true)
        .locked(true)
        .audit_log_reason(reason)
}

/// Build the `EditChannel` request that TEARS DOWN a channel session: rename to
/// the archived name, re-file under the archive category (if any), and apply the
/// read-only tombstone overwrites.
pub fn build_archive_channel_request<'a>(
    archived_name: &str,
    archive_category_id: Option<u64>,
    overwrites: Vec<PermissionOverwrite>,
    reason: &'a str,
) -> EditChannel<'a> {
    let mut req = EditChannel::new()
        .name(archived_name)
        .permissions(overwrites)
        .audit_log_reason(reason);
    if let Some(category_id) = archive_category_id {
        req = req.category(Some(ChannelId::new(category_id)));
    }
    req
}

/// The permission overwrites gating a session surface.
///
/// A *private* session reuses the SAME plan `/channel` uses
/// ([`crate::channels::plan_private_overwrites`]) — deny `@everyone` VIEW, allow
/// the owner and the pinned admin. There is deliberately no second definition of
/// the semi-private posture.
///
/// A *public* session emits NO overwrites: it inherits its parent category's
/// permissions (or, with no category, the guild's `@everyone` baseline). Emitting
/// an empty overwrite list is not the same as emitting allow-everything — it means
/// "do not override", which is what a collective run the whole server can watch
/// actually wants.
///
/// Note the `@everyone` role id *is* the guild id in Discord — that identity is
/// the only reason `guild_id` is needed here.
pub fn session_overwrites(
    guild_id: u64,
    owner_id: u64,
    admin_id: Option<u64>,
    private: bool,
) -> Vec<PermissionOverwrite> {
    if !private {
        return Vec::new();
    }
    crate::channels::plan_private_overwrites(
        RoleId::new(guild_id),
        UserId::new(owner_id),
        admin_id.map(UserId::new),
    )
}

/// Map a serenity error into our capability error. A free function (not a closure)
/// so it stays `Copy` and can be handed to `map_err` at every call site.
fn api_err(e: serenity::Error) -> DiscordCapError {
    DiscordCapError::DiscordApi(e.to_string())
}

/// The guild audit-log reason attached to every write, naming the capability cell
/// that drove it. A guild admin auditing "who created this channel?" gets the cell
/// id, not just "the bot".
fn audit_reason(cell_id: &str) -> String {
    // Discord caps the X-Audit-Log-Reason header at 512 chars.
    let reason = format!("dregg capability {cell_id}");
    reason.chars().take(500).collect()
}

/// The result of exercising a capability.
///
/// `exercise` used to return `()`, which is precisely why the engine could not be
/// driven: a `CreateChannel` whose minted channel id is thrown away cannot be
/// linked to a queue, posted into, or torn down. The id comes back now.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExerciseOutcome {
    /// The id Discord minted, for the capabilities that create something (a
    /// channel, a category, a thread). `None` for the pure side-effects.
    pub created_id: Option<u64>,
}

impl ExerciseOutcome {
    /// The outcome of an action that created nothing.
    fn none() -> Self {
        Self { created_id: None }
    }

    /// The outcome of an action that minted a channel/category/thread.
    fn created(id: u64) -> Self {
        Self {
            created_id: Some(id),
        }
    }
}

/// A registered Discord capability with its cell ID and metadata.
#[derive(Debug, Clone)]
pub struct RegisteredDiscordCap {
    /// The cell ID for this capability.
    pub cell_id: String,
    /// The dregg URI (sturdy ref) for this capability.
    pub uri: Option<String>,
    /// The capability definition.
    pub capability: DiscordCapability,
    /// Guild this belongs to.
    pub guild_id: u64,
    /// Who registered it.
    pub registered_by: u64,
}

/// Registry of Discord capabilities that can be exercised via CapTP.
#[derive(Debug)]
pub struct DiscordCapRegistry {
    /// Map from cell_id to registered capability.
    caps: RwLock<HashMap<String, RegisteredDiscordCap>>,
}

impl DiscordCapRegistry {
    pub fn new() -> Self {
        Self {
            caps: RwLock::new(HashMap::new()),
        }
    }

    /// Register a new Discord capability.
    pub async fn register(&self, cap: RegisteredDiscordCap) {
        let cell_id = cap.cell_id.clone();
        self.caps.write().await.insert(cell_id.clone(), cap);
        info!(cell_id, "Registered Discord capability");
    }

    /// Look up a registered capability without exercising it.
    pub async fn get(&self, cell_id: &str) -> Option<RegisteredDiscordCap> {
        self.caps.read().await.get(cell_id).cloned()
    }

    /// Exercise a capability — execute the Discord action, and return whatever id
    /// Discord minted (see [`ExerciseOutcome`]).
    ///
    /// The `reason` recorded in the guild's audit log names the cell that drove the
    /// write, so a guild admin looking at "who created this channel?" sees the
    /// capability, not just "the bot".
    pub async fn exercise(
        &self,
        cell_id: &str,
        http: &Arc<Http>,
    ) -> Result<ExerciseOutcome, DiscordCapError> {
        // Clone the capability out and DROP the read guard before doing network I/O:
        // holding it across an await would block every other session's register()
        // for the duration of a Discord round-trip.
        let cap = self
            .get(cell_id)
            .await
            .ok_or_else(|| DiscordCapError::NotFound(cell_id.to_string()))?;

        let reason = audit_reason(cell_id);

        let outcome = match &cap.capability {
            DiscordCapability::SendMessage {
                channel_id,
                content,
            } => {
                ChannelId::new(*channel_id)
                    .say(http, content)
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::AssignRole {
                guild_id,
                user_id,
                role_id,
            } => {
                GuildId::new(*guild_id)
                    .member(http, UserId::new(*user_id))
                    .await
                    .map_err(api_err)?
                    .add_role(http, RoleId::new(*role_id))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::RemoveRole {
                guild_id,
                user_id,
                role_id,
            } => {
                GuildId::new(*guild_id)
                    .member(http, UserId::new(*user_id))
                    .await
                    .map_err(api_err)?
                    .remove_role(http, RoleId::new(*role_id))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::CreateChannel {
                guild_id,
                name,
                kind,
            } => {
                let channel = GuildId::new(*guild_id)
                    .create_channel(http, build_channel_request(name, kind, &reason))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::created(channel.id.get())
            }
            DiscordCapability::CreateCategory { guild_id, name } => {
                let channel = GuildId::new(*guild_id)
                    .create_channel(http, build_category_request(name, &reason))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::created(channel.id.get())
            }
            DiscordCapability::CreateSessionChannel {
                guild_id,
                name,
                kind,
                topic,
                category_id,
                owner_id,
                admin_id,
                private,
            } => {
                let overwrites = session_overwrites(*guild_id, *owner_id, *admin_id, *private);
                let req = build_session_channel_request(
                    name,
                    kind,
                    topic.as_deref(),
                    *category_id,
                    overwrites,
                    &reason,
                );
                let channel = GuildId::new(*guild_id)
                    .create_channel(http, req)
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::created(channel.id.get())
            }
            DiscordCapability::CreateSessionThread {
                channel_id,
                name,
                private,
            } => {
                let thread = ChannelId::new(*channel_id)
                    .create_thread(http, build_session_thread_request(name, *private, &reason))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::created(thread.id.get())
            }
            DiscordCapability::ArchiveThread { channel_id } => {
                ChannelId::new(*channel_id)
                    .edit_thread(http, build_archive_thread_request(&reason))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::ArchiveChannel {
                guild_id,
                channel_id,
                archived_name,
                owner_id,
                admin_id,
                archive_category_id,
            } => {
                let overwrites = crate::channels::plan_archived_overwrites(
                    RoleId::new(*guild_id),
                    UserId::new(*owner_id),
                    admin_id.map(UserId::new),
                );
                let req = build_archive_channel_request(
                    archived_name,
                    *archive_category_id,
                    overwrites,
                    &reason,
                );
                ChannelId::new(*channel_id)
                    .edit(http, req)
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::PinMessage {
                channel_id,
                message_id,
            } => {
                ChannelId::new(*channel_id)
                    .pin(http, MessageId::new(*message_id))
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
            DiscordCapability::AddReaction {
                channel_id,
                message_id,
                emoji,
            } => {
                let reaction = serenity::all::ReactionType::Unicode(emoji.clone());
                ChannelId::new(*channel_id)
                    .create_reaction(http, MessageId::new(*message_id), reaction)
                    .await
                    .map_err(api_err)?;
                ExerciseOutcome::none()
            }
        };

        debug!(cell_id, created = ?outcome.created_id, "Exercised Discord capability");
        Ok(outcome)
    }

    /// List all registered capabilities for a guild.
    pub async fn list_for_guild(&self, guild_id: u64) -> Vec<RegisteredDiscordCap> {
        self.caps
            .read()
            .await
            .values()
            .filter(|c| c.guild_id == guild_id)
            .cloned()
            .collect()
    }

    /// Unregister a capability.
    pub async fn unregister(&self, cell_id: &str) -> bool {
        self.caps.write().await.remove(cell_id).is_some()
    }
}

/// Errors from Discord capability operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiscordCapError {
    /// Capability not found in registry.
    NotFound(String),
    /// Discord API error.
    DiscordApi(String),
    /// Unauthorized (invoker doesn't hold the cap).
    Unauthorized(String),
}

impl std::fmt::Display for DiscordCapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiscordCapError::NotFound(id) => write!(f, "capability not found: {id}"),
            DiscordCapError::DiscordApi(e) => write!(f, "Discord API error: {e}"),
            DiscordCapError::Unauthorized(e) => write!(f, "unauthorized: {e}"),
        }
    }
}

impl std::error::Error for DiscordCapError {}

// =============================================================================
// Discord events → Dragon's Egg turns (Discord → dregg direction)
// =============================================================================

/// Queue link configuration: maps a Discord channel to a dregg programmable queue.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelQueueLink {
    /// Discord channel ID.
    pub channel_id: u64,
    /// Guild ID.
    pub guild_id: u64,
    /// Queue name in the dregg namespace.
    pub queue_name: String,
    /// Full namespace path (e.g., /discord/<guild-id>/<name>).
    pub namespace_path: String,
}

/// Event bridge: converts Discord events into dregg turns.
#[derive(Debug)]
pub struct EventBridge {
    /// Active channel-to-queue links.
    channel_links: RwLock<HashMap<u64, ChannelQueueLink>>,
    /// Node URL for submitting turns.
    node_url: String,
    /// HTTP client.
    http: reqwest::Client,
}

impl EventBridge {
    pub fn new(node_url: String) -> Self {
        Self {
            channel_links: RwLock::new(HashMap::new()),
            node_url,
            http: reqwest::Client::new(),
        }
    }

    /// Link a channel to a programmable queue.
    pub async fn link_channel(&self, link: ChannelQueueLink) {
        let channel_id = link.channel_id;
        self.channel_links.write().await.insert(channel_id, link);
        info!(channel_id, "Linked channel to dregg queue");
    }

    /// Unlink a channel.
    pub async fn unlink_channel(&self, channel_id: u64) -> bool {
        self.channel_links
            .write()
            .await
            .remove(&channel_id)
            .is_some()
    }

    /// Handle a Discord message event — enqueue into linked dregg queue if applicable.
    pub async fn on_message(&self, msg: &Message) {
        let channel_id = msg.channel_id.get();
        let links = self.channel_links.read().await;

        if let Some(link) = links.get(&channel_id) {
            let payload = serde_json::json!({
                "type": "message",
                "channel_id": channel_id,
                "guild_id": link.guild_id,
                "author_id": msg.author.id.get(),
                "author_name": msg.author.name,
                "content": msg.content,
                "timestamp": msg.timestamp.to_string(),
                "queue": link.queue_name,
            });

            if let Err(e) = self.submit_turn(&link.namespace_path, payload).await {
                warn!(
                    channel_id,
                    queue = link.queue_name,
                    error = %e,
                    "Failed to enqueue message into dregg queue"
                );
            }
        }
    }

    /// Handle a role change event — emit GrantCapability or RevokeCapability effect.
    pub async fn on_role_change(&self, guild_id: u64, user_id: u64, role_id: u64, added: bool) {
        let effect_type = if added {
            "GrantCapability"
        } else {
            "RevokeCapability"
        };

        let payload = serde_json::json!({
            "type": effect_type,
            "guild_id": guild_id,
            "user_id": user_id,
            "role_id": role_id,
            "added": added,
        });

        let path = format!("/discord/{guild_id}/roles");
        if let Err(e) = self.submit_turn(&path, payload).await {
            warn!(
                guild_id,
                user_id,
                role_id,
                error = %e,
                "Failed to emit role change turn"
            );
        }
    }

    /// Handle a reaction event — if it's on a governance proposal, count as a vote.
    pub async fn on_reaction(
        &self,
        guild_id: u64,
        channel_id: u64,
        message_id: u64,
        user_id: u64,
        emoji: &str,
        added: bool,
    ) {
        let vote = match emoji {
            "\u{1f44d}" | "+1" => Some(true),  // thumbs up = yes
            "\u{1f44e}" | "-1" => Some(false), // thumbs down = no
            _ => None,
        };

        if let Some(vote_yes) = vote {
            let payload = serde_json::json!({
                "type": "ReactionVote",
                "guild_id": guild_id,
                "channel_id": channel_id,
                "message_id": message_id,
                "user_id": user_id,
                "vote": if vote_yes { "yes" } else { "no" },
                "added": added,
            });

            let path = format!("/discord/{guild_id}/governance");
            if let Err(e) = self.submit_turn(&path, payload).await {
                warn!(
                    guild_id,
                    message_id,
                    error = %e,
                    "Failed to emit reaction vote turn"
                );
            }
        }
    }

    /// Submit a turn to the dregg node.
    async fn submit_turn(
        &self,
        namespace_path: &str,
        payload: serde_json::Value,
    ) -> Result<(), String> {
        let url = format!("{}/turns/submit", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "namespace_path": namespace_path,
                "payload": payload,
            }))
            .send()
            .await
            .map_err(|e| e.to_string())?;

        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            return Err(format!("node returned error: {body}"));
        }

        Ok(())
    }
}

// =============================================================================
// Tests — the guild-write REQUEST SHAPES, driven without a Discord token
// =============================================================================
//
// Every serenity builder below derives `Serialize`, and `exercise()` sends exactly
// what these builders produce. So serializing the builder IS the request body that
// would go on the wire: asserting on it is asserting on the real request, not on a
// re-description of one. What these tests CANNOT cover is Discord's response —
// whether the guild grants MANAGE_CHANNELS, whether the category exists, what id
// gets minted. That needs a live guild (see the module docs).

#[cfg(test)]
mod tests {
    use super::*;
    use serenity::all::Permissions;

    /// The body `exercise()` would PUT/POST for this request.
    fn body<T: serde::Serialize>(req: &T) -> serde_json::Value {
        serde_json::to_value(req).expect("a serenity builder serializes")
    }

    /// serenity encodes ids and permission bitfields as strings; comparing against
    /// `to_value(expected)` keeps these assertions independent of that encoding.
    fn as_val<T: serde::Serialize>(v: T) -> serde_json::Value {
        serde_json::to_value(v).unwrap()
    }

    const GUILD: u64 = 1111;
    const OWNER: u64 = 2222;
    const ADMIN: u64 = 3333;
    const CATEGORY: u64 = 4444;

    #[test]
    fn channel_kind_maps_to_the_serenity_type() {
        assert_eq!(ChannelKind::Text.channel_type(), ChannelType::Text);
        assert_eq!(ChannelKind::Voice.channel_type(), ChannelType::Voice);
        assert_eq!(ChannelKind::Forum.channel_type(), ChannelType::Forum);
        assert_eq!(ChannelKind::Announcement.channel_type(), ChannelType::News);
        assert_eq!(ChannelKind::Category.channel_type(), ChannelType::Category);
    }

    #[test]
    fn category_request_is_a_category_with_no_parent() {
        let req = build_category_request("dreggnet-dungeon", "r");
        let b = body(&req);

        assert_eq!(b["name"], "dreggnet-dungeon");
        assert_eq!(b["type"], as_val(ChannelType::Category));
        assert!(
            b.get("parent_id").is_none(),
            "Discord does not nest categories"
        );
        assert!(b.get("permission_overwrites").is_none());
    }

    #[test]
    fn private_session_channel_request_is_gated_and_filed_under_its_category() {
        // The exact request `exercise(CreateSessionChannel { .. })` builds.
        let overwrites = session_overwrites(GUILD, OWNER, Some(ADMIN), true);
        let req = build_session_channel_request(
            "dungeon-a1b2c3",
            &ChannelKind::Text,
            Some("a dungeon run"),
            Some(CATEGORY),
            overwrites,
            "r",
        );
        let b = body(&req);

        assert_eq!(b["name"], "dungeon-a1b2c3");
        assert_eq!(b["type"], as_val(ChannelType::Text));
        assert_eq!(b["topic"], "a dungeon run");
        // The CHILD half of the category/child plan: the request names its parent.
        assert_eq!(
            b["parent_id"],
            as_val(ChannelId::new(CATEGORY)),
            "the session channel must be filed under the offering's category"
        );

        // The GATE: @everyone denied VIEW; owner + admin allowed view/post.
        let ovr = b["permission_overwrites"]
            .as_array()
            .expect("overwrites are on the request");
        assert_eq!(ovr.len(), 3, "everyone-deny + owner-allow + admin-allow");

        // `@everyone`'s role id IS the guild id.
        let everyone = ovr
            .iter()
            .find(|o| o["id"] == as_val(RoleId::new(GUILD)))
            .expect("an @everyone overwrite");
        assert_eq!(everyone["type"], 0, "0 = a role overwrite");
        assert_eq!(everyone["deny"], as_val(Permissions::VIEW_CHANNEL));
        assert_eq!(everyone["allow"], as_val(Permissions::empty()));

        for who in [OWNER, ADMIN] {
            let m = ovr
                .iter()
                .find(|o| o["id"] == as_val(UserId::new(who)))
                .expect("a member overwrite");
            assert_eq!(m["type"], 1, "1 = a member overwrite");
            assert_eq!(
                m["allow"],
                as_val(
                    Permissions::VIEW_CHANNEL
                        | Permissions::SEND_MESSAGES
                        | Permissions::READ_MESSAGE_HISTORY
                )
            );
        }
    }

    #[test]
    fn a_public_session_overrides_nothing_and_inherits_the_category() {
        // A collective run the whole server can watch: NO overwrites — not
        // allow-everything, but "do not override the category/guild baseline".
        let overwrites = session_overwrites(GUILD, OWNER, Some(ADMIN), false);
        assert!(overwrites.is_empty());

        let req = build_session_channel_request(
            "dungeon-public",
            &ChannelKind::Text,
            None,
            Some(CATEGORY),
            overwrites,
            "r",
        );
        let b = body(&req);
        assert!(
            b.get("permission_overwrites").is_none(),
            "a public session must not emit an overwrite that overrides its category"
        );
        assert_eq!(b["parent_id"], as_val(ChannelId::new(CATEGORY)));
        assert!(b.get("topic").is_none());
    }

    #[test]
    fn a_top_level_session_channel_names_no_parent() {
        let req = build_session_channel_request(
            "dungeon-solo",
            &ChannelKind::Text,
            None,
            None,
            session_overwrites(GUILD, OWNER, None, true),
            "r",
        );
        let b = body(&req);
        assert!(b.get("parent_id").is_none());
        // With no admin pinned, the gate is still owner-only.
        assert_eq!(b["permission_overwrites"].as_array().unwrap().len(), 2);
    }

    #[test]
    fn session_thread_request_kind_follows_privacy() {
        let private = body(&build_session_thread_request("dungeon-a1", true, "r"));
        assert_eq!(private["name"], "dungeon-a1");
        assert_eq!(private["type"], as_val(ChannelType::PrivateThread));

        let public = body(&build_session_thread_request("dungeon-a1", false, "r"));
        assert_eq!(public["type"], as_val(ChannelType::PublicThread));
    }

    // ─── teardown ────────────────────────────────────────────────────────────

    #[test]
    fn archiving_a_thread_both_archives_and_locks_it() {
        let b = body(&build_archive_thread_request("r"));
        assert_eq!(b["archived"], true);
        assert_eq!(
            b["locked"], true,
            "an unlocked archived thread un-archives on the next reply — that is not a teardown"
        );
    }

    #[test]
    fn archiving_a_channel_renames_refiles_and_makes_it_read_only() {
        let overwrites = crate::channels::plan_archived_overwrites(
            RoleId::new(GUILD),
            UserId::new(OWNER),
            Some(UserId::new(ADMIN)),
        );
        let req = build_archive_channel_request(
            "archived-dungeon-a1b2c3",
            Some(CATEGORY),
            overwrites,
            "r",
        );
        let b = body(&req);

        assert_eq!(b["name"], "archived-dungeon-a1b2c3");
        assert_eq!(
            b["parent_id"],
            as_val(ChannelId::new(CATEGORY)),
            "a completed run is re-filed under the archive category"
        );

        let ovr = b["permission_overwrites"].as_array().unwrap();
        assert_eq!(ovr.len(), 3);
        // The run stays private...
        let everyone = ovr
            .iter()
            .find(|o| o["id"] == as_val(RoleId::new(GUILD)))
            .unwrap();
        assert_eq!(everyone["deny"], as_val(Permissions::VIEW_CHANNEL));
        // ...and the participants can read it but can no longer write to it.
        for who in [OWNER, ADMIN] {
            let m = ovr
                .iter()
                .find(|o| o["id"] == as_val(UserId::new(who)))
                .unwrap();
            assert_eq!(
                m["allow"],
                as_val(Permissions::VIEW_CHANNEL | Permissions::READ_MESSAGE_HISTORY)
            );
            assert_eq!(m["deny"], as_val(Permissions::SEND_MESSAGES));
        }
    }

    #[test]
    fn archiving_a_channel_without_an_archive_category_leaves_it_in_place() {
        let b = body(&build_archive_channel_request(
            "archived-x",
            None,
            Vec::new(),
            "r",
        ));
        assert!(
            b.get("parent_id").is_none(),
            "no archive category => do not move the channel"
        );
    }

    // ─── the registry: register -> exercise -> unregister ────────────────────

    #[tokio::test]
    async fn exercising_an_unregistered_cell_is_not_found() {
        let reg = DiscordCapRegistry::new();
        // No Discord token is needed to prove the NotFound path: lookup precedes I/O.
        let http = Arc::new(Http::new("Bot invalid"));
        let err = reg
            .exercise("discord/session/dungeon/x/surface", &http)
            .await;
        assert!(matches!(err, Err(DiscordCapError::NotFound(_))));
    }

    #[tokio::test]
    async fn a_registered_cap_is_retrievable_and_revocable() {
        let reg = DiscordCapRegistry::new();
        let cap = DiscordCapability::CreateSessionChannel {
            guild_id: GUILD,
            name: "dungeon-a1".into(),
            kind: ChannelKind::Text,
            topic: None,
            category_id: Some(CATEGORY),
            owner_id: OWNER,
            admin_id: Some(ADMIN),
            private: true,
        };
        reg.register(RegisteredDiscordCap {
            cell_id: "cell-1".into(),
            uri: None,
            capability: cap.clone(),
            guild_id: GUILD,
            registered_by: ADMIN,
        })
        .await;

        assert_eq!(reg.get("cell-1").await.unwrap().capability, cap);
        assert_eq!(reg.list_for_guild(GUILD).await.len(), 1);
        assert_eq!(reg.list_for_guild(9999).await.len(), 0);

        // Revocation is what stops a finished session's guild-write cap from
        // lingering as a live authority.
        assert!(reg.unregister("cell-1").await);
        assert!(reg.get("cell-1").await.is_none());
        assert!(!reg.unregister("cell-1").await, "revoking twice is a no-op");
    }
}
