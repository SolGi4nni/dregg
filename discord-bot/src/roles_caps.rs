//! Discord roles as dregg capabilities — the native-Discord deepening of the cap system.
//!
//! Two directions, and one honest boundary between them.
//!
//! **Role → cap (a gate).** A guild role is a fact Discord already tracks about a
//! member. This module maps a role id to a [`DreggCap`] TAG, so an offering or a
//! command can gate a slot on "does this member hold cap X?" without inventing its
//! own membership store. [`RoleCapMap::caps_for_roles`] reads the invoking member's
//! [`serenity::all::Member::roles`] and yields the caps those roles stand for; a
//! caller gates with [`RoleCapMap::holds`]. This is a *convenience* gate — a
//! locked-but-pressable slot (the same posture `dreggnet_offerings::Action::enabled`
//! takes: the tooth is *shown, not hidden*, and it is only a decoration).
//!
//! **Proof → role (a grant).** When a member earns something the server can verify
//! — tops the Descent board, completes `/credential verify` — the mapped role is
//! assigned via the Discord API ([`grant_cap_role`], which calls
//! [`serenity::all::Member::add_role`] exactly as
//! [`crate::discord_caps::DiscordCapability::AssignRole`] does). The bot needs the
//! **Manage Roles** guild permission to do this; without it the grant returns a
//! clear [`GrantOutcome::MissingManageRoles`], never a panic. The grant is
//! idempotent: a member who already holds the role is a [`GrantOutcome::AlreadyHeld`]
//! no-op.
//!
//! ## The honest boundary — a role is an attestation, not a proof
//!
//! A Discord role is an **attestation by Discord** (and by whoever in the guild can
//! hand roles out). It is convenient, revocable, and legible — and it is exactly as
//! trustworthy as the guild's role administration, no more. It is NOT a dregg proof.
//!
//! So the rule this module keeps: a role may GATE a surface (a UX convenience, and a
//! cheap first filter), but where authority must be **cryptographic** — where the
//! answer has to survive an adversary who controls their own client — the referee is
//! the real cap system, not the role. That referee is the executor (a `TurnReceipt`
//! is refused or it lands) and the macaroon keychain
//! (`dregg_sdk::AgentCipherclerk::{mint_token, attenuate, verify_token}`, surfaced as
//! `/cipherclerk mint | attenuate | authorize`). A held role that *says* "verified"
//! is a hint to show the button; the `verify_token` / executor check is what actually
//! decides whether the effect is allowed to happen. The two are wired so the role can
//! never be *the* authority for anything a forged client could exploit.

use std::collections::{BTreeSet, HashMap};

use serenity::all::{GuildId, Http, Member, RoleId, UserId};

/// A well-known dregg capability a Discord role can stand for.
///
/// Closed on purpose: keeping the set finite makes [`RoleCapMap::caps_for_roles`]
/// total and auditable (the same reasoning as `cipherclerk::MINTABLE_SERVICES`), and
/// gives every cap a stable wire `tag` for the `ROLE_CAP_MAP` env config.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DreggCap {
    /// The server has attested this member as an identity-verified holder (e.g. they
    /// passed `/credential verify`). Gates surfaces that want "a real, checked human".
    VerifiedHolder,
    /// Topped the Descent leaderboard — the achievement role, *granted* by a verified
    /// win (see [`Achievement::VerifiedDescentWin`]), not self-assigned.
    DescentChampion,
    /// May participate in governance (a council seat role).
    CouncilVoter,
    /// A paying patron (credits pledged / a supporter tier).
    Patron,
}

impl DreggCap {
    /// Every known cap — the enumeration the env parser and the audit surfaces walk.
    pub const ALL: &'static [DreggCap] = &[
        DreggCap::VerifiedHolder,
        DreggCap::DescentChampion,
        DreggCap::CouncilVoter,
        DreggCap::Patron,
    ];

    /// The stable wire tag (used in the `ROLE_CAP_MAP` env config and audit lines).
    pub fn tag(self) -> &'static str {
        match self {
            DreggCap::VerifiedHolder => "verified_holder",
            DreggCap::DescentChampion => "descent_champion",
            DreggCap::CouncilVoter => "council_voter",
            DreggCap::Patron => "patron",
        }
    }

    /// Parse a wire tag back to a cap. Total over [`DreggCap::ALL`]; `None` otherwise.
    pub fn from_tag(tag: &str) -> Option<DreggCap> {
        DreggCap::ALL.iter().copied().find(|c| c.tag() == tag)
    }

    /// A short human label for embeds.
    pub fn label(self) -> &'static str {
        match self {
            DreggCap::VerifiedHolder => "Verified Holder",
            DreggCap::DescentChampion => "Descent Champion",
            DreggCap::CouncilVoter => "Council Voter",
            DreggCap::Patron => "Patron",
        }
    }
}

/// A bidirectional role ↔ cap table.
///
/// Stored as raw `u64` role ids (Discord snowflakes) rather than [`RoleId`] so it
/// round-trips through the env config and serde without newtype friction; conversion
/// to `RoleId` happens only at the API edge. A role id of `0` is never stored (it is
/// not a valid snowflake), so the map is always well-formed.
#[derive(Debug, Clone, Default)]
pub struct RoleCapMap {
    role_to_cap: HashMap<u64, DreggCap>,
    cap_to_role: HashMap<DreggCap, u64>,
}

impl RoleCapMap {
    /// The env var carrying the guild's role↔cap table.
    pub const ENV_VAR: &'static str = "ROLE_CAP_MAP";

    /// Build a map from `(cap, role_id)` pairs. Later pairs win on a collision in
    /// either direction, so the table stays a function both ways. Pairs with a
    /// zero role id are dropped (not a valid snowflake).
    pub fn from_pairs(pairs: impl IntoIterator<Item = (DreggCap, u64)>) -> Self {
        let mut map = RoleCapMap::default();
        for (cap, role_id) in pairs {
            map.insert(cap, role_id);
        }
        map
    }

    /// Insert one binding, keeping BOTH directions consistent: if this cap was bound
    /// to a different role (or this role to a different cap), the stale binding is
    /// dropped so neither index can lie. A zero role id is ignored.
    pub fn insert(&mut self, cap: DreggCap, role_id: u64) {
        if role_id == 0 {
            return;
        }
        // Drop any stale binding this role/cap previously had, in both directions.
        if let Some(old_cap) = self.role_to_cap.remove(&role_id) {
            self.cap_to_role.remove(&old_cap);
        }
        if let Some(old_role) = self.cap_to_role.insert(cap, role_id) {
            self.role_to_cap.remove(&old_role);
        }
        self.role_to_cap.insert(role_id, cap);
    }

    /// Load the table from [`RoleCapMap::ENV_VAR`]. Format: comma-separated
    /// `tag:role_id` pairs, e.g. `verified_holder:112233445566,descent_champion:998877`.
    /// Malformed entries (unknown tag, non-numeric or zero id) are skipped with a
    /// warning; an unset env var yields an empty map (every gate then simply refuses
    /// and every grant reports "no mapping" — fail-closed, not fail-open).
    pub fn from_env() -> Self {
        match std::env::var(Self::ENV_VAR) {
            Ok(raw) => Self::parse(&raw),
            Err(_) => {
                tracing::info!(
                    "{} not set; role→cap gating is inert until it is configured",
                    Self::ENV_VAR
                );
                RoleCapMap::default()
            }
        }
    }

    /// Parse the `ROLE_CAP_MAP` wire form (see [`from_env`](Self::from_env)).
    pub fn parse(raw: &str) -> Self {
        let mut map = RoleCapMap::default();
        for entry in raw.split(',') {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let Some((tag, id_str)) = entry.split_once(':') else {
                tracing::warn!(entry, "ROLE_CAP_MAP entry is not `tag:role_id`; skipping");
                continue;
            };
            let Some(cap) = DreggCap::from_tag(tag.trim()) else {
                tracing::warn!(tag = tag.trim(), "ROLE_CAP_MAP: unknown cap tag; skipping");
                continue;
            };
            match id_str.trim().parse::<u64>() {
                Ok(id) if id != 0 => map.insert(cap, id),
                _ => tracing::warn!(
                    id = id_str.trim(),
                    "ROLE_CAP_MAP: role id is not a nonzero u64; skipping"
                ),
            }
        }
        map
    }

    /// The role id bound to a cap, if any.
    pub fn role_for(&self, cap: DreggCap) -> Option<RoleId> {
        self.cap_to_role.get(&cap).map(|&id| RoleId::new(id))
    }

    /// The cap a role stands for, if any.
    pub fn cap_for(&self, role: RoleId) -> Option<DreggCap> {
        self.role_to_cap.get(&role.get()).copied()
    }

    /// The number of bindings — a `/roles` status line, and a "is anything wired?" check.
    pub fn len(&self) -> usize {
        self.cap_to_role.len()
    }

    /// Whether the table is empty (nothing wired yet).
    pub fn is_empty(&self) -> bool {
        self.cap_to_role.is_empty()
    }

    // ─── Role → cap (the gate) ───────────────────────────────────────────────

    /// The set of caps a member holds, derived from their Discord roles.
    ///
    /// This is the read a gate consults. It is honest about its own resolution: the
    /// caps here are exactly those the guild's role administration has handed out —
    /// a Discord attestation, not a dregg proof (see the module docs).
    pub fn caps_for_roles(&self, roles: &[RoleId]) -> BTreeSet<DreggCap> {
        roles.iter().filter_map(|&r| self.cap_for(r)).collect()
    }

    /// Whether a member holding `roles` holds `cap` — the gate predicate.
    pub fn holds(&self, roles: &[RoleId], cap: DreggCap) -> bool {
        roles.iter().any(|&r| self.cap_for(r) == Some(cap))
    }

    /// Gate a surface on a cap: `Ok(())` if the member holds it, else a legible
    /// [`Denied`] naming the cap and (when the table knows one) the role that grants
    /// it, so the refusal can tell the member exactly how to unlock it.
    pub fn gate(&self, roles: &[RoleId], cap: DreggCap) -> Result<(), Denied> {
        if self.holds(roles, cap) {
            Ok(())
        } else {
            Err(Denied {
                needed: cap,
                granting_role: self.role_for(cap),
            })
        }
    }
}

/// A gate refusal — the cap the surface needed and the role that would grant it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Denied {
    /// The cap the member lacked.
    pub needed: DreggCap,
    /// The role that grants it, if the guild has one wired. `None` = the table has
    /// no role for this cap (nothing can currently unlock it here).
    pub granting_role: Option<RoleId>,
}

impl Denied {
    /// A one-line, legible reason for an embed.
    pub fn message(&self) -> String {
        match self.granting_role {
            Some(role) => format!(
                "This needs the **{}** capability. In this server that is the <@&{}> role; \
                 earn or request it, then try again.",
                self.needed.label(),
                role.get()
            ),
            None => format!(
                "This needs the **{}** capability, but no role is wired to grant it in this \
                 server yet.",
                self.needed.label()
            ),
        }
    }
}

// ─── Proof → role (the grant) ────────────────────────────────────────────────

/// A verifiable achievement that grants a mapped role.
///
/// Each variant names a fact the server can CHECK (not a self-claim): the grant seam
/// fires only after the real verification has already passed (a re-verified board win,
/// a `verify_token`-accepted credential presentation), so the role is downstream of a
/// proof — the role is the *convenient badge*, the proof is what earned it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Achievement {
    /// A Descent run whose recorded move line re-verified to a leaderboard-topping win
    /// (the no-cheat board's replay gate; see `commands::descent`). Grants
    /// [`DreggCap::DescentChampion`].
    VerifiedDescentWin,
    /// A completed `/credential verify` — a real selective-disclosure presentation the
    /// verifier accepted (see `commands::proof_verify` / `AgentCipherclerk::verify_token`).
    /// Grants [`DreggCap::VerifiedHolder`].
    IdentityVerified,
}

impl Achievement {
    /// The cap this achievement grants.
    pub fn granted_cap(self) -> DreggCap {
        match self {
            Achievement::VerifiedDescentWin => DreggCap::DescentChampion,
            Achievement::IdentityVerified => DreggCap::VerifiedHolder,
        }
    }
}

/// The pure decision half of a grant, factored out of the Discord I/O so idempotency
/// is testable without a live guild (the same pure/effect split
/// `discord_caps::build_*_request` uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrantPlan {
    /// The member already holds the role — assigning it again is a no-op.
    AlreadyHeld,
    /// The member lacks the role — assign it.
    Grant,
}

/// Decide whether a member with `current_roles` needs `role` assigned. Idempotent:
/// holding the role already is [`GrantPlan::AlreadyHeld`].
pub fn plan_grant(current_roles: &[RoleId], role: RoleId) -> GrantPlan {
    if current_roles.contains(&role) {
        GrantPlan::AlreadyHeld
    } else {
        GrantPlan::Grant
    }
}

/// The outcome of a role grant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrantOutcome {
    /// The role was assigned.
    Granted { role: RoleId },
    /// The member already held the role (idempotent no-op).
    AlreadyHeld { role: RoleId },
    /// No role is wired to the achievement's cap in this guild — nothing to grant.
    NoMapping { cap: DreggCap },
    /// The bot lacks the **Manage Roles** guild permission (or the target role is
    /// above the bot's highest role). The grant did not happen; this is a
    /// configuration problem for the guild admin, not a bug.
    MissingManageRoles { role: RoleId, detail: String },
    /// Any other Discord API failure — carried as a string so the caller can surface
    /// it without matching serenity's error taxonomy.
    Failed { detail: String },
}

impl GrantOutcome {
    /// A legible one-line summary for an embed / audit line.
    pub fn message(&self) -> String {
        match self {
            GrantOutcome::Granted { role } => {
                format!("Granted the <@&{}> role.", role.get())
            }
            GrantOutcome::AlreadyHeld { role } => {
                format!("Already holds the <@&{}> role, nothing to do.", role.get())
            }
            GrantOutcome::NoMapping { cap } => format!(
                "No role is wired to the **{}** capability in this server ({}). \
                 Set {}=<{}>:<role_id> to enable this grant.",
                cap.label(),
                cap.tag(),
                RoleCapMap::ENV_VAR,
                cap.tag()
            ),
            GrantOutcome::MissingManageRoles { role, detail } => format!(
                "Could not grant <@&{}>: the bot needs the **Manage Roles** permission, and its \
                 role must sit ABOVE the granted role. ({detail})",
                role.get()
            ),
            GrantOutcome::Failed { detail } => format!("Grant failed: {detail}"),
        }
    }
}

/// Classify a serenity error from an `add_role`/`remove_role` call. A missing
/// **Manage Roles** permission (Discord code 50013) or missing access (50001) is the
/// common, actionable case; everything else is opaque. We match on the rendered
/// string rather than serenity's error enum so this stays robust across patch
/// versions — the classification only drives the *message*, never a security choice.
fn classify_role_error(role: RoleId, detail: &str) -> GrantOutcome {
    let low = detail.to_lowercase();
    if low.contains("50013")
        || low.contains("50001")
        || low.contains("missing permissions")
        || low.contains("missing access")
    {
        GrantOutcome::MissingManageRoles {
            role,
            detail: detail.to_string(),
        }
    } else {
        GrantOutcome::Failed {
            detail: detail.to_string(),
        }
    }
}

/// Grant the role mapped to `achievement`'s cap to a guild member — the proof→role
/// flow. Idempotent (a member who already holds the role is
/// [`GrantOutcome::AlreadyHeld`]) and fail-graceful (a missing **Manage Roles**
/// permission is [`GrantOutcome::MissingManageRoles`], never a panic).
///
/// Fetching the member first both gives the current role set for the idempotency
/// check and is the same `GuildId::member` round-trip `add_role` needs.
///
/// This is the honest half of the boundary: the role it assigns is a *badge* for an
/// already-verified fact. The verification (the board replay, the credential check)
/// must have happened before this is called — this function does not itself prove
/// anything, it only reflects a proof into a convenient, revocable Discord role.
pub async fn grant_cap_role(
    http: &Http,
    map: &RoleCapMap,
    guild_id: GuildId,
    user_id: UserId,
    achievement: Achievement,
) -> GrantOutcome {
    let cap = achievement.granted_cap();
    let Some(role) = map.role_for(cap) else {
        return GrantOutcome::NoMapping { cap };
    };

    let member = match guild_id.member(http, user_id).await {
        Ok(m) => m,
        Err(e) => return classify_role_error(role, &e.to_string()),
    };

    match plan_grant(&member.roles, role) {
        GrantPlan::AlreadyHeld => GrantOutcome::AlreadyHeld { role },
        GrantPlan::Grant => match member.add_role(http, role).await {
            Ok(()) => GrantOutcome::Granted { role },
            Err(e) => classify_role_error(role, &e.to_string()),
        },
    }
}

/// The counterpart of [`grant_cap_role`]: hand a mapped role back (a role granted for
/// the duration of a run that outlives its run is a lingering grant — the same reason
/// `discord_caps::DiscordCapability::RemoveRole` exists). Idempotent: a member who
/// does not hold the role is [`GrantOutcome::AlreadyHeld`] read as "already absent".
pub async fn revoke_cap_role(
    http: &Http,
    map: &RoleCapMap,
    guild_id: GuildId,
    user_id: UserId,
    cap: DreggCap,
) -> GrantOutcome {
    let Some(role) = map.role_for(cap) else {
        return GrantOutcome::NoMapping { cap };
    };
    let member = match guild_id.member(http, user_id).await {
        Ok(m) => m,
        Err(e) => return classify_role_error(role, &e.to_string()),
    };
    if !member.roles.contains(&role) {
        // Symmetric no-op: nothing to remove.
        return GrantOutcome::AlreadyHeld { role };
    }
    match member.remove_role(http, role).await {
        Ok(()) => GrantOutcome::Granted { role },
        Err(e) => classify_role_error(role, &e.to_string()),
    }
}

/// Whether a grant outcome is worth telling the member about at an automatic seam.
///
/// The automatic grant rides along on someone ELSE's success embed, so it must not
/// turn a clean "handoff redeemed" into noise about server configuration the member
/// cannot fix. [`GrantOutcome::NoMapping`] — the guild simply has not wired
/// [`RoleCapMap::ENV_VAR`] — is therefore silent: the feature is *inert*, not broken.
/// Everything else IS said: a grant, an idempotent no-op, and above all a missing
/// **Manage Roles** permission, which an admin reading the channel can actually fix.
pub fn worth_surfacing(outcome: &GrantOutcome) -> bool {
    !matches!(outcome, GrantOutcome::NoMapping { .. })
}

/// Fire the proof→role grant at a verified seam and render it as an embed FIELD.
///
/// The one call a verified seam makes. `None` means "say nothing": the interaction
/// carried no guild (a DM — there is no role to grant), or the guild has wired no role
/// for this cap. `Some((title, body))` is a field to hang on the embed the seam was
/// already sending, so the badge is legible in the same breath as the verification that
/// earned it, and a missing **Manage Roles** permission surfaces as an actionable line
/// rather than a silent failure. Never panics; every Discord error is classified into a
/// [`GrantOutcome`] first.
///
/// The caller is responsible for the honest part: call this ONLY after the real
/// verification has already passed. This function grants a badge for a proof; it does
/// not check one.
pub async fn grant_and_describe(
    http: &Http,
    guild_id: Option<GuildId>,
    user_id: UserId,
    achievement: Achievement,
) -> Option<(&'static str, String)> {
    let guild_id = guild_id?;
    let map = RoleCapMap::from_env();
    let outcome = grant_cap_role(http, &map, guild_id, user_id, achievement).await;
    if !worth_surfacing(&outcome) {
        return None;
    }
    tracing::info!(
        user_id = user_id.get(),
        guild_id = guild_id.get(),
        cap = achievement.granted_cap().tag(),
        outcome = ?outcome,
        "proof→role grant fired at a verified seam"
    );
    Some(("Capability Role", outcome.message()))
}

/// Read the invoking member's caps straight off a serenity [`Member`] — the ergonomic
/// entry a slash handler uses (`map.member_caps(command.member.as_deref())`).
impl RoleCapMap {
    /// The caps the invoking member holds, or the empty set if the interaction carried
    /// no member (a DM, or an uncached member).
    pub fn member_caps(&self, member: Option<&Member>) -> BTreeSet<DreggCap> {
        member
            .map(|m| self.caps_for_roles(&m.roles))
            .unwrap_or_default()
    }
}

/// The honest-boundary blurb, surfaced verbatim in `/identity roles show` so a user reads it in
/// the product, not just the source.
pub fn attestation_boundary() -> &'static str {
    "A Discord role here is an **attestation by this server**: convenient, revocable, \
     and exactly as trustworthy as who hands roles out. It can GATE a surface (a cheap \
     first filter and a nice UX), but it is NOT a dregg proof. Where authority must be \
     cryptographic, the referee is the real cap system: the executor (a turn is refused \
     or it lands) and your macaroon tokens (`/cipherclerk authorize`, \
     `AgentCipherclerk::verify_token`), never the role."
}

// ─── The `roles` surface — folded under `/identity` ──────────────────────────
//
// One surface that shows both directions honestly:
//   `/identity roles show`    — the caps you hold via your Discord roles, plus the
//                               boundary, verbatim.
//   `/identity roles unlock`  — the DEMO GATE: a cap-gated offering that refuses
//                               legibly without `DreggCap::VerifiedHolder`, and
//                               reveals it with.
//   `/identity roles grant`   — admin-only manual trigger of proof→role: assign an
//                               achievement's role to a member, for the achievements
//                               whose automatic seam is not wired yet.
//
// NOT a top-level command: [`register`] is folded into `/identity` — the granting-authority
// command — as a subcommand GROUP by `menus::command_for`, dispatched by
// `menus::handle_identity` through the same `as_command` re-nesting every other fold uses.
// The map is read from the environment on demand (`RoleCapMap::from_env`); a production
// wiring would cache it on `BotState`.
//
// ⚑ `/identity` is a `Door::Lab` row on `menus::SLASH_SURFACE`, so this whole surface is
// un-advertised: it is registered only inside `DREGG_LAB_GUILD_ID`. Nothing about it is
// deleted — the handlers, the role→cap map and the proof→role grant seam are untouched — but
// `/identity roles …` is not typeable on the global surface.
//
// The automatic (non-admin) grant seam is live for [`Achievement::IdentityVerified`],
// fired from the canonical `validate_handoff` acceptance in `commands::handoff`.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

/// Register `/roles` and its subcommands.
pub fn register() -> CreateCommand {
    CreateCommand::new("roles")
        .description(
            "Discord roles as dregg capabilities · what they gate, and how proofs grant them",
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "show",
            "Show the caps your roles grant you, and the honest boundary",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "unlock",
            "A demo offering gated on the Verified Holder capability",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "grant",
                "(admin) Grant an achievement's role to a member · the proof→role demo",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::User, "user", "Who earned it")
                    .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "achievement",
                    "The verified achievement whose role to grant",
                )
                .required(true)
                .add_string_choice("Verified Descent win", "descent-win")
                .add_string_choice("Identity verified", "identity-verified"),
            ),
        )
}

/// Handle `/roles`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first().map(|o| o.name.clone()) else {
        return;
    };
    match sub.as_str() {
        "show" => handle_show(ctx, command).await,
        "unlock" => handle_unlock(ctx, command).await,
        "grant" => handle_grant(ctx, command, state).await,
        _ => {}
    }
}

/// `/identity roles show` — the caps the invoking member holds, plus the honest boundary.
async fn handle_show(ctx: &Context, command: &CommandInteraction) {
    defer_ephemeral(ctx, command).await;
    let map = RoleCapMap::from_env();
    let caps = map.member_caps(command.member.as_deref());

    let held = if caps.is_empty() {
        "_none · no cap-bearing roles_".to_string()
    } else {
        caps.iter()
            .map(|c| {
                let role = map
                    .role_for(*c)
                    .map(|r| format!(" (<@&{}>)", r.get()))
                    .unwrap_or_default();
                format!("- **{}**{role}", c.label())
            })
            .collect::<Vec<_>>()
            .join("\n")
    };

    let wired = if map.is_empty() {
        format!(
            "No role↔cap bindings configured. Set `{}` to wire them (e.g. \
             `verified_holder:<role_id>,descent_champion:<role_id>`).",
            RoleCapMap::ENV_VAR
        )
    } else {
        format!("{} binding(s) wired.", map.len())
    };

    let embed = embeds::dregg_embed("Your Capabilities (from Discord roles)").description(format!(
        "**You hold:**\n{held}\n\n{wired}\n\n{}",
        attestation_boundary()
    ));
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// `/identity roles unlock` — the DEMO GATE. A cap-gated offering: refuse legibly without the
/// Verified Holder cap, reveal it with. This is the *convenience* gate; a real
/// cryptographic effect behind this button would re-check on the executor / a macaroon
/// (the role only decides whether to SHOW it).
async fn handle_unlock(ctx: &Context, command: &CommandInteraction) {
    defer_ephemeral(ctx, command).await;
    let map = RoleCapMap::from_env();
    let roles: &[RoleId] = command
        .member
        .as_deref()
        .map(|m| m.roles.as_slice())
        .unwrap_or(&[]);

    let embed = match map.gate(roles, DreggCap::VerifiedHolder) {
        Ok(()) => embeds::success_embed("Unlocked · Verified Holders' Table")
            .description(
                "Your **Verified Holder** role opened this surface. (A real cryptographic \
                 action here would still re-verify on the executor / your macaroon; the role \
                 only decided whether to show you the door.)",
            )
            .field("Offering", "the verified-only lounge", false),
        Err(denied) => embeds::warning_embed("Locked", &denied.message()),
    };
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// `/identity roles grant` — admin-only demo of the proof→role flow.
async fn handle_grant(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    defer_ephemeral(ctx, command).await;

    // Guild-only.
    let Some(guild_id) = command.guild_id else {
        let embed = embeds::error_embed("Guild Required", "Run this in a server.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    // Admin-only: this manual trigger stands in for the automatic verified seam, so
    // it is gated to server administrators (the same posture as `/federation setup`).
    let is_admin = command
        .member
        .as_deref()
        .and_then(|m| m.permissions)
        .map(|p| p.administrator())
        .unwrap_or(false);
    if !is_admin {
        let embed = embeds::warning_embed(
            "Admins Only",
            "This is the manual demo of the proof→role grant. In production the grant fires \
             automatically from the verified achievement (a re-verified Descent win, a \
             `/credential verify` success), no admin press needed.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let target = sub_user_opt(command, "user");
    let achievement = match sub_string_opt(command, "achievement").as_deref() {
        Some("descent-win") => Achievement::VerifiedDescentWin,
        Some("identity-verified") => Achievement::IdentityVerified,
        _ => {
            let embed =
                embeds::error_embed("Invalid Achievement", "Pick one of the offered choices.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let Some(user_id) = target else {
        let embed = embeds::error_embed("Invalid Arguments", "Specify a target user.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    let map = RoleCapMap::from_env();
    let outcome = grant_cap_role(&ctx.http, &map, guild_id, user_id, achievement).await;

    let embed = match &outcome {
        GrantOutcome::Granted { .. } | GrantOutcome::AlreadyHeld { .. } => {
            embeds::success_embed("Role Grant")
        }
        _ => embeds::warning_embed("Role Grant", &outcome.message()),
    }
    .description(format!(
        "**Achievement:** {} → **{}** cap\n{}",
        match achievement {
            Achievement::VerifiedDescentWin => "verified Descent win",
            Achievement::IdentityVerified => "identity verified",
        },
        achievement.granted_cap().label(),
        outcome.message()
    ));
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

/// Read a String option nested under the invoked subcommand (`command.data.options[0]`).
fn sub_string_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options.first()?.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

/// Read a User option nested under the invoked subcommand.
fn sub_user_opt(command: &CommandInteraction, name: &str) -> Option<UserId> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options.first()?.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(*uid),
            _ => None,
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_map() -> RoleCapMap {
        RoleCapMap::from_pairs([
            (DreggCap::VerifiedHolder, 100),
            (DreggCap::DescentChampion, 200),
            (DreggCap::CouncilVoter, 300),
        ])
    }

    // ─── mapping: roles → caps ────────────────────────────────────────────────

    #[test]
    fn member_caps_maps_roles_to_caps() {
        let map = demo_map();

        // One mapped role → its one cap.
        assert_eq!(
            map.caps_for_roles(&[RoleId::new(100)]),
            BTreeSet::from([DreggCap::VerifiedHolder])
        );

        // Several roles (one of them unmapped) → exactly the mapped caps.
        assert_eq!(
            map.caps_for_roles(&[RoleId::new(100), RoleId::new(200), RoleId::new(999)]),
            BTreeSet::from([DreggCap::VerifiedHolder, DreggCap::DescentChampion])
        );

        // No mapped roles → no caps (fail-closed, not fail-open).
        assert!(map.caps_for_roles(&[RoleId::new(999)]).is_empty());
        assert!(map.caps_for_roles(&[]).is_empty());
    }

    #[test]
    fn the_map_is_a_function_both_ways() {
        let map = demo_map();
        assert_eq!(
            map.cap_for(RoleId::new(100)),
            Some(DreggCap::VerifiedHolder)
        );
        assert_eq!(
            map.role_for(DreggCap::VerifiedHolder),
            Some(RoleId::new(100))
        );
        assert_eq!(
            map.role_for(DreggCap::Patron),
            None,
            "unwired cap has no role"
        );
    }

    #[test]
    fn rebinding_a_role_or_cap_leaves_no_stale_index() {
        let mut map = RoleCapMap::default();
        map.insert(DreggCap::VerifiedHolder, 100);
        // Re-point the SAME cap at a new role: the old role must stop resolving.
        map.insert(DreggCap::VerifiedHolder, 101);
        assert_eq!(
            map.role_for(DreggCap::VerifiedHolder),
            Some(RoleId::new(101))
        );
        assert_eq!(map.cap_for(RoleId::new(100)), None);
        // Re-point the SAME role at a new cap: the old cap must stop resolving.
        map.insert(DreggCap::DescentChampion, 101);
        assert_eq!(
            map.cap_for(RoleId::new(101)),
            Some(DreggCap::DescentChampion)
        );
        assert_eq!(map.role_for(DreggCap::VerifiedHolder), None);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn env_parse_round_trips_and_skips_garbage() {
        let map = RoleCapMap::parse(
            "verified_holder:100, descent_champion:200 , bogus_tag:300, council_voter:notanumber, patron:0",
        );
        assert_eq!(
            map.role_for(DreggCap::VerifiedHolder),
            Some(RoleId::new(100))
        );
        assert_eq!(
            map.role_for(DreggCap::DescentChampion),
            Some(RoleId::new(200))
        );
        // Unknown tag, non-numeric id, and zero id are all dropped.
        assert_eq!(map.role_for(DreggCap::CouncilVoter), None);
        assert_eq!(map.role_for(DreggCap::Patron), None);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn cap_tags_round_trip() {
        for &cap in DreggCap::ALL {
            assert_eq!(DreggCap::from_tag(cap.tag()), Some(cap));
        }
        assert_eq!(DreggCap::from_tag("nope"), None);
    }

    // ─── the gate refuses without the cap ─────────────────────────────────────

    #[test]
    fn the_gate_refuses_without_the_cap_and_names_the_role() {
        let map = demo_map();

        // Holds it → open.
        assert!(
            map.gate(&[RoleId::new(100)], DreggCap::VerifiedHolder)
                .is_ok()
        );

        // Lacks it → refused, and the refusal names the role that would unlock it.
        let denied = map
            .gate(&[RoleId::new(200)], DreggCap::VerifiedHolder)
            .expect_err("a member without the verified role must be refused");
        assert_eq!(denied.needed, DreggCap::VerifiedHolder);
        assert_eq!(denied.granting_role, Some(RoleId::new(100)));
        assert!(denied.message().contains("100"), "names the unlocking role");

        // Empty role set → refused.
        assert!(map.gate(&[], DreggCap::VerifiedHolder).is_err());
    }

    #[test]
    fn gating_an_unwired_cap_refuses_and_says_so() {
        let map = demo_map();
        let denied = map
            .gate(&[RoleId::new(100)], DreggCap::Patron)
            .expect_err("no role is wired to Patron");
        assert_eq!(denied.granting_role, None);
        assert!(denied.message().to_lowercase().contains("no role"));
    }

    #[test]
    fn member_caps_handles_a_missing_member() {
        let map = demo_map();
        assert!(map.member_caps(None).is_empty(), "a DM carries no roles");
    }

    // ─── the grant is idempotent ──────────────────────────────────────────────

    #[test]
    fn the_grant_is_idempotent() {
        let role = RoleId::new(200);

        // Not held yet → grant.
        assert_eq!(plan_grant(&[RoleId::new(100)], role), GrantPlan::Grant);
        assert_eq!(plan_grant(&[], role), GrantPlan::Grant);

        // Already held → no-op (this is the idempotency).
        assert_eq!(
            plan_grant(&[RoleId::new(100), RoleId::new(200)], role),
            GrantPlan::AlreadyHeld
        );
        assert_eq!(plan_grant(&[role], role), GrantPlan::AlreadyHeld);
    }

    #[test]
    fn achievements_map_to_their_grant_caps() {
        assert_eq!(
            Achievement::VerifiedDescentWin.granted_cap(),
            DreggCap::DescentChampion
        );
        assert_eq!(
            Achievement::IdentityVerified.granted_cap(),
            DreggCap::VerifiedHolder
        );
    }

    #[test]
    fn grant_with_no_mapped_role_is_a_clean_no_mapping() {
        // A map with no DescentChampion binding: the outcome names the fix, not a crash.
        let map = RoleCapMap::from_pairs([(DreggCap::VerifiedHolder, 100)]);
        assert_eq!(map.role_for(DreggCap::DescentChampion), None);
        let outcome = GrantOutcome::NoMapping {
            cap: Achievement::VerifiedDescentWin.granted_cap(),
        };
        assert!(outcome.message().contains(RoleCapMap::ENV_VAR));
    }

    #[test]
    fn the_automatic_seam_is_quiet_when_inert_and_loud_when_fixable() {
        let role = RoleId::new(200);
        // An unconfigured guild is INERT, not broken — the automatic grant rides on
        // someone else's success embed and must not nag about config nobody asked for.
        assert!(!worth_surfacing(&GrantOutcome::NoMapping {
            cap: DreggCap::VerifiedHolder
        }));
        // Everything else is said. A missing Manage Roles permission especially: it is
        // the one outcome an admin reading the channel can actually act on.
        assert!(worth_surfacing(&GrantOutcome::MissingManageRoles {
            role,
            detail: "50013: Missing Permissions".into(),
        }));
        assert!(worth_surfacing(&GrantOutcome::Granted { role }));
        assert!(worth_surfacing(&GrantOutcome::AlreadyHeld { role }));
        assert!(worth_surfacing(&GrantOutcome::Failed {
            detail: "boom".into()
        }));
    }

    #[test]
    fn missing_manage_roles_is_classified_from_the_error_string() {
        let role = RoleId::new(200);
        // The rendered Discord 50013 must be surfaced as the actionable permission case,
        // so the grant tells the admin the real fix (grant Manage Roles + raise the bot's
        // role) rather than an opaque failure.
        assert!(matches!(
            classify_role_error(role, "50013: Missing Permissions"),
            GrantOutcome::MissingManageRoles { .. }
        ));
        assert!(matches!(
            classify_role_error(role, "Some 50001 missing access thing"),
            GrantOutcome::MissingManageRoles { .. }
        ));
        // Anything else stays an opaque (but non-panicking) failure.
        assert!(matches!(
            classify_role_error(role, "500: Internal Server Error"),
            GrantOutcome::Failed { .. }
        ));
    }
}
