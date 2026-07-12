//! Semi-private per-user DreggNet Cloud channels.
//!
//! A user claims their own Discord channel ([`commands::channel`]). The channel
//! is visibility-gated to the user + the admin (ember): `@everyone` is denied
//! `VIEW_CHANNEL`, while the owner and the admin are allowed to view + post. The
//! channel is recorded in the bot DB bound to the user's dregg cell, and becomes
//! the surface from which the user drives their own confined Hermes
//! ([`crate::hermes_channel`]).
//!
//! ## The "semi-private" posture (best-effort; admin sees all)
//!
//! This is Discord-permission privacy, not cryptographic privacy: it keeps the
//! channel out of `@everyone`'s view, but the guild owner, anyone with
//! `MANAGE_CHANNELS`/`ADMINISTRATOR`, and — by design — the pinned admin can read
//! it. The admin's read access is explicit (an allow overwrite) AND total (the
//! admin webportal monitors every channel's DB-recorded activity and internal
//! state). "Semi-private" names exactly this: private from peers, transparent to
//! the operator.
//!
//! The permission *plan* ([`plan_private_overwrites`]) is a pure function so the
//! gating logic is unit-tested offline; the live Discord `create_channel` call is
//! the only part that needs a token (gated in [`commands::channel`]).

use serenity::all::{PermissionOverwrite, PermissionOverwriteType, Permissions, RoleId, UserId};

/// The permission set a participant (owner / admin) needs to use the channel.
pub(crate) fn participant_allow() -> Permissions {
    Permissions::VIEW_CHANNEL | Permissions::SEND_MESSAGES | Permissions::READ_MESSAGE_HISTORY
}

/// The permission set a participant retains once a surface is ARCHIVED: they can
/// still read the record of the run, but they can no longer write to it.
pub(crate) fn reader_allow() -> Permissions {
    Permissions::VIEW_CHANNEL | Permissions::READ_MESSAGE_HISTORY
}

/// Build the permission overwrites for a semi-private per-user channel.
///
/// * `@everyone` (the role whose id equals the guild id) is DENIED `VIEW_CHANNEL`
///   — the channel does not appear for peers.
/// * the `owner` is ALLOWED to view, post, and read history — it is their surface.
/// * the `admin` (if pinned) is ALLOWED the same — the operator sees all.
///
/// Pure: no Discord client needed, so the gating is unit-testable.
pub fn plan_private_overwrites(
    everyone_role: RoleId,
    owner: UserId,
    admin: Option<UserId>,
) -> Vec<PermissionOverwrite> {
    let mut overwrites = vec![
        // Deny the whole guild.
        PermissionOverwrite {
            allow: Permissions::empty(),
            deny: Permissions::VIEW_CHANNEL,
            kind: PermissionOverwriteType::Role(everyone_role),
        },
        // Allow the owner.
        PermissionOverwrite {
            allow: participant_allow(),
            deny: Permissions::empty(),
            kind: PermissionOverwriteType::Member(owner),
        },
    ];

    // Allow the admin — but never emit a duplicate overwrite if the admin IS the
    // owner (e.g. ember claiming their own channel).
    if let Some(admin) = admin {
        if admin != owner {
            overwrites.push(PermissionOverwrite {
                allow: participant_allow(),
                deny: Permissions::empty(),
                kind: PermissionOverwriteType::Member(admin),
            });
        }
    }

    overwrites
}

/// Build the permission overwrites for an ARCHIVED per-session surface — the
/// read-only tombstone a completed run leaves behind.
///
/// * `@everyone` stays DENIED `VIEW_CHANNEL` (an archived private run stays private).
/// * the `owner` and the `admin` keep `VIEW_CHANNEL` + `READ_MESSAGE_HISTORY` — the
///   record of the run remains readable — but `SEND_MESSAGES` is *explicitly DENIED*.
///
/// The deny is explicit rather than merely "not allowed" on purpose: an overwrite
/// that only dropped `SEND_MESSAGES` from the allow-set would still let a
/// role-level grant (or the guild's `@everyone` base permissions) re-open the
/// channel for writing. A member-level DENY is the highest-precedence rule in
/// Discord's permission resolution, so the archive actually closes.
///
/// Pure: no Discord client needed, so teardown is unit-testable.
pub fn plan_archived_overwrites(
    everyone_role: RoleId,
    owner: UserId,
    admin: Option<UserId>,
) -> Vec<PermissionOverwrite> {
    let mut overwrites = vec![
        PermissionOverwrite {
            allow: Permissions::empty(),
            deny: Permissions::VIEW_CHANNEL,
            kind: PermissionOverwriteType::Role(everyone_role),
        },
        PermissionOverwrite {
            allow: reader_allow(),
            deny: Permissions::SEND_MESSAGES,
            kind: PermissionOverwriteType::Member(owner),
        },
    ];

    if let Some(admin) = admin {
        if admin != owner {
            overwrites.push(PermissionOverwrite {
                allow: reader_allow(),
                deny: Permissions::SEND_MESSAGES,
                kind: PermissionOverwriteType::Member(admin),
            });
        }
    }

    overwrites
}

/// The channel name for a user's semi-private channel (Discord lowercases +
/// dash-normalizes channel names; we do it ourselves so the stored name matches).
pub fn channel_name_for(discord_id: u64) -> String {
    format!("dregg-{discord_id}")
}

/// Discord's own normalization for guild text-channel names: lowercase, and every
/// run of non-`[a-z0-9-]` collapsed to a single `-`. We apply it ourselves so the
/// name we *store* is the name Discord actually assigns (otherwise a session's
/// recorded name and its live name drift, and idempotent re-open misses).
///
/// Also enforces Discord's 100-character channel-name limit.
pub fn normalize_channel_name(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut last_dash = false;
    for ch in raw.chars() {
        let c = ch.to_ascii_lowercase();
        if c.is_ascii_alphanumeric() {
            out.push(c);
            last_dash = false;
        } else if !last_dash && !out.is_empty() {
            out.push('-');
            last_dash = true;
        }
    }
    // Never end on the separator, and respect Discord's 100-char cap.
    while out.len() > MAX_CHANNEL_NAME {
        out.pop();
    }
    while out.ends_with('-') {
        out.pop();
    }
    out
}

/// Discord's hard limit on a channel name.
const MAX_CHANNEL_NAME: usize = 100;

/// The channel/thread name for one session of an offering (e.g. `dungeon-a1b2c3`).
pub fn session_surface_name(offering: &str, session_id: &str) -> String {
    normalize_channel_name(&format!("{offering}-{session_id}"))
}

/// The name of the per-offering CATEGORY every session of that offering is filed
/// under. Categories are not name-normalized by Discord the way channels are, but
/// we keep them boring and stable so the category is findable by name.
pub fn category_name_for(offering: &str) -> String {
    format!("dreggnet-{}", normalize_channel_name(offering))
}

/// The name an archived session surface is renamed to. Idempotent: archiving an
/// already-archived name does not stack a second prefix.
pub fn archived_name_for(name: &str) -> String {
    if name.starts_with(ARCHIVE_PREFIX) {
        return normalize_channel_name(name);
    }
    normalize_channel_name(&format!("{ARCHIVE_PREFIX}{name}"))
}

/// The prefix marking a torn-down session surface.
const ARCHIVE_PREFIX: &str = "archived-";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_overwrites_deny_everyone_allow_owner_and_admin() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        let admin = UserId::new(200);

        let ovr = plan_private_overwrites(everyone, owner, Some(admin));
        assert_eq!(ovr.len(), 3, "everyone-deny + owner-allow + admin-allow");

        // @everyone is denied VIEW_CHANNEL and allowed nothing.
        let everyone_ovr = ovr
            .iter()
            .find(|o| matches!(o.kind, PermissionOverwriteType::Role(r) if r == everyone))
            .expect("an everyone overwrite");
        assert!(everyone_ovr.deny.contains(Permissions::VIEW_CHANNEL));
        assert!(everyone_ovr.allow.is_empty());

        // Owner + admin can both view.
        for who in [owner, admin] {
            let m = ovr
                .iter()
                .find(|o| matches!(o.kind, PermissionOverwriteType::Member(u) if u == who))
                .expect("a member overwrite");
            assert!(m.allow.contains(Permissions::VIEW_CHANNEL));
            assert!(m.allow.contains(Permissions::SEND_MESSAGES));
        }
    }

    #[test]
    fn admin_equal_to_owner_is_not_duplicated() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        // ember claims their own channel: admin == owner.
        let ovr = plan_private_overwrites(everyone, owner, Some(owner));
        assert_eq!(ovr.len(), 2, "no duplicate owner/admin overwrite");
    }

    #[test]
    fn no_admin_pinned_still_gates_to_owner() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        let ovr = plan_private_overwrites(everyone, owner, None);
        assert_eq!(ovr.len(), 2);
    }

    #[test]
    fn channel_name_is_stable() {
        assert_eq!(channel_name_for(42), "dregg-42");
    }

    // ─── the per-session surface: archive plan + naming ──────────────────────

    #[test]
    fn archived_overwrites_are_a_read_only_tombstone() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        let admin = UserId::new(200);

        let ovr = plan_archived_overwrites(everyone, owner, Some(admin));
        assert_eq!(ovr.len(), 3);

        // The run stays private after it ends.
        let everyone_ovr = ovr
            .iter()
            .find(|o| matches!(o.kind, PermissionOverwriteType::Role(r) if r == everyone))
            .expect("an everyone overwrite");
        assert!(everyone_ovr.deny.contains(Permissions::VIEW_CHANNEL));

        // Owner + admin can still READ the record, but can no longer WRITE to it —
        // and the write-block is an explicit DENY, not a mere absence of allow.
        for who in [owner, admin] {
            let m = ovr
                .iter()
                .find(|o| matches!(o.kind, PermissionOverwriteType::Member(u) if u == who))
                .expect("a member overwrite");
            assert!(m.allow.contains(Permissions::VIEW_CHANNEL));
            assert!(m.allow.contains(Permissions::READ_MESSAGE_HISTORY));
            assert!(
                !m.allow.contains(Permissions::SEND_MESSAGES),
                "an archived surface must not ALLOW writes"
            );
            assert!(
                m.deny.contains(Permissions::SEND_MESSAGES),
                "the write-block must be an explicit DENY so no role grant re-opens it"
            );
        }
    }

    #[test]
    fn archiving_flips_the_live_plan_from_writable_to_read_only() {
        // The same (everyone, owner, admin) triple, before and after teardown: the
        // ONLY difference that matters is the owner's write bit.
        let (everyone, owner, admin) = (RoleId::new(1), UserId::new(100), Some(UserId::new(200)));
        let live = plan_private_overwrites(everyone, owner, admin);
        let dead = plan_archived_overwrites(everyone, owner, admin);
        assert_eq!(live.len(), dead.len(), "same targets, different rights");

        let owner_live = live
            .iter()
            .find(|o| matches!(o.kind, PermissionOverwriteType::Member(u) if u == owner))
            .unwrap();
        let owner_dead = dead
            .iter()
            .find(|o| matches!(o.kind, PermissionOverwriteType::Member(u) if u == owner))
            .unwrap();
        assert!(owner_live.allow.contains(Permissions::SEND_MESSAGES));
        assert!(owner_dead.deny.contains(Permissions::SEND_MESSAGES));
    }

    #[test]
    fn archived_plan_does_not_duplicate_when_admin_is_owner() {
        let owner = UserId::new(100);
        let ovr = plan_archived_overwrites(RoleId::new(1), owner, Some(owner));
        assert_eq!(ovr.len(), 2);
    }

    #[test]
    fn channel_names_are_discord_normalized() {
        assert_eq!(normalize_channel_name("Dungeon Run #7"), "dungeon-run-7");
        assert_eq!(normalize_channel_name("a  b"), "a-b", "runs collapse");
        assert_eq!(normalize_channel_name("!!!lead"), "lead", "no leading dash");
        assert_eq!(
            normalize_channel_name("trail!!!"),
            "trail",
            "no trailing dash"
        );
        assert_eq!(normalize_channel_name("ALLCAPS"), "allcaps");
        // Discord's 100-char cap, with no dangling separator at the cut.
        let long = normalize_channel_name(&"x".repeat(250));
        assert_eq!(long.len(), 100);
        assert!(!long.ends_with('-'));
    }

    #[test]
    fn session_and_category_names_are_stable_and_legal() {
        assert_eq!(session_surface_name("dungeon", "a1b2c3"), "dungeon-a1b2c3");
        // An offering/session id with junk in it still yields a legal channel name.
        assert_eq!(
            session_surface_name("Hosted Hermes", "Run #4"),
            "hosted-hermes-run-4"
        );
        assert_eq!(category_name_for("dungeon"), "dreggnet-dungeon");
    }

    #[test]
    fn archiving_a_name_is_idempotent() {
        let live = session_surface_name("dungeon", "a1b2c3");
        let dead = archived_name_for(&live);
        assert_eq!(dead, "archived-dungeon-a1b2c3");
        // Tearing down twice must not stack `archived-archived-`.
        assert_eq!(archived_name_for(&dead), dead);
    }
}
