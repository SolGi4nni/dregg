//! # The COMMAND REGISTRY — one source of truth for the dispatcher, `/help`, and Telegram's
//! `/` menu.
//!
//! A hand-written help string rots the moment someone adds a command, and it had already rotted:
//! `/menu`, `/webapp`, `/record` and `/start` were dispatched by
//! [`crate::runtime::route_text_decided`] and appeared in NO help text, while the help advertised
//! `/operation` (a document *caption*, not a chat command) as if it were one.
//!
//! So the enumeration moved here and became load-bearing in three directions at once:
//!
//! 1. **The dispatcher resolves through [`lookup`]** — a word that is not in [`COMMANDS`] cannot
//!    reach a handler at all, so a new command MUST be registered to work;
//! 2. **`/help` is generated** from the same table ([`help_text`]), and `/help <cmd>` renders one
//!    entry's [`BotCommand::detail`] ([`command_help`]);
//! 3. **Telegram's `/` menu is registered** from the same table
//!    ([`bot_father_commands`] → `setMyCommands` at boot), so the client-side command list cannot
//!    disagree with the bot either. Before this, `getMyCommands` returned `[]` — the client showed
//!    NO command menu at all, which is why the surface had to be guessed.
//!
//! `tests/help_is_exhaustive.rs` closes the loop: every registered command must appear in
//! `/help`, must carry a non-empty summary and detail, must resolve through [`lookup`] under its
//! own name and every alias, and must actually dispatch (never `Unknown`). Adding a command
//! without help text fails the build.

/// One registered chat command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BotCommand {
    /// The canonical command word, with the leading slash (`"/open"`). This is what the
    /// dispatcher matches on after [`lookup`] resolves aliases.
    pub name: &'static str,
    /// Alternative spellings that resolve to [`name`](Self::name).
    pub aliases: &'static [&'static str],
    /// The argument grammar as a human reads it (`"<key>"`), or `""` for a bare command.
    pub args: &'static str,
    /// The one-line description `/help` and Telegram's `/` menu show.
    pub summary: &'static str,
    /// The longer account `/help <cmd>` renders.
    pub detail: &'static str,
    /// Whether this command is offered in Telegram's client-side `/` menu (`setMyCommands`).
    /// Aliases and rarely-wanted commands stay out of the menu but remain fully dispatchable and
    /// fully documented in `/help`.
    pub in_menu: bool,
}

impl BotCommand {
    /// `"/open <key>"` — the command as its usage line reads.
    pub fn usage(&self) -> String {
        if self.args.is_empty() {
            self.name.to_string()
        } else {
            format!("{} {}", self.name, self.args)
        }
    }
}

/// Telegram's cap on a `setMyCommands` description.
const MENU_DESCRIPTION_MAX: usize = 256;

/// **Every command this bot dispatches.** The dispatcher, `/help`, and Telegram's `/` menu all
/// read this one table.
pub const COMMANDS: &[BotCommand] = &[
    BotCommand {
        name: "/help",
        aliases: &["/start"],
        args: "[command]",
        summary: "this list; /help <command> explains one",
        detail: "With no argument, the complete command surface. With one (`/help open`, or \
                 `/help /open`), that command's own account. Generated from the dispatcher's \
                 registry, so it cannot drift from what the bot actually does.",
        in_menu: true,
    },
    BotCommand {
        name: "/offerings",
        aliases: &["/menu"],
        args: "",
        summary: "the game shelf: a button per game",
        detail: "Posts the catalog as an inline keyboard; a press opens that offering in this \
                 chat. Always posts a FRESH message at the bottom of the chat, so asking for the \
                 menu always produces something you can see. In a group, a game that has to keep \
                 part of itself hidden from the other player is shown DIMMED (🔒) with the reason \
                 and the DM route, because a group's board is one message every member reads; the \
                 shelf says so before you press, not after.",
        in_menu: true,
    },
    BotCommand {
        name: "/open",
        aliases: &[],
        args: "<key>",
        summary: "open a game here (e.g. /open descent)",
        detail: "Opens (or re-presents) `<key>` in this chat as its own message. Keys come from \
                 /offerings. An offering that hides per-player state is refused in a group or \
                 forum topic (a group's surface is ONE message every member reads) and redirects \
                 you to a DM; /offerings dims exactly those rows and names them, so you do not \
                 have to guess which. Re-opening something already open reposts its live surface \
                 at the bottom of the chat rather than editing a message you have scrolled past.",
        in_menu: true,
    },
    BotCommand {
        name: "/status",
        aliases: &["/record"],
        args: "",
        summary: "this chat's game record, audience, and receipts",
        detail: "Inspects the active game through the shared game-session spine: the audience \
                 boundary, the replay verdict, landed steps, advertised proof operations and \
                 artifacts. A group gets the viewer-blind projection; a DM may see the \
                 host-rich one.",
        in_menu: true,
    },
    BotCommand {
        name: "/verify",
        aliases: &[],
        args: "",
        summary: "re-verify this chat's committed chain by replay",
        detail: "Replays the active offering's committed move-log and reports the verifier's own \
                 verdict. Read-only: the presented surface is untouched.",
        in_menu: true,
    },
    BotCommand {
        name: "/act",
        aliases: &[],
        args: "<turn> <arg>",
        summary: "fire a value-taking turn (e.g. /act bid 500)",
        detail: "Mints the same press a button would, for turns that take a value the keyboard \
                 cannot enumerate. `<arg>` must be an integer. The executor stays the sole \
                 referee: an ineligible move lands a real refusal, never a silent accept.",
        in_menu: false,
    },
    BotCommand {
        name: "/cancel",
        aliases: &["/reset", "/stop"],
        args: "",
        summary: "escape hatch: unstick this chat, keep every receipt",
        detail: "Always works, from any state, session or no session. It disarms a pending \
                 free-text slot (so your next message is ordinary chatter again), drops this \
                 chat's surface bookkeeping and stale keyboards, and reposts the offerings menu. \
                 It NEVER discards a committed move-log: your sessions and their receipts survive \
                 untouched, and /open <key> brings any of them back. Use /close <key> for the \
                 destructive form.",
        in_menu: true,
    },
    BotCommand {
        name: "/close",
        aliases: &[],
        args: "<key>",
        summary: "END a session and DISCARD its local move-log",
        detail: "Destructive, and deliberately requires the key: it closes `<key>`'s session in \
                 this chat and forgets its durable move-log, so the next /open starts a genuinely \
                 fresh session. Use this when a session can no longer advance (every affordance \
                 refuses). /cancel is the non-destructive escape.",
        in_menu: false,
    },
    BotCommand {
        name: "/play",
        aliases: &["/webapp"],
        args: "",
        summary: "Mini App launch buttons, per offering (DMs only)",
        detail: "One `web_app` button per offering, opening the richer web surface at this \
                 chat's session. Telegram honours `web_app` inline buttons in private chats \
                 only, so this is a DM command; the inline keyboard plays everything without it.",
        in_menu: true,
    },
    BotCommand {
        name: "/link",
        aliases: &[],
        args: "",
        summary: "bind this Telegram to your dregg root key (DMs only)",
        detail: "Opens the identity-link ceremony in the Mini App, where you sign a link claim \
                 with your root key: one you, across platforms. Private chats only, for the \
                 same `web_app` reason as /play.",
        in_menu: true,
    },
];

/// A pseudo-command documented in `/help` but dispatched from a DOCUMENT CAPTION, never as a chat
/// message. Kept out of [`COMMANDS`] so the registry stays exactly "what the text dispatcher
/// routes", and named here so `/help` can still teach it.
pub const OPERATION_CAPTION_NOTE: &str = "📎 /operation <name> · not a chat command: it is the \
    exact CAPTION you attach to a canonical receipt document. Normally DM-only; the \
    proof-operation guide names any shared-session exception.";

/// The closing note every `/help` carries.
pub const HELP_FOOTER: &str = "A group chat plays as a collective; a DM plays solo. Sessions \
    survive bot restarts. Stuck? /cancel always works.";

/// The opening note every `/help` carries.
pub const HELP_HEADER: &str = "Dregg games use one addressed session-and-receipt protocol while \
    keeping different rulebooks.";

/// The flagship pointers `/help` leads with — concrete openings, not an abstract catalog.
///
/// ⚑ **THESE MUST BE ON THE SHIP LIST.** `/help` is a public shelf in prose: a line here
/// advertises an offering just as loudly as a menu button, and no host-level filter can reach it.
/// `the_help_flagships_are_all_shipped` below is the gate. To add a line, ship the offering first
/// (`dreggnet_catalog::SHIPPED_KEYS`). It previously advertised `dungeon`, `bazaar` and
/// `private-raid` alongside the Descent, which is precisely the leak the ship list exists to stop.
const FLAGSHIP_LINES: &[(&str, &str)] = &[
    (
        "descent",
        "⚔️ /open descent · a dungeon crawl: one dungeon a day, one life, no retries",
    ),
    (
        "automatafl",
        "♟ /open automatafl · a two-player board game where both moves are revealed at once",
    ),
    (
        "tug",
        "🪢 /open tug · a two-player game of hidden influence over seven guilds",
    ),
];

/// Strip a `@BotName` suffix and normalise a typed word to a lookup key. In a group, Telegram
/// delivers commands as `/open@MyBot dungeon`.
fn normalise(word: &str) -> String {
    let word = word.trim();
    let word = word.split('@').next().unwrap_or(word);
    let mut out = String::with_capacity(word.len() + 1);
    if !word.starts_with('/') {
        out.push('/');
    }
    out.push_str(word);
    out.to_ascii_lowercase()
}

/// **Resolve a typed word to its registered command**, through aliases and a `@BotName` suffix.
/// `None` for anything unregistered — which is exactly why the dispatcher cannot route a command
/// that is not in [`COMMANDS`].
pub fn lookup(word: &str) -> Option<&'static BotCommand> {
    let want = normalise(word);
    COMMANDS.iter().find(|c| {
        c.name.eq_ignore_ascii_case(&want)
            || c.aliases.iter().any(|a| a.eq_ignore_ascii_case(&want))
    })
}

/// **The generated `/help` text** — the whole command surface, from the registry the dispatcher
/// resolves through. Every entry in [`COMMANDS`] appears here by construction.
pub fn help_text() -> String {
    let mut out = String::new();
    out.push_str(HELP_HEADER);
    out.push('\n');
    for (_key, line) in FLAGSHIP_LINES {
        out.push_str(line);
        out.push('\n');
    }
    // ⚑ No "…and there is also a Lab full of markets, councils and RPG systems" line here.
    // /help is a public shelf in prose; naming the unshipped set in passing re-advertises
    // exactly what `dreggnet_catalog::SHIPPED_KEYS` took off every other surface.
    out.push('\n');
    out.push_str("Commands:\n");
    for command in COMMANDS {
        out.push_str(&format!("{} · {}\n", command.usage(), command.summary));
        if !command.aliases.is_empty() {
            out.push_str(&format!("    (also {})\n", command.aliases.join(", ")));
        }
    }
    out.push('\n');
    out.push_str(OPERATION_CAPTION_NOTE);
    out.push_str("\n\n");
    out.push_str(HELP_FOOTER);
    out
}

/// **Per-command help** (`/help open`). `None` for an unregistered word; the caller answers with
/// the full [`help_text`] plus an honest "no such command".
pub fn command_help(word: &str) -> Option<String> {
    let command = lookup(word)?;
    let mut out = format!("{}\n{}\n", command.usage(), command.summary);
    if !command.aliases.is_empty() {
        out.push_str(&format!("Also: {}\n", command.aliases.join(", ")));
    }
    out.push('\n');
    out.push_str(command.detail);
    Some(out)
}

/// **The `setMyCommands` payload** — `(command-without-slash, description)` for every
/// [`BotCommand::in_menu`] entry, so Telegram's client-side `/` menu is registered from the same
/// table the dispatcher uses. Descriptions are clamped to Telegram's 256-character ceiling.
pub fn bot_father_commands() -> Vec<(String, String)> {
    COMMANDS
        .iter()
        .filter(|c| c.in_menu)
        .map(|c| {
            let name = c.name.trim_start_matches('/').to_string();
            let description: String = c.summary.chars().take(MENU_DESCRIPTION_MAX).collect();
            (name, description)
        })
        .collect()
}

#[cfg(test)]
mod ship_list_tests {
    use super::*;

    /// ⚑ **`/help` cannot advertise something we do not ship.** The Telegram help text is a shelf
    /// written in prose — no `OfferingHost` filter reaches it — so this is the gate that keeps it
    /// in step with `dreggnet_catalog::SHIPPED_KEYS`. Both directions: a flagship line must name a
    /// shipped offering, and every shipped offering must have a line, so paring the ship list can
    /// never leave a stale pointer and adding to it can never leave a silent omission.
    #[test]
    fn the_help_flagships_are_exactly_the_ship_list() {
        let listed: Vec<&str> = FLAGSHIP_LINES.iter().map(|(key, _)| *key).collect();
        for key in &listed {
            assert!(
                dreggnet_catalog::is_shipped(key),
                "/help advertises `{key}`, which is not on dreggnet_catalog::SHIPPED_KEYS"
            );
        }
        for key in dreggnet_catalog::SHIPPED_KEYS {
            assert!(
                listed.contains(&key),
                "`{key}` is shipped but /help never points at it"
            );
        }
        let help = help_text();
        for (key, line) in FLAGSHIP_LINES {
            assert!(
                help.contains(line),
                "the `{key}` flagship line reaches /help"
            );
        }
    }
}
