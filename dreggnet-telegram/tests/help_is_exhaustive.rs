//! **`/help` is GENERATED, and the generation is enforced.**
//!
//! The old help was a hand-written `&str` and had already rotted: `/menu`, `/webapp`, `/record`
//! and `/start` were dispatched by `route_text_decided` and documented NOWHERE, while
//! `/operation` was listed as a command though it is a document CAPTION. There was also no
//! escape command at all, and `getMyCommands` on the live bot returned `[]` — Telegram showed no
//! `/` menu, so the surface had to be guessed.
//!
//! These tests are the ratchet. Adding a command without help text fails the build; adding a
//! dispatcher arm that is not in the registry cannot dispatch at all (the dispatcher resolves
//! through `commands::lookup`), and this file proves every registered command really routes.

use dreggnet_telegram::commands::{COMMANDS, bot_father_commands, command_help, help_text, lookup};
use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::runtime::{TextDecision, route_text_decided};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [0x2f; 32];
const CHAT: i64 = 550055;
const ALICE: u64 = 4242;

/// **Every registered command appears in `/help`**, under its own name and with its argument
/// grammar. This is the test that fails when someone adds a command and forgets the help.
#[test]
fn every_registered_command_appears_in_help() {
    let help = help_text();
    assert!(!COMMANDS.is_empty(), "the registry is not empty");
    for command in COMMANDS {
        assert!(
            help.contains(&command.usage()),
            "/help must document `{}` (usage line `{}`) — help is generated from the registry, \
             so a missing line means the generator dropped it:\n{help}",
            command.name,
            command.usage()
        );
        assert!(
            help.contains(command.summary),
            "/help must carry `{}`'s summary",
            command.name
        );
        for alias in command.aliases {
            assert!(
                help.contains(alias),
                "/help must mention `{alias}` as an alias of `{}`",
                command.name
            );
        }
    }
}

/// **`/help` must fit in one Telegram message.** It grows with the registry, and a `sendMessage`
/// over 4096 characters is refused by the Bot API — so an over-long help would answer the one
/// command a lost user types with NOTHING. Per-command help is bounded by the same ceiling.
#[test]
fn help_fits_in_one_telegram_message() {
    let limit = dreggnet_telegram::api::TELEGRAM_TEXT_LIMIT;
    let help = help_text();
    assert!(
        help.chars().count() <= limit,
        "/help is {} characters; Telegram refuses over {limit}",
        help.chars().count()
    );
    for command in COMMANDS {
        let one = command_help(command.name).expect("every command has per-command help");
        assert!(
            one.chars().count() <= limit,
            "/help {} is {} characters; Telegram refuses over {limit}",
            command.name,
            one.chars().count()
        );
    }
}

/// Every entry carries real prose and a well-formed name — no placeholder can ship.
#[test]
fn every_registered_command_is_fully_described() {
    for command in COMMANDS {
        assert!(
            command.name.starts_with('/') && command.name.len() > 1,
            "`{}` is a well-formed command word",
            command.name
        );
        assert!(
            !command.summary.trim().is_empty(),
            "`{}` has a one-line summary",
            command.name
        );
        assert!(
            command.detail.trim().len() > command.summary.trim().len(),
            "`{}`'s /help <cmd> detail says more than its one-liner",
            command.name
        );
        assert!(
            command_help(command.name).is_some(),
            "/help {} resolves",
            command.name
        );
    }
}

/// Names and aliases are unique, and every one of them resolves through the dispatcher's own
/// [`lookup`] — including with a `@BotName` suffix, which is how Telegram delivers commands in a
/// group.
#[test]
fn names_and_aliases_are_unique_and_all_resolve() {
    let mut seen: Vec<String> = Vec::new();
    for command in COMMANDS {
        for word in std::iter::once(command.name).chain(command.aliases.iter().copied()) {
            assert!(
                !seen.contains(&word.to_string()),
                "`{word}` is registered twice"
            );
            seen.push(word.to_string());
            assert_eq!(
                lookup(word).map(|c| c.name),
                Some(command.name),
                "`{word}` resolves to `{}`",
                command.name
            );
            assert_eq!(
                lookup(&format!("{word}@dreggnet_bot")).map(|c| c.name),
                Some(command.name),
                "`{word}@dreggnet_bot` (the group form) resolves to `{}`",
                command.name
            );
        }
    }
    assert_eq!(
        lookup("/nope"),
        None,
        "an unregistered word does not resolve"
    );
}

/// **Every registered command actually DISPATCHES** — none is documented-but-unrouted. A command
/// in the registry that fell through would be reported as `Unknown`, which is exactly the lie the
/// registry exists to prevent.
#[test]
fn every_registered_command_dispatches() {
    let mut host: TelegramHost<MockTransport> =
        TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE]);
    for command in COMMANDS {
        for word in std::iter::once(command.name).chain(command.aliases.iter().copied()) {
            let (reply, decision) = route_text_decided(&mut host, CHAT, None, ALICE, word);
            assert!(
                !matches!(decision, TextDecision::Unknown { .. }),
                "`{word}` is registered but the dispatcher does not route it: {decision:?}"
            );
            // …and NOT `Ignored` either. A registry entry with no dispatcher arm used to fall
            // through to the free-text path and be reported as ordinary chatter — the assertion
            // above passes for that, so on its own it is a gate that cannot go red. `Ignored` is
            // the SILENCE the registry exists to make impossible.
            assert!(
                !matches!(decision, TextDecision::Ignored),
                "`{word}` is registered but fell through to the free-text path (silence): \
                 {decision:?}"
            );
            assert!(
                reply.is_some() || matches!(decision, TextDecision::Menu),
                "`{word}` answers something the user can see (the offerings menu IS its own \
                 reply, so `Menu` is the one decision allowed to reply `None`): {decision:?}"
            );
        }
    }
}

/// An UNREGISTERED slash command is refused with an honest, legible reply — not silence. The live
/// bot's audit shows a real user typing `/descent` and getting nothing back at all.
#[test]
fn an_unregistered_command_says_so_instead_of_staying_silent() {
    let mut host: TelegramHost<MockTransport> =
        TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE]);
    let (reply, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/descent");
    assert!(
        matches!(&decision, TextDecision::Unknown { cmd } if cmd == "/descent"),
        "{decision:?}"
    );
    let reply = reply.expect("an unknown command gets a reply, not silence");
    assert!(
        reply.contains("/descent") && reply.contains("/help"),
        "the refusal names the word and points at /help: {reply}"
    );
}

/// `/help <cmd>` renders ONE command, and an unknown argument falls back to the full list while
/// saying so.
#[test]
fn per_command_help_answers_one_command() {
    let mut host: TelegramHost<MockTransport> =
        TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE]);

    let (reply, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/help open");
    assert!(matches!(decision, TextDecision::Help), "{decision:?}");
    let reply = reply.expect("/help open answers");
    let open = lookup("/open").expect("/open is registered");
    assert!(reply.contains(open.detail), "it renders /open's detail");
    assert!(
        reply.len() < help_text().len(),
        "per-command help is not the whole list"
    );

    // With the slash, too.
    let (slashed, _) = route_text_decided(&mut host, CHAT, None, ALICE, "/help /open");
    assert_eq!(slashed, Some(reply), "`/help /open` == `/help open`");

    let (unknown, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/help wibble");
    assert!(matches!(decision, TextDecision::Help), "{decision:?}");
    let unknown = unknown.expect("an unknown /help argument answers");
    assert!(
        unknown.contains("No command") && unknown.contains(&open.usage()),
        "it says there is no such command AND falls back to the full list"
    );
}

/// **The escape is documented and always answers.** A user who is stuck must be able to find the
/// way out in `/help` itself.
#[test]
fn the_escape_hatch_is_documented() {
    let help = help_text();
    assert!(
        help.contains("/cancel"),
        "/help documents the escape hatch:\n{help}"
    );
    assert!(
        help.to_lowercase().contains("stuck"),
        "/help says what to do when stuck:\n{help}"
    );
    let cancel = lookup("/cancel").expect("/cancel is registered");
    assert!(cancel.in_menu, "/cancel is in Telegram's own / menu");
    for alias in ["/reset", "/stop"] {
        assert_eq!(
            lookup(alias).map(|c| c.name),
            Some("/cancel"),
            "{alias} is an escape alias"
        );
    }
}

/// **Telegram's `/` menu is registered from the same table** — and within the Bot API's limits.
#[test]
fn the_bot_father_command_list_comes_from_the_registry() {
    let menu = bot_father_commands();
    assert!(
        !menu.is_empty(),
        "the client-side / menu is registered (the live bot's getMyCommands returned [])"
    );
    for (name, description) in &menu {
        assert!(
            !name.starts_with('/'),
            "setMyCommands takes the bare word, not `/{name}`"
        );
        assert!(
            name.len() <= 32
                && name
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_'),
            "`{name}` fits the Bot API's command grammar"
        );
        assert!(
            (1..=256).contains(&description.chars().count()),
            "`{name}`'s description fits the 1..=256 ceiling"
        );
        assert!(
            lookup(name).is_some(),
            "`{name}` in the / menu is a command the dispatcher routes"
        );
    }
    let expected = COMMANDS.iter().filter(|c| c.in_menu).count();
    assert_eq!(menu.len(), expected, "every in-menu command is registered");
}
