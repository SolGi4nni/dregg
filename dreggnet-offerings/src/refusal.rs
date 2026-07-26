//! **THE PLAYER-FACING REFUSAL VOCABULARY — one sentence per condition, for every surface.**
//!
//! An audit of every player-visible "no" in the product found ONE root cause behind nine failure
//! modes: a `Display`/`Debug` impl written for a log line leaked, unfiltered, into a player-facing
//! string. Nobody decided to be rude to a player; a `format!("{e}")` or a `{decision:?}` did it for
//! them. And the second finding was worse than the first: **the same condition got fixed in one
//! surface and never propagated.** Telegram's stale-control dead end was diagnosed and repaired at
//! `dreggnet_telegram::runtime` while its own sibling three hundred lines away kept the dead end,
//! and so did the web's two, and Discord's two, and tug's two — five wordings of one condition, each
//! one somebody's careful afternoon.
//!
//! So the copy lives HERE, as functions, and the surfaces call them. A sixth wording is then a
//! *diff to this file* rather than a phrase somebody types at a new call site.
//!
//! ## The house style these functions conform to
//!
//! Every player-facing refusal must:
//!
//! 1. **name the specific failing check or cause in plain words** — never a system-component name
//!    (`executor`, `world-cell`, `teeth`, `oracle`), never a raw id or 64-char hex, never a
//!    `Debug` dump, never a `snake_case` wire field / function / env-var symbol;
//! 2. **say whether anything was lost** — the one rule the good refusals in this house never break
//!    and the bad ones never keep; and
//! 3. **give one concrete next action** the reader can actually take.
//!
//! [`dreggnet-web`'s identity-link and seed-identity pages][exemplar] are the exemplars, and their
//! discipline is enforced by tests. [`audit_player_text`] is the generalisation of those tests: it
//! is the scanner a refusal-copy gate runs, and it lives beside the copy it checks so a new
//! sentence and its check cannot drift apart.
//!
//! [exemplar]: https://github.com/dregg/dregg/blob/main/dreggnet-web/src/identity_link.rs
//!
//! ## The operator's half is not thrown away
//!
//! Sanding a string down to a sentence a player can act on would be a *worse* failure mode if the
//! detail vanished. Where a refusal is really about missing/broken server machinery, the internals
//! move to an `operator_diagnostic()` beside the `Display`
//! ([`crate::OfferingError::operator_diagnostic`], [`crate::session::PlayRefusal::operator_diagnostic`],
//! `spween_dregg::WorldError::operator_diagnostic`, `cell::program::ProgramError::operator_diagnostic`
//! — the pattern this module is the copy half of), and the surface logs it at `tracing::error!`
//! beside the sentence it shows.

/// **The stale-control refusal** — the ONE sentence for *"the control you just used is not one the
/// live game offers"*, whatever drew it and whatever surface it was drawn on.
///
/// The condition is single even though its five old wordings made it look like five bugs: a browser
/// form POSTed after the board moved, a Telegram inline button minted before a restart, a Discord
/// `custom_id` from an older deployment, a tug decision index that no longer names a decision, an
/// unknown verb spliced onto a native Descent action. In every case the same three things are true —
/// **the live surface does not offer that control, nothing was changed, and there IS a working
/// control somewhere the reader can reach.** The old wordings said the first, forgot the second, and
/// answered the third with silence, deployment language ("this bot build"), or a `{decision:?}` dump.
///
/// `next_step` is the surface's own working control, and it is a required argument on purpose: a
/// refusal with no next action is the failure mode this function exists to make impossible to write.
/// Phrase it as an instruction ("Reload the page…", "Send /offerings…"). Surfaces with no idea what
/// frontend is reading them use [`stale_control_refresh`].
///
/// ```
/// # use dreggnet_offerings::refusal::stale_control;
/// let why = stale_control("Reload the page to see the current board and pick up from there.");
/// assert!(why.contains("nothing was changed"));
/// assert!(why.ends_with("pick up from there."));
/// ```
pub fn stale_control(next_step: &str) -> String {
    format!(
        "That control is not on the current surface — the game moved on since this view was drawn, \
         so nothing was changed. {next_step}"
    )
}

/// [`stale_control`] for a refusal minted BELOW any frontend — an offering/engine layer that does
/// not know whether a browser, a chat or a bot is reading it, and so cannot name a reload button or
/// a slash command. "Refresh" is the one instruction true on all of them.
pub fn stale_control_refresh() -> String {
    stale_control("Refresh the game to see the moves it offers now.")
}

/// **The wrong-player refusal** — the ONE sentence for *"this run is bound to a player who is not
/// the one acting"*.
///
/// It replaces eight sites that threw **two 64-character Ed25519 hex strings** at a player, in five
/// wordings ("this Descent is bound to {}; {} cannot move it", "this traversal is bound to …",
/// "this errand belongs to …", "only public seat 0 ({}) may …", "{} is not in this proof-bound raid
/// roster"). The hex was never readable and never actionable, and — this is the part that makes the
/// whole shape unnecessary — **every one of those branches only fires when `bound != actor`**, so
/// the reader never needs to tell the two keys apart. Both go.
///
/// What a player in this state actually needs is the *account* diagnosis, because the overwhelmingly
/// common cause is a second device (or a second platform) deriving a different identity for the same
/// human: they are signed in as somebody else. The second most common cause is that it is genuinely
/// not their run, and then "you're just watching" is the whole truth.
///
/// `noun` names the thing per surface — `"run"`, `"Descent"`, `"traversal"`, `"errand"`, `"raid"`,
/// `"raid's proof upload"` — and the sentence does NOT change with it.
///
/// ```
/// # use dreggnet_offerings::refusal::belongs_to_another_player;
/// let why = belongs_to_another_player("traversal");
/// assert!(why.starts_with("This traversal belongs to a different player"));
/// assert!(why.contains("Nothing was changed"));
/// ```
pub fn belongs_to_another_player(noun: &str) -> String {
    format!(
        "This {noun} belongs to a different player than the one you're signed in as. Nothing was \
         changed. If it's yours from another device, switch back to that account — otherwise you're \
         just watching."
    )
}

/// **The generic commit-failure refusal** — the ONE sentence for a refusal whose cause is entirely
/// on our side of the wire and says nothing about the move: a durability write that would not land,
/// a federation peer that would not confirm, a gate that did not lower to checkable form.
///
/// This is the player half of the split every such error owes them. The internals go to the error's
/// own `operator_diagnostic()` and into a log line; the reader gets the two facts that change what
/// they do next — **nothing was changed, and retrying is the right move.**
///
/// Kept as a `const` rather than a function because it takes no parameters and is asserted against
/// verbatim by the refusal-copy gate.
pub const COMMIT_FAILED_NOTHING_CHANGED: &str =
    "Something went wrong committing that move — nothing was changed. Try again in a moment.";

/// **The generic server-side-store refusal** — the ONE sentence for "we could not read or write our
/// own records", the condition ~30 Discord command sites answered by pasting raw `sqlx` text
/// ("Database Error: error returned from database: database is locked").
///
/// Those 30 all broke the same rule, and it was not the rule about jargon: **none of them said
/// whether anything was lost.** A player who is told "database is locked" after pressing *transfer*
/// has no way to know whether their DEC moved. Every site this replaces is a read or a pre-flight
/// check with nothing behind it, so the sentence can promise what it promises.
///
/// ⚑ It is therefore NOT the right sentence for a failure *after* a mutation. A site that cannot
/// honestly say "nothing was changed" must say what it does know instead — see `pay.rs`'s explicit
/// "this is NOT a zero" copy, which is the model for that case.
pub const STORE_FAILED_NOTHING_CHANGED: &str =
    "Something went wrong on our end — nothing was changed. Try again in a moment.";

/// ⚑ **THE ONE CALL that replaces `Outcome::Refused(e.to_string())`.** Logs the operator half of a
/// world-cell commit failure and returns the player half — so the two audiences cannot be collapsed
/// back into one string by a future call site, and sanding the sentence down cannot lose the detail.
///
/// This is the whole fix for the widest-reach leak in the audit. `spween_dregg::WorldError`'s
/// `Display` prepends the name of an internal architecture ("world-cell turn refused: …",
/// "under-gated choice refused: method `select` did not lower fully to executor teeth (handler-only
/// gate; drive it through the runtime path)") and it was the GENERIC FALLBACK for every commit in
/// Automatafl, Tug, the dungeon and the native Descent — ~12 sites, all spelled
/// `Err(e) => Outcome::Refused(e.to_string())`. They are all spelled `Err(e) =>
/// Outcome::Refused(refuse_world_error(&e))` now.
///
/// A [`WorldError::Refused`] is returned VERBATIM and logs nothing: its text is the game's own rules
/// talking, it is what the player should read, and re-logging it would be noise on the ordinary path
/// (a refused move is the referee WORKING). Everything else is a fault on this server, so the player
/// gets [`COMMIT_FAILED_NOTHING_CHANGED`] and an operator gets the cause plus — via `#[track_caller]`
/// — the exact call site that refused.
#[track_caller]
pub fn refuse_world_error(error: &spween_dregg::WorldError) -> String {
    if let Some(detail) = error.operator_diagnostic() {
        let at = std::panic::Location::caller();
        tracing::error!(
            target: "dregg::refusal",
            at = %at,
            detail = %detail,
            "a world-cell commit failed for a reason that is NOT about the player's move; the \
             player was shown the generic commit-failure sentence and nothing was committed"
        );
    }
    error.player_message()
}

/// ⚑ **The sibling of [`refuse_world_error`] for a RULES ORACLE that could not answer.** Logs the
/// operator half and returns [`COMMIT_FAILED_NOTHING_CHANGED`].
///
/// A shipped game's verified rule-checker is reached over the Lean FFI, and every one of those calls
/// is `Result<_, String>` where the `String` is a machinery diagnostic — a missing export, an archive
/// this binary was built without. Automatafl and Tug pasted those straight into refusals ("the game
/// oracle could not run the round: …", "the goal assignment is unavailable: …", "the round cannot be
/// adjudicated: …"), which names a piece of our machinery to a player and then tells them nothing they
/// can do. The condition is real and fail-closed — the game refuses rather than guessing at a verdict —
/// but a player did not choose it and cannot fix it.
///
/// `what` names the call for the log, not for the reader (`"roundStep"`, `"stock goals"`,
/// `"adjudicate"`).
#[track_caller]
pub fn refuse_rules_unavailable(what: &str, detail: &str) -> String {
    let at = std::panic::Location::caller();
    tracing::error!(
        target: "dregg::refusal",
        at = %at,
        call = what,
        detail = detail,
        "a verified rules oracle reached NO VERDICT, so the game refused fail-closed rather than \
         guess at one; nothing was committed. This is a build/deployment fault — the linked Lean \
         archive is absent or does not export what this game calls"
    );
    COMMIT_FAILED_NOTHING_CHANGED.to_string()
}

/// A banned shape found in a player-facing string by [`audit_player_text`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BannedShape {
    /// A run of ≥32 hex characters — a key, a root, a session id, a commitment. Unreadable to a
    /// person and never the next action.
    RawHexRun {
        /// The offending run, truncated for the assertion message.
        excerpt: String,
    },
    /// A `Debug` dump: a Rust struct/enum/tuple literal shape (`Foo { .. }`, `Foo(..)`, `[..]`) that
    /// only a `{:?}` produces.
    DebugDump {
        /// The offending fragment.
        excerpt: String,
    },
    /// A `snake_case` or `SCREAMING_SNAKE` identifier — a wire field, a function, an env var, a
    /// C-ABI export. A symbol is never a player's next action, because a player cannot call it.
    SymbolAsFix {
        /// The offending identifier.
        symbol: String,
    },
    /// A system-component name. A player does not have an executor.
    ComponentName {
        /// The offending word.
        word: String,
    },
    /// The string never tells the reader what to do next.
    NoNextAction,
    /// The string never says whether anything was committed / lost.
    NoLossStatement,
}

impl std::fmt::Display for BannedShape {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BannedShape::RawHexRun { excerpt } => write!(
                f,
                "a raw hex run (`{excerpt}`) — a player cannot read a key, and it is never the next action"
            ),
            BannedShape::DebugDump { excerpt } => write!(
                f,
                "a Debug dump (`{excerpt}`) — an internal Rust value reached a person's screen"
            ),
            BannedShape::SymbolAsFix { symbol } => write!(
                f,
                "a symbol as the fix (`{symbol}`) — a player cannot set an env var or call a function"
            ),
            BannedShape::ComponentName { word } => write!(
                f,
                "a system-component name (`{word}`) — name the failing CHECK, not the machinery"
            ),
            BannedShape::NoNextAction => write!(
                f,
                "no next action — a refusal with no way forward reads as broken, not as refused"
            ),
            BannedShape::NoLossStatement => write!(
                f,
                "no statement of what was lost — the reader cannot tell whether their move landed"
            ),
        }
    }
}

/// Words that name a piece of our machinery. A player has no executor, no world-cell, no oracle and
/// no teeth; naming one tells them nothing and frames their screen as the problem.
const BANNED_COMPONENT_WORDS: &[&str] = &[
    "executor",
    "world-cell",
    "world cell",
    "teeth",
    "oracle",
    "substrate",
    "bot build",
    "AIR",
    "sqlx",
];

/// `snake_case`-ish identifiers that are legitimate ENGLISH in a player sentence and must not be
/// mistaken for symbols. Kept deliberately tiny: a long allowlist is how a linter stops linting.
const SYMBOL_ALLOWLIST: &[&str] = &["/cancel", "/close", "/offerings", "/start", "/status"];

/// Phrases that constitute a **next action** — something the reader can actually do with what they
/// have just been told. The list is the vocabulary the shipped copy uses, not an attempt at English.
///
/// ⚑ **The last group is the legitimate exception**, and it has to be here or the rule is a lie. For
/// the class of refusal whose cause is missing SERVER machinery — the constraint oracle absent from a
/// build, a node token an operator holds — there IS no action the reader can take, and inventing one
/// ("try again") would be the dishonesty this whole audit is about. The honest next action is to say
/// where the problem lives so they can escalate: *"that is a fault in how this server was built, not
/// in what you did — the server log names the missing piece"*. That is the shape
/// `cell::program::ProgramError::ConstraintOracleUnavailable` already ships, and it is the shape
/// [`crate::session::PlayRefusal::OracleUnavailable`] now ships.
const NEXT_ACTION_MARKERS: &[&str] = &[
    // Do this instead.
    "reload",
    "refresh",
    "try again",
    "send /",
    "run /",
    "open ",
    "press",
    "switch back",
    "check ",
    "use the",
    "start ",
    "pick ",
    "claim ",
    "wait ",
    "ask ",
    "close this page",
    "sign in",
    "contact",
    // …or, honestly, nothing: here is whose problem it is.
    "the server log",
    "an operator",
    "on our side",
    "not in what you did",
    "just watching",
];

/// Phrases that constitute a **loss statement** — an explicit answer to *"did my move land?"*.
///
/// ⚑ The primary marker is the bare word **"nothing"**, on purpose. It is this house's actual tell —
/// "nothing was changed", "nothing committed — anti-ghost", "nothing was opened", "nothing was
/// linked", "nothing was fired", "nothing was re-executed", "an unconfirmed link must record
/// NOTHING" — and enumerating the past participles instead just meant the enumeration went stale
/// (this list began as ten of them and missed "nothing was linked", which is the EXEMPLAR page's own
/// wording). The remaining entries are the refusals that state the opposite: something DID land, and
/// the copy's job is to say so rather than to reassure.
const LOSS_MARKERS: &[&str] = &[
    "nothing ",
    "not a zero",
    "was committed",
    "did commit",
    "was changed",
];

/// **THE REFUSAL-COPY GATE, as a function.** Scan one player-facing string for the shapes this
/// audit found, and return every violation.
///
/// This is the generalisation of three tests that already guard one page
/// (`identity_link.rs`: *"the refusal must not blame the player"*, *"never a bare 'invalid'"*,
/// *"a refusal must say nothing happened"*) — hand-written assertions about one module's copy, which
/// is why they caught nothing anywhere else. As a function over an arbitrary string it can be
/// pointed at the strings a *shipped surface actually produces*, which is what the gate tests do.
///
/// `require_next_action` and `require_loss_statement` are separate switches because the two carry
/// different false-positive risk: the banned SHAPES are mechanical and safe to demand everywhere,
/// while "does this sentence contain an instruction" is a judgement a marker list only approximates.
/// A gate that scans a whole surface's refusal vocabulary turns them on; a gate spot-checking one
/// fragment (a clause that will be embedded in a larger message that carries the next action) leaves
/// them off.
///
/// ```
/// # use dreggnet_offerings::refusal::{audit_player_text, stale_control_refresh};
/// assert_eq!(audit_player_text(&stale_control_refresh(), true, true), Vec::new());
/// let leak = "method `comp` does not name decision 3 (Secret { card: 9 })";
/// assert!(!audit_player_text(leak, true, true).is_empty());
/// ```
pub fn audit_player_text(
    text: &str,
    require_next_action: bool,
    require_loss_statement: bool,
) -> Vec<BannedShape> {
    let mut found = Vec::new();
    let lower = text.to_lowercase();

    // ── A RAW HEX RUN. 32 hex chars is the shortest thing in this product that is a key or a root
    //    (a 16-byte id); the sites this gate was written for threw 64. Counted over CHARS so a
    //    UTF-8 refusal cannot panic the linter, and reset by any non-hex char, so an ordinary word
    //    like "decade" (6 hex letters) cannot trip it.
    {
        let mut run = String::new();
        let flush = |run: &mut String, found: &mut Vec<BannedShape>| {
            if run.chars().count() >= 32 {
                found.push(BannedShape::RawHexRun {
                    excerpt: run.chars().take(24).collect::<String>() + "…",
                });
            }
            run.clear();
        };
        for c in text.chars() {
            if c.is_ascii_hexdigit() {
                run.push(c);
            } else {
                flush(&mut run, &mut found);
            }
        }
        flush(&mut run, &mut found);
    }

    // ── A DEBUG DUMP. `{:?}` on a struct/enum with fields prints `Name { field: value }`; on a
    //    newtype/tuple variant it prints `Name(value)`. The struct shape is unambiguous — English
    //    does not put a brace after a capitalised word — so it is the one this checks. A braced
    //    dump is the exact shape of tug's `{decision:?}` and the game spine's `{expected:?}`.
    if let Some(at) = find_debug_struct_dump(text) {
        found.push(BannedShape::DebugDump {
            excerpt: text[at..].chars().take(32).collect::<String>(),
        });
    }

    // ── A SYMBOL AS THE FIX. `snake_case` / `SCREAMING_SNAKE` with an underscore between two
    //    alphanumerics: `game_host_incarnation`, `DEVNET_API_TOKEN`, `dregg_deleg_admit`. An
    //    underscore is the tell — a player-facing sentence has no reason to contain one.
    for symbol in snake_case_identifiers(text) {
        if !SYMBOL_ALLOWLIST.contains(&symbol.as_str()) {
            found.push(BannedShape::SymbolAsFix { symbol });
        }
    }

    // ── A RUST PATH: `crate::module::thing`, `dreggnet_web::refusal`.
    if text.contains("::") {
        found.push(BannedShape::SymbolAsFix {
            symbol: "::".to_string(),
        });
    }

    // ── A DOTTED MODULE PATH: `Dregg2.Apps.DelegAdmit.delegAdmit` — the Lean theorem path that was
    //    sitting in `PlayRefusal::OracleUnavailable`, waiting for delegated play to be wired up.
    //    THREE-or-more dot-joined alphanumeric parts of length ≥ 2, so ordinary prose ("e.g.", a
    //    sentence ending before a capital, a version like `1.0.3`) cannot trip it: an English
    //    sentence never joins three words with dots and no spaces.
    for token in text.split_whitespace() {
        let parts: Vec<&str> = token
            .trim_matches(|c: char| !c.is_ascii_alphanumeric())
            .split('.')
            .collect();
        if parts.len() >= 3
            && parts
                .iter()
                .all(|p| p.len() >= 2 && p.chars().all(|c| c.is_ascii_alphanumeric()))
        {
            found.push(BannedShape::SymbolAsFix {
                symbol: token.to_string(),
            });
        }
    }

    // ── A SYSTEM-COMPONENT NAME.
    for word in BANNED_COMPONENT_WORDS {
        // `AIR` is checked case-sensitively; every other word would match inside ordinary prose
        // ("air", "repair") if it were not.
        let hit = if word.chars().all(|c| c.is_ascii_uppercase()) {
            text.split(|c: char| !c.is_ascii_alphanumeric())
                .any(|w| w == *word)
        } else {
            lower.contains(*word)
        };
        if hit {
            found.push(BannedShape::ComponentName {
                word: (*word).to_string(),
            });
        }
    }

    if require_next_action && !NEXT_ACTION_MARKERS.iter().any(|m| lower.contains(m)) {
        found.push(BannedShape::NoNextAction);
    }
    if require_loss_statement && !LOSS_MARKERS.iter().any(|m| lower.contains(m)) {
        found.push(BannedShape::NoLossStatement);
    }
    found
}

/// The byte offset of a `Name { ` fragment — a `{:?}` of a struct or struct-variant. Returns the
/// offset of the capitalised name so the caller can quote the dump.
fn find_debug_struct_dump(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut i = 0usize;
    while let Some(rel) = text[i..].find(" {") {
        let brace = i + rel;
        // Walk back over the identifier immediately before the space.
        let mut start = brace;
        while start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_') {
            start -= 1;
        }
        let ident = &text[start..brace];
        let capitalised = ident
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_uppercase() && ident.len() > 1);
        // `Foo {}` from a fieldless Debug is still a dump; `Foo { field` is the common one.
        if capitalised && text[brace..].starts_with(" {") {
            return Some(start);
        }
        i = brace + 2;
    }
    None
}

/// Every `snake_case` / `SCREAMING_SNAKE` identifier in `text` — an underscore flanked by
/// alphanumerics, extended to the whole surrounding word.
fn snake_case_identifiers(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for word in text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '/')) {
        let trimmed = word.trim_matches('_');
        if trimmed.contains('_')
            && trimmed
                .split('_')
                .all(|part| !part.is_empty() && part.chars().all(|c| c.is_ascii_alphanumeric()))
        {
            out.push(trimmed.to_string());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑ THE GATE'S OWN TOOTH: it must go RED on the nine strings the audit actually found, and
    /// GREEN on the sentences that replaced them. A linter proven only on its own good examples is
    /// the "documented ≠ detected" failure — so the reds are the real assertions here, and they are
    /// the VERBATIM shipped strings, copied out of the audit.
    #[test]
    fn the_gate_reds_on_every_string_the_audit_found() {
        let leaks: &[(&str, &str)] = &[
            (
                "tug's Debug-dumped decision",
                "method `comp` does not name decision 3 (Secret { card: 9 }, which dispatches under `secret`)",
            ),
            (
                "the game spine's Debug-dumped binding",
                "game authority epoch mismatch for tug / x1: expected GameSessionBinding { incarnation: 3 }, presented GameSessionBinding { incarnation: 4 }",
            ),
            (
                "the wire field name",
                "missing or malformed game_host_incarnation",
            ),
            (
                "two raw Ed25519 keys",
                "this Descent is bound to 3b1f0c9d8e7a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f9a8b7c6d5e4f3a2b1c; \
                 9a8b7c6d5e4f3a2b1c0d9e8f7a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f9a8b cannot move it",
            ),
            (
                "the under-gated choice",
                "under-gated choice refused: method `select` did not lower fully to executor teeth \
                 (handler-only gate; drive it through the runtime path)",
            ),
            (
                "the world-cell prefix",
                "world-cell turn refused: the purse is empty",
            ),
            (
                "a C-ABI symbol and a Lean path",
                "turn refused fail-closed — the verified admission oracle (dregg_deleg_admit / \
                 Dregg2.Apps.DelegAdmit.delegAdmit) reached NO VERDICT: absent",
            ),
            (
                "an env var as the fix",
                "Not authorized to submit the transfer (HTTP 403). This node gates writes behind an \
                 operator token — set `DEVNET_API_TOKEN` for the bot.",
            ),
            (
                "deployment language",
                "This governance control is not recognized by this bot build.",
            ),
            (
                "raw sqlx text with no loss statement",
                "error returned from database: database is locked",
            ),
        ];
        for (what, leak) in leaks {
            let violations = audit_player_text(leak, true, true);
            assert!(
                !violations.is_empty(),
                "the gate must red on {what}: {leak}"
            );
        }
    }

    /// …and GREEN on this module's own vocabulary, which is what every fixed site now emits.
    #[test]
    fn the_gate_greens_on_the_replacement_copy() {
        let good = [
            stale_control_refresh(),
            stale_control("Reload the page to see the current board and pick up from there."),
            stale_control("Send /offerings for a fresh menu, or /cancel to clear this chat."),
            belongs_to_another_player("run"),
            belongs_to_another_player("traversal"),
            belongs_to_another_player("errand"),
            belongs_to_another_player("raid"),
            COMMIT_FAILED_NOTHING_CHANGED.to_string(),
            STORE_FAILED_NOTHING_CHANGED.to_string(),
        ];
        for text in good {
            assert_eq!(
                audit_player_text(&text, true, true),
                Vec::new(),
                "the shared copy must pass its own gate: {text}"
            );
        }
    }

    /// The two checks that are judgements rather than shapes, isolated: a sentence with the right
    /// shape and no way forward is still a bad refusal, and so is one that leaves the reader unsure
    /// whether their move landed.
    #[test]
    fn a_shapely_dead_end_is_still_caught() {
        let dead_end = "That affordance is not on the current surface.";
        assert_eq!(
            audit_player_text(dead_end, false, false),
            Vec::new(),
            "it carries no banned SHAPE — which is exactly why the old wording survived"
        );
        assert!(audit_player_text(dead_end, true, false).contains(&BannedShape::NoNextAction));
        assert!(audit_player_text(dead_end, false, true).contains(&BannedShape::NoLossStatement));
    }

    /// ⚑ THE FALSE-POSITIVE TOOTH. A linter that reds on ordinary English is a linter somebody
    /// turns off. These are player sentences the audit explicitly VERIFIED as good, plus the
    /// near-misses that a naive regex eats.
    #[test]
    fn the_gate_does_not_red_on_verified_good_copy() {
        let whole_messages = [
            // A near-miss: hex letters in ordinary words, and a decimal that is not a key.
            "The deed decade faded; nothing was changed, so try again in a moment.",
            // A slash command is a real next action, not a symbol.
            "No session in this chat yet — nothing was changed. Send /offerings to start one.",
            // A brace in prose after a lowercase word is not a Debug dump.
            "Your purse is empty {and the toll is 50} — nothing was changed. Try again later.",
        ];
        for text in whole_messages {
            assert_eq!(
                audit_player_text(text, true, true),
                Vec::new(),
                "the gate reddened on good copy: {text}"
            );
        }
        // ⚑ AND THE FRAGMENT CASE, which is why the last two arguments exist. An offering's
        // `Outcome::Refused(why)` is a CLAUSE: the host wraps it ("Refused: {why} (nothing
        // committed — anti-ghost)"), so the loss statement and often the next action belong to the
        // wrapper, not the clause. The MARKED-square message — which the audit verified as GOOD —
        // would red under the whole-message rules and must not under the fragment rules.
        let marked = "(3,4) is MARKED — a clash burned that square, and for the rest of this turn \
                      no piece may leave it or land on it";
        assert_eq!(
            audit_player_text(marked, false, false),
            Vec::new(),
            "a verified-good refusal CLAUSE carries no banned shape: {marked}"
        );
        assert!(
            audit_player_text(marked, true, true).contains(&BannedShape::NoLossStatement),
            "…and the whole-message rules are strictly stronger, as intended"
        );
    }

    /// ⚑ THE TWO-CRATE PIN. [`COMMIT_FAILED_NOTHING_CHANGED`] is duplicated as a literal in
    /// `spween-dregg` (which sits BELOW this crate, so it cannot import the constant), and a
    /// duplicated literal is a drift waiting to happen — the exact mechanism that gave one condition
    /// five wordings. This asserts the two are the same sentence, so a reword in one place goes red
    /// instead of silently shipping two.
    #[test]
    fn the_world_error_player_half_is_this_modules_sentence() {
        use spween_dregg::WorldError;
        for machinery in [
            WorldError::UngatedChoice("select".to_string()),
            WorldError::Durability("the image would not fsync".to_string()),
            WorldError::Federation("peer refused".to_string()),
            WorldError::UnknownTarget("nowhere".to_string()),
        ] {
            assert_eq!(
                machinery.player_message(),
                COMMIT_FAILED_NOTHING_CHANGED,
                "the two crates must say the same sentence"
            );
            assert!(
                machinery.operator_diagnostic().is_some(),
                "…and the detail must not be thrown away: {machinery:?}"
            );
            assert_eq!(
                audit_player_text(&machinery.player_message(), true, true),
                Vec::new()
            );
        }
        // A rules refusal is the game talking; it passes straight through and logs nothing.
        let rules = WorldError::Refused("the purse is empty".to_string());
        assert_eq!(rules.player_message(), "the purse is empty");
        assert_eq!(rules.operator_diagnostic(), None);
        assert_eq!(refuse_world_error(&rules), "the purse is empty");
        // ⚑ And the OLD string — the one ~12 sites shipped — is exactly what the gate reds on, which
        // is the proof this fix is not cosmetic.
        assert!(
            !audit_player_text(
                &WorldError::UngatedChoice("select".to_string()).to_string(),
                true,
                true
            )
            .is_empty(),
            "the Display that leaked must still be gate-red; it is the operator's string now"
        );
    }

    /// A 31-hex-char run is not flagged and a 32 is — the boundary is stated, not incidental.
    #[test]
    fn the_hex_threshold_is_the_shortest_key_this_product_has() {
        let thirty_one = "a".repeat(31);
        let thirty_two = "a".repeat(32);
        let tail = " — nothing was changed. Try again.";
        assert_eq!(
            audit_player_text(&format!("{thirty_one}{tail}"), true, true),
            Vec::new()
        );
        assert!(
            audit_player_text(&format!("{thirty_two}{tail}"), true, true)
                .iter()
                .any(|v| matches!(v, BannedShape::RawHexRun { .. }))
        );
    }
}
