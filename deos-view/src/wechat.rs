//! **The WeChat Official-Account backend** — the [`ViewNode`] IR → an OA text message with a
//! **numbered reply list**.
//!
//! WeChat OA forbids arbitrary per-message buttons (no inline keyboard, no components). The
//! OA-native way to offer dynamic choices is a `1.`-indexed list in the message text, to which the
//! user **replies with the number** (the reply arrives as an ordinary inbound text message). So the
//! WeChat projection of a card is:
//!
//! ```text
//!   <the prose>                       ← the SHARED ViewNode→text walk (crate::text::render_text)
//!
//!   Reply with the number of your move:
//!   1. Vote                           ← the tree's actuations, in walk order (crate::backend::actuations)
//!   2. 🔒 Pass (locked)               ← a !enabled affordance: the cap tooth SHOWN, not hidden
//! ```
//!
//! Two halves, both from the ONE IR:
//! * **prose** — [`crate::text::render_text`], the SAME walk [`crate::telegram::TelegramBackend`]
//!   uses (full node coverage: every container recurses; `Menu`/`Button` are omitted because they
//!   ride the numbered block, not the prose). No second subset walker.
//! * **affordances** — [`crate::backend::actuations`] over the SAME tree, numbered 1-based in walk
//!   order. A `!enabled` entry keeps its number and is rendered locked ([`LOCK_GLYPH`] + `(locked)`),
//!   never dropped: the refusal is in-band. The `enabled` bit is whatever the render pipeline
//!   ([`crate::pipeline`]) stamped — i.e. the FOUR-conjunct membrane/reactive gate for THIS viewer at
//!   THIS height, if the caller rendered through it.
//!
//! **The codec** ([`crate::affordance::AffordanceTransport::WeChat`]) is a PAIR, because the channel
//! is positional: a user's reply carries a NUMBER, not an id. [`WeChatMessage::resolve`] takes the
//! inbound text to the `{turn, arg}` it names, accepting BOTH
//! * a **position** — `"2"` / `"2."` / `"2 trade blows"` ([`crate::affordance::wechat_reply_index`]),
//!   resolved against the numbered list THIS message presented; and
//! * a marked **id** — `#<turn>:<arg>` (what each option carries, and what a Mini-Program card's
//!   button posts back), decoded by the ONE codec.
//!
//! An unmarked, non-numeric line is ordinary user prose (WeChat's inbound channel is free text) and
//! resolves to `None` — never a press the surface did not mint.
//!
//! HONEST SCOPE: `dreggnet-wechat` today renders through [`crate::text::render_text`] and keeps its
//! numbered codec crate-local (its `api::{parse_reply_index, render_affordance_block}`); this backend
//! is the deos-view home of exactly that shape, over the whole IR rather than a passed `Action` list.
//! Adopting it there (`WeChatFrontend::present` → `WeChatBackend::render`, `collect` →
//! [`WeChatMessage::resolve`]) is a follow-up in that crate.

use crate::affordance::{
    affordance_id, parse_affordance_id, wechat_reply_index, AffordanceTransport,
};
use crate::backend::{actuations, SurfaceBackend};
use crate::text::render_text;
use crate::tree::ViewNode;

/// The dim lock glyph prefixing a `!enabled` (refused) affordance's numbered line — the cap tooth
/// SHOWN, not hidden. The line keeps its reply number; the executor refuses the move on fire.
/// (Byte-identical to the live loop's `dreggnet_wechat::api::LOCK_GLYPH`.)
pub const LOCK_GLYPH: &str = "🔒 ";

/// The header above the numbered block — it tells the user how to act on a channel with no buttons.
pub const REPLY_HEADER: &str = "Reply with the number of your move:";

/// One numbered option in a WeChat OA message — an actuation of the rendered tree, at its 1-based
/// reply POSITION, carrying both the label the user reads and the `{turn, arg}` (plus its marked
/// [`AffordanceTransport::WeChat`] id) the executor fires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeChatOption {
    /// The 1-based reply number (the user types this).
    pub index: usize,
    /// The label shown on the numbered line.
    pub label: String,
    /// The affordance the pick fires.
    pub turn: String,
    /// The argument the pick carries.
    pub arg: i64,
    /// The render-time gate verdict. `false` → the line is rendered locked (kept + numbered).
    pub enabled: bool,
    /// The marked id (`#<turn>:<arg>`) — what a Mini-Program button posts back, and what the OA loop
    /// stores for the position. Minted by the ONE codec ([`affordance_id`]).
    pub id: String,
}

/// **A rendered WeChat OA message** — the text body the OA posts, plus the numbered option table the
/// user's reply is resolved against ([`WeChatMessage::resolve`]).
///
/// The table travels WITH the render (rather than living in backend state), so the backend stays
/// STATELESS like the other bake backends: the caller persists the last presented message per user
/// (exactly what `dreggnet_wechat::PresentedSurface` does) and resolves the next reply against it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeChatMessage {
    /// The full message body — the prose, then (if there are any affordances) a blank line, the
    /// [`REPLY_HEADER`], and the numbered lines.
    pub content: String,
    /// The presented affordances, in walk order, 1-based by [`WeChatOption::index`]. Empty when the
    /// surface offers nothing (a terminal room — nothing to reply).
    pub options: Vec<WeChatOption>,
}

impl WeChatMessage {
    /// **Resolve an inbound reply to the affordance it names** — the positional half of the WeChat
    /// codec. Accepts a reply NUMBER (`"2"`, `"2."`, `"2 trade blows"`) resolved against THIS
    /// message's numbered list, or a marked `#<turn>:<arg>` id (the Mini-Program button path),
    /// decoded by the ONE codec.
    ///
    /// `None` for ordinary prose, an out-of-range number, or an id this transport never minted.
    /// A LOCKED option still resolves (the user may pick it): the refusal is the executor's, in-band
    /// and precise — this render-time bit is a projection, never the authority. Use
    /// [`WeChatMessage::resolve_enabled`] to refuse at the transport instead.
    pub fn resolve(&self, reply: &str) -> Option<(String, i64)> {
        if let Some(n) = wechat_reply_index(reply) {
            let opt = self.options.iter().find(|o| o.index == n)?;
            return Some((opt.turn.clone(), opt.arg));
        }
        parse_affordance_id(reply.trim(), AffordanceTransport::WeChat)
    }

    /// [`resolve`](Self::resolve), refusing a pick whose option is `!enabled` (the render-time gate
    /// said no). Returns the option so a caller can name the refusal to the user.
    pub fn resolve_enabled(&self, reply: &str) -> Option<(String, i64)> {
        let (turn, arg) = self.resolve(reply)?;
        let ok = self
            .options
            .iter()
            .find(|o| o.turn == turn && o.arg == arg)
            .map(|o| o.enabled)
            // An id-carried pick for an affordance NOT in this message's list (a Mini-Program button
            // from an older card) is not something this render can vouch for — let the executor gate.
            .unwrap_or(true);
        ok.then_some((turn, arg))
    }
}

/// **Render a [`ViewNode`] into a WeChat OA message** — prose + the numbered reply block.
///
/// The prose is the shared text walk; the options are the tree's actuations in walk order (see the
/// module doc). A `!enabled` actuation keeps its number and is marked locked.
pub fn render_message(tree: &ViewNode) -> WeChatMessage {
    let options: Vec<WeChatOption> = actuations(tree)
        .into_iter()
        .enumerate()
        .map(|(i, a)| WeChatOption {
            index: i + 1, // 1-based reply number
            id: affordance_id(&a.turn, a.arg, AffordanceTransport::WeChat),
            label: a.label,
            turn: a.turn,
            arg: a.arg,
            enabled: a.enabled,
        })
        .collect();

    let mut content = render_text(tree);
    if !options.is_empty() {
        if !content.is_empty() {
            content.push_str("\n\n");
        }
        content.push_str(REPLY_HEADER);
        for o in &options {
            let n = o.index;
            if o.enabled {
                content.push_str(&format!("\n{n}. {}", o.label));
            } else {
                content.push_str(&format!("\n{n}. {LOCK_GLYPH}{} (locked)", o.label));
            }
        }
    }

    WeChatMessage { content, options }
}

/// **The WeChat [`SurfaceBackend`]** — the [`ViewNode`] IR → an OA text message + its numbered reply
/// table ([`render_message`]). Binds are unused (an OA text message has no in-place live re-read; the
/// caller pre-reads and re-sends).
///
/// [`decode`](SurfaceBackend::decode) routes the marked `#<turn>:<arg>` id through the ONE codec; a
/// user's REPLY NUMBER is positional and is resolved against the presented
/// [`WeChatMessage::resolve`] table (a bare number is not an id — see the module doc).
pub struct WeChatBackend;

impl SurfaceBackend for WeChatBackend {
    type Rendered = WeChatMessage;

    fn transport(&self) -> AffordanceTransport {
        AffordanceTransport::WeChat
    }

    fn render(&self, tree: &ViewNode, _binds: &[u64]) -> WeChatMessage {
        render_message(tree)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::{Crumb, HaloHandle, MenuItem};

    /// A room card: prose in nested containers (a `Table`/`Grid`/`Host`/`Tabs`, which the OLD
    /// WeChat subset walker dropped), plus the actuation half in several shapes.
    fn room() -> ViewNode {
        ViewNode::VStack(vec![
            ViewNode::Section {
                title: "The Cellar".into(),
                tag: String::new(),
                children: vec![
                    ViewNode::Text("A damp room. A rat watches you.".into()),
                    ViewNode::Grid {
                        cols: 2,
                        children: vec![ViewNode::Text("Party: 2".into())],
                    },
                ],
            },
            ViewNode::Host {
                cell: "beef".into(),
                view: Some(Box::new(ViewNode::Text(
                    "Hosted: the ledger is quiet.".into(),
                ))),
            },
            ViewNode::Menu {
                items: vec![
                    MenuItem {
                        label: "Trade blows".into(),
                        turn: "fight".into(),
                        arg: 1,
                        enabled: true,
                    },
                    MenuItem {
                        label: "Open the vault".into(),
                        turn: "vault".into(),
                        arg: 0,
                        enabled: false, // the gate refused it — SHOWN locked, not hidden
                    },
                ],
            },
            ViewNode::Button {
                label: "Flee".into(),
                turn: "flee".into(),
                arg: 0,
            },
        ])
    }

    /// The full projection: prose from the SHARED walk (with the nested containers the old subset
    /// walker dropped), then the numbered block — locked entries keep their number.
    #[test]
    fn renders_the_numbered_oa_message_with_full_node_coverage() {
        let msg = WeChatBackend.render(&room(), &[]);
        assert_eq!(
            msg.content,
            "The Cellar\n\
             A damp room. A rat watches you.\n\
             Party: 2\n\
             Hosted: the ledger is quiet.\n\
             \n\
             Reply with the number of your move:\n\
             1. Trade blows\n\
             2. 🔒 Open the vault (locked)\n\
             3. Flee"
        );
        assert_eq!(msg.options.len(), 3);
        assert_eq!(msg.options[1].index, 2);
        assert_eq!(msg.options[1].id, "#vault:0");
        assert!(!msg.options[1].enabled);
        // The Menu/Button nodes are NOT in the prose (they ride the numbered block).
        assert!(!msg.content.contains("Trade blows\nOpen"));
    }

    /// The POSITIONAL round-trip: the user replies with a number → the `{turn, arg}` the option
    /// named. Ordinary prose and an out-of-range number resolve to `None` (WeChat's inbound channel
    /// is free text — a chat line is not a press).
    #[test]
    fn a_reply_number_resolves_to_the_affordance_it_names() {
        let msg = WeChatBackend.render(&room(), &[]);
        assert_eq!(msg.resolve("1"), Some(("fight".to_string(), 1)));
        assert_eq!(msg.resolve("2."), Some(("vault".to_string(), 0)));
        assert_eq!(msg.resolve(" 3 flee "), Some(("flee".to_string(), 0)));
        assert_eq!(msg.resolve("9"), None, "no 9th option");
        assert_eq!(msg.resolve("hello there"), None, "prose is not a press");
        // The rendered line round-trips to its own option.
        for o in &msg.options {
            assert_eq!(
                msg.resolve(&format!("{}. {}", o.index, o.label)),
                Some((o.turn.clone(), o.arg))
            );
        }
    }

    /// The ID round-trip (the Mini-Program button path): each option's `#<turn>:<arg>` decodes back
    /// through the ONE codec — via the backend's own `decode` (the trait's default, keyed by
    /// `transport()`) and via `resolve`.
    #[test]
    fn the_marked_id_round_trips_through_the_one_codec() {
        let msg = WeChatBackend.render(&room(), &[]);
        for o in &msg.options {
            assert_eq!(
                WeChatBackend.decode(&o.id),
                Some((o.turn.clone(), o.arg)),
                "{} decodes through SurfaceBackend::decode",
                o.id
            );
            assert_eq!(msg.resolve(&o.id), Some((o.turn.clone(), o.arg)));
        }
        // An UNMARKED id (a user typing the telegram shape in chat) is not ours.
        assert_eq!(WeChatBackend.decode("fight:1"), None);
    }

    /// The LOCKED option is offered (numbered, visible) but `resolve_enabled` refuses the pick at
    /// the transport — the render-time gate reaching the reply loop. `resolve` still returns it (the
    /// executor is the authority; the caller chooses which refusal to speak).
    #[test]
    fn a_locked_option_is_shown_numbered_and_refused_by_the_gated_resolve() {
        let msg = WeChatBackend.render(&room(), &[]);
        assert!(msg.content.contains("2. 🔒 Open the vault (locked)"));
        assert_eq!(msg.resolve("2"), Some(("vault".to_string(), 0)));
        assert_eq!(
            msg.resolve_enabled("2"),
            None,
            "the render-time gate refuses the locked pick at the transport"
        );
        assert_eq!(
            msg.resolve_enabled("1"),
            Some(("fight".to_string(), 1)),
            "an enabled pick passes"
        );
    }

    /// A surface with NO affordances (a terminal room) is prose only — no header, no numbered block.
    #[test]
    fn a_surface_with_no_affordances_has_no_numbered_block() {
        let msg = WeChatBackend.render(&ViewNode::Text("The end.".into()), &[]);
        assert_eq!(msg.content, "The end.");
        assert!(msg.options.is_empty());
        assert_eq!(msg.resolve("1"), None);
    }

    /// Every fixed-`{turn, arg}` node shape reaches the numbered list (halo handles, breadcrumbs,
    /// tabs — not just menus/buttons): the affordance half has full node coverage too.
    #[test]
    fn every_actuation_shape_gets_a_number() {
        let tree = ViewNode::VStack(vec![
            ViewNode::Halo {
                target_slot: 0,
                handles: vec![HaloHandle {
                    glyph: "✂".into(),
                    turn: "cut".into(),
                    arg: 2,
                    enabled: true,
                }],
            },
            ViewNode::Breadcrumb {
                items: vec![Crumb {
                    label: "up".into(),
                    turn: "nav".into(),
                    arg: 1,
                }],
            },
            ViewNode::Tabs {
                tabs: vec!["Log".into()],
                selected_slot: 0,
                select_turn: "tab".into(),
                panels: vec![ViewNode::Text("…".into())],
            },
        ]);
        let msg = WeChatBackend.render(&tree, &[]);
        let picks: Vec<(usize, String, i64)> = msg
            .options
            .iter()
            .map(|o| (o.index, o.turn.clone(), o.arg))
            .collect();
        assert_eq!(
            picks,
            vec![
                (1, "cut".to_string(), 2),
                (2, "nav".to_string(), 1),
                (3, "tab".to_string(), 0),
            ]
        );
    }
}
