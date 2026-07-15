//! # `TavernOffering` — a **read-surface posting board** (the shared social hub).
//!
//! The tavern is the persistent social PLACE players inhabit between runs — a shared LFG board, a
//! presence seat per patron, and a party-up roster. The live tavern (`dreggnet_tavern`) boots a
//! headless dregg node and hosts a deos-js GM over real HTTP (each patron's `post`/`enter`/
//! `party_up` a genuine attributed turn on the node's one ledger); that path pulls the deos-host
//! (mozjs) + node + axum weight, so it stays OUT of this do-once render layer. This Offering is the
//! **render seam** for it: a light, gpui-free view of the board + presence + roster that every
//! frontend (web/discord/telegram/wechat) paints identically from a plain [`ViewNode`] tree, faithful
//! to the tavern's real slot layout (board post-count + per-patron lane, seat present-flag, party
//! roster).
//!
//! ## The surface story — DECIDED: a light presence-read that **links out**
//!
//! The tavern's real transport is heavy and async (a booted [`dreggnet_tavern`] node behind an
//! HTTP/mozjs host); the write verbs (`post`/`enter`/`party_up`) are genuine attributed turns on
//! that node's ledger, not synchronous surface moves. Rather than mint a *fake* synchronous post
//! path here (which would look playable but commit nothing real), this Offering commits to the
//! honest classification: it is a **read mirror** of the live board (presence + LFG + party) that
//! every frontend paints from one [`ViewNode`] tree, PLUS an explicit **link-out** — a
//! [`ViewNode::Button`] whose `join` verb the host resolves to the live hall (open the booted
//! node), so the do-once render still carries the actuation to *reach* the real transport. So:
//! `actions` is empty (nothing commits *here*), the render carries the join link-out, and `advance`
//! is a precise read-only refusal that points at the live node. NAMED NEXT (deliberately off this
//! light layer): an async host that binds the join button to a booted [`dreggnet_tavern`] session so
//! `post`/`enter`/`party_up` fire real node turns.

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::{pill, row, section, text};
use deos_view::ViewNode;

/// The link-out verb the render carries — the host resolves it to *opening the live tavern node*
/// (the async transport), not to a synchronous surface commit. `advance` of it here is refused.
pub const TURN_JOIN: &str = "join";

/// A patron at the tavern — a name, a live presence flag (seated / away), and their last LFG post.
struct Patron {
    name: String,
    present: bool,
    last_post: Option<String>,
}

/// One post on the LFG board — who posted it and the call.
struct Post {
    by: String,
    text: String,
}

/// **A tavern render session** — the shared board's state as a light in-memory view (the same
/// shape the live [`dreggnet_tavern`] node commits: presence seats, an LFG board, a party roster).
pub struct TavernSession {
    hall: String,
    patrons: Vec<Patron>,
    board: Vec<Post>,
    party: Vec<String>,
}

impl TavernSession {
    /// The number of patrons known to the tavern.
    pub fn patron_count(&self) -> usize {
        self.patrons.len()
    }
    /// How many patrons are currently present (seated).
    pub fn present_count(&self) -> usize {
        self.patrons.iter().filter(|p| p.present).count()
    }
    /// The number of posts on the LFG board.
    pub fn post_count(&self) -> usize {
        self.board.len()
    }
    /// The party roster size (how many patrons have partied up).
    pub fn party_size(&self) -> usize {
        self.party.len()
    }
    /// Whether the tavern is empty (no patrons).
    pub fn is_empty(&self) -> bool {
        self.patrons.is_empty()
    }
}

/// **The tavern offering** — a read-surface factory. [`demo`](Self::demo) seeds a lively hall;
/// [`new`](Self::new) opens an empty one.
pub struct TavernOffering {
    hall: String,
    populate: bool,
}

impl TavernOffering {
    /// An EMPTY tavern named `hall` (the empty-state surface).
    pub fn new(hall: impl Into<String>) -> Self {
        TavernOffering {
            hall: hall.into(),
            populate: false,
        }
    }

    /// A populated DEMO tavern — patrons present + away, an LFG board, and a party roster (the
    /// web/discord register state).
    pub fn demo(hall: impl Into<String>) -> Self {
        TavernOffering {
            hall: hall.into(),
            populate: true,
        }
    }
}

impl Offering for TavernOffering {
    type Session = TavernSession;

    fn open(&self, _cfg: SessionConfig) -> Result<TavernSession, OfferingError> {
        if !self.populate {
            return Ok(TavernSession {
                hall: self.hall.clone(),
                patrons: Vec::new(),
                board: Vec::new(),
                party: Vec::new(),
            });
        }
        let patrons = vec![
            Patron {
                name: "Aria".into(),
                present: true,
                last_post: Some("LFG the Salt Shore — need a healer".into()),
            },
            Patron {
                name: "Bram".into(),
                present: true,
                last_post: Some("selling a spare Ember Cloak, 2◈".into()),
            },
            Patron {
                name: "Cyra".into(),
                present: false,
                last_post: None,
            },
            Patron {
                name: "Dell".into(),
                present: true,
                last_post: None,
            },
        ];
        let board = vec![
            Post {
                by: "Aria".into(),
                text: "LFG the Salt Shore — need a healer".into(),
            },
            Post {
                by: "Bram".into(),
                text: "selling a spare Ember Cloak, 2◈".into(),
            },
        ];
        let party = vec!["Aria".to_string(), "Dell".to_string()];
        Ok(TavernSession {
            hall: self.hall.clone(),
            patrons,
            board,
            party,
        })
    }

    /// A read-surface exposes no moves.
    fn actions(&self, _s: &TavernSession) -> Vec<Action> {
        Vec::new()
    }

    /// Read-only: a post/enter/party-up is a real attributed turn on the LIVE tavern node (the
    /// named-next async path), not a synchronous surface move.
    fn advance(&self, _s: &mut TavernSession, _input: Action, _actor: DreggIdentity) -> Outcome {
        Outcome::Refused(
            "the tavern board is a read mirror — use the `join` link-out to open the live tavern \
             node, where post/enter/party-up fire real attributed turns"
                .into(),
        )
    }

    /// A render-surface: the board is consistent by construction (posts carry their author).
    fn verify(&self, s: &TavernSession) -> VerifyReport {
        for p in &s.board {
            if p.by.is_empty() {
                return VerifyReport::broken(s.board.len(), "a board post has no author");
            }
        }
        VerifyReport::ok(s.board.len())
    }

    fn render(&self, s: &TavernSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Tavern",
            "muted",
            vec![text(format!(
                "{} · {} patron(s) · {} present · {} post(s) · party of {}",
                s.hall,
                s.patron_count(),
                s.present_count(),
                s.post_count(),
                s.party_size(),
            ))],
        ));

        if s.is_empty() {
            children.push(section(
                "Presence",
                "muted",
                vec![text("The hall is empty — no patrons have entered yet.")],
            ));
        } else {
            // Presence — a Table of patrons with a live present/away pill + their last post.
            let mut rows: Vec<ViewNode> = vec![row(vec![
                text("Patron"),
                text("Presence"),
                text("Last post"),
            ])];
            for p in &s.patrons {
                let (word, tag) = if p.present {
                    ("present", "good")
                } else {
                    ("away", "muted")
                };
                rows.push(row(vec![
                    text(&p.name),
                    pill(word, tag),
                    text(p.last_post.clone().unwrap_or_else(|| "—".into())),
                ]));
            }
            children.push(section("Presence", "accent", vec![ViewNode::Table(rows)]));
        }

        // The LFG board — the posting board (a List of the calls).
        if s.board.is_empty() {
            children.push(section("LFG board", "muted", vec![text("No posts yet.")]));
        } else {
            let items: Vec<ViewNode> = s
                .board
                .iter()
                .map(|p| text(format!("{}: {}", p.by, p.text)))
                .collect();
            children.push(section("LFG board", "accent", vec![ViewNode::List(items)]));
        }

        // The party roster (party-up hook).
        if s.party.is_empty() {
            children.push(section("Party", "muted", vec![text("No party formed.")]));
        } else {
            let members: Vec<ViewNode> = s.party.iter().map(|m| pill(m, "accent")).collect();
            children.push(section("Party", "genuine", vec![row(members)]));
        }

        // The explicit LINK-OUT — the host resolves this button to opening the live tavern node
        // (the async transport), where post/enter/party-up are real attributed turns. It rides the
        // one ViewNode tree so every frontend surfaces the way to reach the real hall.
        children.push(section(
            "Join the live hall",
            "accent",
            vec![
                text("This board is a live mirror — enter the hall to post, seat, and party up."),
                ViewNode::Button {
                    label: format!("Enter {}", s.hall),
                    turn: TURN_JOIN.to_string(),
                    arg: 0,
                },
            ],
        ));

        Surface(section(format!("Tavern — {}", s.hall), "accent", children))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
