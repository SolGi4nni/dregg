//! **The `SurfaceBackend` trait** — the one seat every renderer of the [`ViewNode`] IR shares.
//!
//! A backend takes the SAME (mount-resolved, disclosed) view-tree + its live bind values and
//! projects it onto its channel's output ([`render`](SurfaceBackend::render) → an HTML string, a
//! Discord card, Telegram text, …), and it [`decode`](SurfaceBackend::decode)s an actuation id
//! that channel carried back into the `{turn, arg}` affordance to fire. Decoding is the ONE
//! [`crate::affordance`] codec, selected by the backend's [`transport`](SurfaceBackend::transport)
//! — so every backend round-trips its own encoded affordances by construction.
//!
//! This is the extraction of the previously ad-hoc render functions (`web::render_html`,
//! `discord::render_card`, the moved-in web-form + Telegram-text walkers) behind one trait; the
//! frontend crates (`dreggnet-web`, `dreggnet-telegram`) render through the deos-view backends
//! instead of maintaining their own subset walkers.

use crate::affordance::{parse_affordance_id, AffordanceTransport};
use crate::tree::ViewNode;

/// A projection of the one [`ViewNode`] IR onto a concrete surface channel (web / Discord /
/// Telegram / …). One `render` from the tree + binds; one `decode` back from an actuation id via
/// the shared affordance codec.
pub trait SurfaceBackend {
    /// The rendered output of this channel — an HTML `String`, a `DiscordCard`, Telegram text, …
    type Rendered;

    /// The channel this backend carries affordances on — selects the [`crate::affordance`] codec
    /// used by the default [`decode`](Self::decode).
    fn transport(&self) -> AffordanceTransport;

    /// Render `tree` (already mount-resolved + disclosed) with its live `binds` (tree-walk order;
    /// a channel with no live binds, e.g. Telegram text, ignores them) into this channel's output.
    fn render(&self, tree: &ViewNode, binds: &[u64]) -> Self::Rendered;

    /// Decode an actuation id this channel carried back into the `{turn, arg}` affordance to fire.
    /// The default routes through the ONE [`crate::affordance`] codec for this backend's
    /// [`transport`](Self::transport); `None` for an id this transport never minted.
    fn decode(&self, id: &str) -> Option<(String, i64)> {
        parse_affordance_id(id, self.transport())
    }
}

/// **One fireable affordance found in a rendered tree** — a `{turn, arg}` with the label the
/// channel shows and the `enabled` bit the surface's gate computed for THIS viewer.
///
/// A chat channel does not put its affordances in the prose: Telegram builds an inline keyboard,
/// WeChat a 1.-indexed numbered reply list. Both need the SAME thing — the tree's actuations in
/// walk order, each with its enabled verdict. That list is [`actuations`]; the enabled bit is
/// whatever the render pipeline ([`crate::pipeline`], the FOUR-conjunct gate) already stamped on
/// the node, so a channel never re-derives (or re-guesses) authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Actuation {
    /// The affordance name the press fires (the `turn`).
    pub turn: String,
    /// The argument the press carries.
    pub arg: i64,
    /// The label/glyph the channel shows for it.
    pub label: String,
    /// May it fire, for this viewer, right now? A `false` is the cap tooth SHOWN, not hidden — the
    /// channel dims/locks the entry rather than dropping it (`enabled` is the render-time verdict,
    /// never a substitute for the executor's own gate on fire).
    pub enabled: bool,
}

/// **Collect a tree's fireable actuations in walk order** — the affordance half every non-DOM
/// channel carries OUT of the prose (Telegram's keyboard, WeChat's numbered list).
///
/// Covers every [`ViewNode`] variant carrying a definite `{turn, arg}`: [`ViewNode::Button`],
/// [`ViewNode::Menu`] rows, [`ViewNode::Halo`] handles, clickable [`ViewNode::Breadcrumb`] crumbs
/// (non-empty `turn`), and [`ViewNode::Tabs`] (one per tab label, `arg` = the tab index); all
/// containers recurse (including a [`ViewNode::Host`]'s mounted subtree and an unfiltered
/// [`ViewNode::Adept`] wrapper), so nothing nested is dropped.
///
/// [`ViewNode::Slider`] and [`ViewNode::Toggle`] are deliberately NOT here: their `arg`/`turn` is
/// VALUE-dependent (the drag's chosen value; the on/off turn chosen by the live slot), so they are
/// not a fixed press — a numbered reply or a keyboard button cannot express them, and inventing an
/// `arg` for them would be a lie. Those stay renderer-side (the DOM/native controls that can read
/// the live value).
///
/// `enabled` is read OFF THE NODE — the nodes that carry a bit ([`crate::tree::MenuItem`],
/// [`crate::tree::HaloHandle`]) give theirs (the pipeline's gate verdict); the nodes that carry
/// none (Button/Breadcrumb/Tabs — the IR has no `enabled` field on them) default to `true`. Pass the
/// gate oracle to [`actuations_with`] to give THOSE a live verdict too.
pub fn actuations(tree: &ViewNode) -> Vec<Actuation> {
    actuations_with(tree, &|_| None)
}

/// [`actuations`], with an `enabled_for(turn)` oracle consulted for EVERY actuation — including the
/// nodes the IR gives no `enabled` field (`Button`/`Breadcrumb`/`Tabs`).
///
/// This is how a channel closes the IR's gap without a breaking ViewNode change: the gate verdict is
/// applied at the TRANSPORT boundary (the keyboard/numbered list the channel actually mints), so a
/// cap-refused or out-of-window `Button` rides as a LOCKED entry rather than a live one. `None` from
/// the oracle (an affordance the surface does not govern) keeps the node's own bit.
pub fn actuations_with<F>(tree: &ViewNode, enabled_for: &F) -> Vec<Actuation>
where
    F: Fn(&str) -> Option<bool>,
{
    let mut out = Vec::new();
    walk(tree, &|t| enabled_for(t), &mut out);
    out
}

fn walk(node: &ViewNode, enabled_for: &dyn Fn(&str) -> Option<bool>, out: &mut Vec<Actuation>) {
    let push = |out: &mut Vec<Actuation>, turn: &str, arg: i64, label: &str, authored: bool| {
        out.push(Actuation {
            turn: turn.to_string(),
            arg,
            label: label.to_string(),
            enabled: enabled_for(turn).unwrap_or(authored),
        });
    };
    let kids = |cs: &[ViewNode], out: &mut Vec<Actuation>| {
        for c in cs {
            walk(c, enabled_for, out);
        }
    };
    match node {
        ViewNode::Button { label, turn, arg } => push(out, turn, *arg, label, true),
        ViewNode::Menu { items } => {
            for it in items {
                push(out, &it.turn, it.arg, &it.label, it.enabled);
            }
        }
        ViewNode::Halo { handles, .. } => {
            for h in handles {
                push(out, &h.turn, h.arg, &h.glyph, h.enabled);
            }
        }
        ViewNode::Breadcrumb { items } => {
            for c in items {
                if !c.turn.is_empty() {
                    push(out, &c.turn, c.arg, &c.label, true);
                }
            }
        }
        ViewNode::Tabs {
            tabs,
            select_turn,
            panels,
            ..
        } => {
            if !select_turn.is_empty() {
                for (i, label) in tabs.iter().enumerate() {
                    push(out, select_turn, i as i64, label, true);
                }
            }
            kids(panels, out);
        }
        ViewNode::VStack(cs)
        | ViewNode::Row(cs)
        | ViewNode::List(cs)
        | ViewNode::Table(cs)
        | ViewNode::Section { children: cs, .. }
        | ViewNode::Grid { children: cs, .. } => kids(cs, out),
        ViewNode::Host { view: Some(v), .. } => walk(v, enabled_for, out),
        ViewNode::Adept(inner) => walk(inner, enabled_for, out),
        // A coordinate board: each CLICKABLE cell (non-empty `turn`) is one fixed `{turn, arg}`
        // press — the glyph is its label — so a board square reaches the numbered/keyboard carrier.
        ViewNode::CoordGrid { cells, .. } => {
            for cell in cells {
                if !cell.turn.is_empty() {
                    push(out, &cell.turn, cell.arg, &cell.glyph, true);
                }
            }
        }
        // Leaves (and the value-dependent Slider/Toggle — see the doc above) carry no fixed press.
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::{Crumb, HaloHandle, MenuItem};

    /// The collector reaches EVERY `{turn, arg}` carrier, through every container — including a
    /// hosted subtree and an (undisclosed-away) Adept wrapper — and reads each node's own
    /// `enabled` bit.
    #[test]
    fn collects_every_actuation_through_every_container() {
        let tree = ViewNode::VStack(vec![
            ViewNode::Button {
                label: "Inc".into(),
                turn: "inc".into(),
                arg: 1,
            },
            ViewNode::Section {
                title: "Acts".into(),
                tag: String::new(),
                children: vec![ViewNode::Menu {
                    items: vec![
                        MenuItem {
                            label: "Vote".into(),
                            turn: "vote".into(),
                            arg: 1,
                            enabled: true,
                        },
                        MenuItem {
                            label: "Pass".into(),
                            turn: "pass".into(),
                            arg: 0,
                            enabled: false,
                        },
                    ],
                }],
            },
            ViewNode::Host {
                cell: "ab".into(),
                view: Some(Box::new(ViewNode::Halo {
                    target_slot: 0,
                    handles: vec![HaloHandle {
                        glyph: "✂".into(),
                        turn: "cut".into(),
                        arg: 3,
                        enabled: true,
                    }],
                })),
            },
            ViewNode::Breadcrumb {
                items: vec![
                    Crumb {
                        label: "root".into(),
                        turn: "nav".into(),
                        arg: 0,
                    },
                    Crumb {
                        label: "here".into(),
                        turn: String::new(),
                        arg: 0,
                    },
                ],
            },
            ViewNode::Adept(Box::new(ViewNode::Tabs {
                tabs: vec!["A".into(), "B".into()],
                selected_slot: 4,
                select_turn: "tab".into(),
                panels: vec![ViewNode::Divider, ViewNode::Divider],
            })),
            // Value-dependent: NOT a fixed press (no lie about its arg).
            ViewNode::Slider {
                slot: 0,
                min: 0,
                max: 9,
                turn: "seek".into(),
            },
        ]);

        let got: Vec<(String, i64, bool)> = actuations(&tree)
            .into_iter()
            .map(|a| (a.turn, a.arg, a.enabled))
            .collect();
        assert_eq!(
            got,
            vec![
                ("inc".to_string(), 1, true),
                ("vote".to_string(), 1, true),
                ("pass".to_string(), 0, false), // the node's own (authored/gated) bit
                ("cut".to_string(), 3, true),   // inside a HOSTED subtree
                ("nav".to_string(), 0, true),   // the clickable crumb only
                ("tab".to_string(), 0, true),   // one per tab label, arg = index
                ("tab".to_string(), 1, true),
            ],
            "every fixed {{turn, arg}} carrier, in walk order; the value-dependent slider is not one"
        );
    }

    /// The oracle reaches the nodes the IR gives NO `enabled` field (`Button`/`Tabs`/`Breadcrumb`) —
    /// so a refused affordance rides the channel LOCKED instead of live, with no ViewNode change.
    #[test]
    fn the_oracle_gates_the_nodes_that_carry_no_enabled_field() {
        let tree = ViewNode::Row(vec![
            ViewNode::Button {
                label: "Vote".into(),
                turn: "vote".into(),
                arg: 1,
            },
            ViewNode::Button {
                label: "Look".into(),
                turn: "look".into(),
                arg: 0,
            },
        ]);
        let refused = |t: &str| (t == "vote").then_some(false); // the gate darkens `vote`
        let got: Vec<(String, bool)> = actuations_with(&tree, &refused)
            .into_iter()
            .map(|a| (a.turn, a.enabled))
            .collect();
        assert_eq!(
            got,
            vec![("vote".to_string(), false), ("look".to_string(), true)],
            "the gated Button is LOCKED (shown, not hidden); an ungoverned one stays live"
        );
    }
}
