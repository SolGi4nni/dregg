//! **THE AGENT-ACTIVITY CARD** — the cockpit's ADOS agent-activity surface, reborn as a
//! deos-js card.
//!
//! An agent is an intricate LOOP — perceive, decide, act, repeat. dregg grounds the ONE seam
//! that matters: the agent's ACTIONS, at the tool-call/turn boundary, each a cap-gated,
//! receipted, conservation-checked verified turn. The cockpit's agent-activity surface (see
//! `starbridge-v2/src/agent.rs`) renders that grounded seam, but as hardcoded Rust gpui — you
//! cannot reshape it without a rebuild and the agent cannot rewrite it. This module makes the
//! agent-activity surface a **deos-js card** — a cell whose view is a *view-tree*
//! ([`crate::card_editor::ViewTree`], the `{kind, props, children}` shape [`deos-view`]
//! renders) generated from an agent cell's provable activity, read off the live ledger:
//!
//!   - **THE HELD MANDATE** — the agent's c-list (its attenuated reach): one labeled
//!     [`ViewTree::Text`] per capability edge (`→ <target> @<slot> · <rights>`, faceted /
//!     expiry annotated). This is "adoption IS attenuation" made legible: an agent is exactly
//!     as powerful as the mandate it holds — nothing ambient.
//!   - **THE CAP-GATED TURNS + RECEIPTS** — the agent's recent committed turns, each a
//!     [`ViewTree::Text`] (`@h<height> · <effect-kind> · receipt <hash>`), drawn from the
//!     card's own receipt tape (the executor's verdicts, never faked). A live
//!     [`ViewTree::Bind`] on [`AGENT_NONCE_SLOT`] shows the loop's on-ledger step count, so a
//!     new committed turn advances it in place.
//!
//! ## Editable from within
//!
//! Because the view is *data*, it is **editable from within**: [`AgentCard::edit_view`]
//! patches the card's OWN view-source — relabel the mandate section, append an action button
//! — as a *receipted patch* with *blame*. The activity UI reshapes live; the edit is an
//! accountable patch, not a recompile.
//!
//! ## The cap tooth is kept
//!
//! A view-edit (and the step-counter bump it leaves) is admitted only when `held` satisfies
//! the card's `edit_authority` ([`AgentCard::authorized`]) — the proven
//! [`dregg_cell::is_attenuation`] gate. An unauthorized reshape is refused in-band — no
//! patch, no receipt.

use dregg_cell::{AuthRequired, CellId, Ledger};
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;

use deos_reflect::short_hex;

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    BindProps, ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;
use dregg_cell::Requirement;

/// The model slot whose value is the agent's on-ledger step count (its nonce shadow) — the
/// [`ViewTree::Bind`] the renderer re-reads, advanced by a real `SetField` turn each time the
/// card observes a fresh committed turn. Disjoint from the inspector/feed/card-editor slots.
pub const AGENT_NONCE_SLOT: Slot = 13;

/// How many recent cap-gated turns the card renders as rows (most-recent-FIRST).
const DEFAULT_ACTIONS: usize = 12;

/// One held capability of an agent — a single edge of its mandate (the attenuated authority
/// the agent loop runs under). The gpui-free mirror of `starbridge-v2::agent::MandateEdge`,
/// read off a live [`dregg_cell::CapabilityRef`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MandateEdge {
    /// The cell this capability reaches (what the agent may act upon, short-rendered).
    pub target: String,
    /// The slot in the agent's c-list (its local handle to this authority).
    pub slot: u32,
    /// A short operator-legible label for the rights ("open"/"sig"/"proof"/…).
    pub rights: &'static str,
    /// Whether the capability is confined to a subset of effect types (a facet).
    pub faceted: bool,
    /// An optional expiry height (the cap is invalid beyond it), if any.
    pub expires_at: Option<u64>,
}

impl MandateEdge {
    /// The legible mandate-row line: `→ <target> @<slot> · <rights>` (faceted/expiry tagged).
    pub fn row_text(&self) -> String {
        let mut s = format!("→ {} @{} · {}", self.target, self.slot, self.rights);
        if self.faceted {
            s.push_str(" · faceted");
        }
        if let Some(h) = self.expires_at {
            s.push_str(&format!(" · expires@h{h}"));
        }
        s
    }
}

/// One recent cap-gated turn the agent committed — a row of the grounded seam (a single step
/// the agent actually performed, with its receipt). The gpui-free mirror of
/// `starbridge-v2::agent::AgentAction`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentAction {
    /// The local chain height of this turn (the agent's step index on-ledger).
    pub height: u64,
    /// The effect-kind label (what the turn did) — the human-meaningful kind of transition.
    pub effect_kind: String,
    /// The receipt hash (short-rendered) — the provenance-chain link.
    pub receipt: String,
}

impl AgentAction {
    /// Build an action from a height, an effect-kind label, and the raw receipt hash.
    pub fn new(height: u64, effect_kind: impl Into<String>, receipt: &[u8; 32]) -> Self {
        AgentAction {
            height,
            effect_kind: effect_kind.into(),
            receipt: short_hex(receipt),
        }
    }

    /// The legible action-row line: `@h<height> · <effect-kind> · receipt <hash>`.
    pub fn row_text(&self) -> String {
        format!(
            "@h{} · {} · receipt {}",
            self.height, self.effect_kind, self.receipt
        )
    }
}

/// **The agent-activity card** — a deos-js card whose view is a view-tree generated from an
/// agent cell's held mandate + recent cap-gated turns + receipts, rendered over a live World,
/// and editable from within (each edit a receipted patch with blame).
pub struct AgentCard {
    /// The card's substance — a cell on a live embedded verified World. A view-edit leaves a
    /// real `SetField` provenance turn on it; its own view-source is what edit-from-within
    /// rewrites.
    card: Applet,
    /// The agent's mandate (its c-list edges), read off the live ledger at open/observe time.
    mandate: Vec<MandateEdge>,
    /// The agent's recent cap-gated turns (most-recent-FIRST), grown by [`Self::observe`].
    actions: Vec<AgentAction>,
    /// The card's view-source AS A DOCUMENT (a patch-history). Regenerated as activity grows;
    /// every edit-from-within appends a patch, so [`Self::view_blame`] attributes each line.
    view: ProgramSource,
    /// The authority the card's driver holds (the cap a view-edit is checked against).
    held: AuthRequired,
    /// The authority a reshape on THIS card requires (`held` must satisfy it).
    edit_authority: Requirement,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

impl AgentCard {
    /// **Open the agent card** over a live substance cell, reading the agent's held mandate
    /// off `ledger` for cell `agent`. The initial view-tree is GENERATED from that mandate
    /// (and an empty action stream) and seeded as the card's editable `view_source` document.
    pub fn open(
        card: Applet,
        agent: CellId,
        ledger: &Ledger,
        author: Author,
        held: AuthRequired,
        edit_authority: Requirement,
    ) -> Self {
        let mandate = read_mandate(ledger, agent);
        let actions: Vec<AgentAction> = Vec::new();
        let initial = agent_view(&mandate, &actions).to_json();
        let view = ProgramSource::seed(author, &initial);
        AgentCard {
            card,
            mandate,
            actions,
            view,
            held,
            edit_authority,
            author,
        }
    }

    /// The card's substance cell (read-only).
    pub fn card(&self) -> &Applet {
        &self.card
    }

    /// Consume the card, yielding its substance [`Applet`] — the live cell a renderer drives
    /// (the `Bind` step-count row re-reads its model).
    pub fn into_card(self) -> Applet {
        self.card
    }

    /// The card's current view source (the document fold).
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The card's view-tree (the re-folded shape a renderer paints).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the card's view source — who authored each view line, in which patch.
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// The agent's held mandate (read-only) — the rows the mandate section renders.
    pub fn mandate(&self) -> &[MandateEdge] {
        &self.mandate
    }

    /// The agent's recent cap-gated turns (read-only, most-recent-FIRST).
    pub fn actions(&self) -> &[AgentAction] {
        &self.actions
    }

    /// The total reach of the mandate (how many distinct cells the agent can act upon).
    pub fn reach(&self) -> usize {
        let mut targets: Vec<&str> = self.mandate.iter().map(|m| m.target.as_str()).collect();
        targets.sort_unstable();
        targets.dedup();
        targets.len()
    }

    /// The live step count (the value the bound step-count row shows) — read off the ledger.
    pub fn live_steps(&self) -> u64 {
        self.card.get_u64(AGENT_NONCE_SLOT)
    }

    /// Whether the card is authorized to advance / reshape itself (the cap tooth).
    fn authorized(&self) -> bool {
        self.edit_authority.satisfied_by(&self.held)
    }

    /// Fire a real `SetField` turn setting the card's [`AGENT_NONCE_SLOT`] to the current
    /// committed-action count — the loop's on-ledger step count, advanced by a real verified
    /// turn (gated on `edit_authority`). Returns the receipt.
    fn bump_steps_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let steps = self.actions.len() as u64;
        self.card.register_affordance(Affordance {
            name: "__agent_steps__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(AGENT_NONCE_SLOT, pack_u64(steps))]),
        });
        self.card
            .fire("__agent_steps__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **OBSERVE A CAP-GATED TURN — the grounded seam grows.** Push `action` onto the
    /// activity stream (most-recent-FIRST), fire a real `SetField` turn advancing the bound
    /// step-count row, and re-derive the rows as a fresh patch on the view-source document.
    /// Refused in-band if `held` does not satisfy `edit_authority` (the cap tooth).
    pub fn observe(&mut self, action: AgentAction) -> Result<TurnReceipt, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        self.actions.insert(0, action);
        let receipt = self.bump_steps_turn()?;
        let fresh = agent_view(&self.mandate, &self.actions).to_json();
        self.view.edit(self.author, &fresh);
        Ok(receipt)
    }

    /// **EDIT THE VIEW FROM WITHIN.** Apply a structural reshape (relabel a section, append a
    /// button) to the card's OWN view-tree, append the result as a PATCH to the view-source
    /// document, and leave a provenance receipt on the card's chain. Refused in-band on an
    /// unauthorized reshape (the cap tooth) or a no-op.
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        let mut tree = self.view_tree()?;
        if !apply_patch(&patch, &mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();
        self.view.edit(self.author, &new_source);
        let receipt = self.bump_steps_turn()?;
        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }
}

/// Read the agent's held mandate off the live ledger — its c-list of [`MandateEdge`]s (the
/// attenuated reach). An agent not in the ledger has an empty mandate (an honest readout).
pub fn read_mandate(ledger: &Ledger, agent: CellId) -> Vec<MandateEdge> {
    ledger
        .get(&agent)
        .map(|cell| {
            cell.capabilities
                .iter()
                .map(|cap| MandateEdge {
                    target: short_hex(cap.target.as_bytes()),
                    slot: cap.slot,
                    rights: rights_label(&cap.permissions),
                    faceted: cap.allowed_effects.is_some(),
                    expires_at: cap.expires_at,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// **Generate the agent-activity view-tree** from a held mandate + a recent-turn stream: a
/// title, the HELD MANDATE section (a row per cap edge), a live-bound step-count row, and the
/// CAP-GATED TURNS section (a row per recent action, most-recent-FIRST). Pure, so the rows
/// are `cargo test`-able without a World.
pub fn agent_view(mandate: &[MandateEdge], actions: &[AgentAction]) -> ViewTree {
    let mut children: Vec<ViewTree> = Vec::new();

    // Title.
    children.push(ViewTree::Text {
        props: TextProps {
            text: "Agent Activity".into(),
        },
    });

    // ── THE HELD MANDATE ────────────────────────────────────────────────────────────────
    let mut mandate_rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "Held Mandate".into(),
        },
    }];
    if mandate.is_empty() {
        mandate_rows.push(ViewTree::Text {
            props: TextProps {
                text: "(holds no outbound capability — confined to itself)".into(),
            },
        });
    } else {
        for edge in mandate {
            mandate_rows.push(ViewTree::Text {
                props: TextProps {
                    text: edge.row_text(),
                },
            });
        }
    }
    children.push(ViewTree::VStack {
        children: mandate_rows,
    });

    // The live step count — a `Bind` the renderer re-reads off AGENT_NONCE_SLOT, advanced by
    // a real turn each time a fresh committed turn is observed.
    children.push(ViewTree::Bind {
        props: BindProps {
            slot: AGENT_NONCE_SLOT,
            label: "steps committed: ".into(),
        },
    });

    // ── THE CAP-GATED TURNS + RECEIPTS ──────────────────────────────────────────────────
    let n = actions.len().min(DEFAULT_ACTIONS);
    let mut action_rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "Cap-Gated Turns".into(),
        },
    }];
    if actions.is_empty() {
        action_rows.push(ViewTree::Text {
            props: TextProps {
                text: "(no committed turns observed yet)".into(),
            },
        });
    } else {
        for action in &actions[..n] {
            action_rows.push(ViewTree::Text {
                props: TextProps {
                    text: action.row_text(),
                },
            });
        }
    }
    children.push(ViewTree::VStack {
        children: action_rows,
    });

    ViewTree::VStack { children }
}

/// A short operator-legible label for an `AuthRequired` rights value (mirrors
/// `starbridge-v2::agent::rights_label`).
fn rights_label(r: &AuthRequired) -> &'static str {
    match r {
        AuthRequired::None => "open",
        AuthRequired::Signature => "sig",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "sig|proof",
        AuthRequired::Impossible => "locked",
        AuthRequired::Custom { .. } => "custom",
    }
}

/// Apply a [`ViewPatch`] reshape to a view-tree (append a button/text to the root, or relabel
/// the first matching text). Mirrors the inspector card's apply.
fn apply_patch(patch: &ViewPatch, tree: &mut ViewTree) -> bool {
    match patch {
        ViewPatch::AddButton { label, turn, arg } => push_child(
            tree,
            ViewTree::Button {
                props: ButtonProps {
                    label: label.clone(),
                    on_click: OnClick {
                        turn: turn.clone(),
                        arg: *arg,
                    },
                },
            },
        ),
        ViewPatch::AddText { text } => push_child(
            tree,
            ViewTree::Text {
                props: TextProps { text: text.clone() },
            },
        ),
        ViewPatch::AddBind { slot, label } => push_child(
            tree,
            ViewTree::Bind {
                props: crate::card_editor::BindProps {
                    slot: *slot,
                    label: label.clone(),
                },
            },
        ),
        ViewPatch::Relabel { from, to } => relabel_text(tree, from, to),
    }
}

fn push_child(tree: &mut ViewTree, node: ViewTree) -> bool {
    match tree {
        ViewTree::VStack { children } | ViewTree::Row { children } => {
            children.push(node);
            true
        }
        _ => false,
    }
}

fn relabel_text(tree: &mut ViewTree, from: &str, to: &str) -> bool {
    if let ViewTree::Text { props } = tree {
        if props.text == from {
            props.text = to.to_string();
            return true;
        }
    }
    match tree {
        ViewTree::VStack { children } | ViewTree::Row { children } => {
            for c in children.iter_mut() {
                if relabel_text(c, from, to) {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}
