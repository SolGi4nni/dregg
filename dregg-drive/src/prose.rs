//! **The PROSE surface, driven — and the projection census.**
//!
//! This surface is `deos_view::text::render_text` over the offering's own `render_for`. It is not
//! a stand-in for a chat surface: it is *the same function* — `deos_view::TelegramBackend::render`
//! is `render_text`, and WeChat's message body is the same walk. So whatever a `ViewNode` variant
//! fails to say here, it fails to say on every chat channel simultaneously.
//!
//! ## Why this surface earns its place beside the two routed ones
//!
//! Telegram and web hand the driver *rendered output*, which is the right thing to judge a UX by
//! and the wrong thing to find a PROJECTION HOLE with: if a variant projects to nothing, the
//! absence looks exactly like the node not being there. Here the driver holds the tree AND the
//! projection, so it can say **"the surface contains 4 nodes this channel drops"** and name them.
//! That is the class the `ViewNode::Pill` hole belonged to — a phase badge the board carried and
//! chat readers never saw.
//!
//! The census is not a re-derivation of the projection. It reads the tree, and reports which
//! variants the prose walk is *documented and observed* to omit; the prose body printed beside it
//! is the real `render_text` output, so the two disagreeing is itself visible.

use std::collections::BTreeMap;
use std::path::PathBuf;

use deos_view::ViewNode;
use dreggnet_offerings::{Action, DreggIdentity, OfferingHost, SessionId};
use dreggnet_web::{demo_host_resumed_from, web_identity};

use crate::out::{Control, Frame, Paint, PaintHow, pills_in_text};
use crate::surface::DrivenSurface;

/// The driven prose surface.
pub struct ProseDriver {
    dir: PathBuf,
    key: String,
    session: SessionId,
    viewer: String,
    host: Option<OfferingHost>,
    current: Vec<Control>,
    previous: Vec<Control>,
    restarts: usize,
}

impl ProseDriver {
    /// Build the driver over a durable state directory.
    pub fn new(dir: PathBuf, key: &str, session: &str, viewer: &str) -> Result<Self, String> {
        std::fs::create_dir_all(dir.join("sessions"))
            .map_err(|e| format!("cannot create {}: {e}", dir.join("sessions").display()))?;
        Ok(ProseDriver {
            host: Some(demo_host_resumed_from(dir.join("sessions"))),
            dir,
            key: key.to_string(),
            session: SessionId::new(session),
            viewer: viewer.to_string(),
            current: Vec::new(),
            previous: Vec::new(),
            restarts: 0,
        })
    }

    fn host(&mut self) -> &mut OfferingHost {
        self.host
            .as_mut()
            .expect("the host is only absent mid-restart")
    }

    fn identity(&self) -> DreggIdentity {
        // The SAME derivation the web surface uses, so `--as alice` is one actor across both.
        web_identity(&self.viewer)
    }

    /// Render the current state: the prose the channel would send, the affordances it would carry
    /// beside it, and the census of what the projection dropped.
    fn look(&mut self, verb: &str) -> Frame {
        let mut frame = Frame::new(verb);
        let key = self.key.clone();
        let sid = self.session.clone();
        let viewer = self.identity();

        let Some(surface) = self.host().render_for(&key, &sid, &viewer) else {
            frame.note(format!(
                "no live session for `{key}` under `{}` — run `open` first (or the key is not \
                 registered on this host).",
                sid.0
            ));
            frame.flag_silence();
            return frame;
        };
        let tree = surface.view().clone();
        let prose = deos_view::text::render_text(&tree);
        frame.paints.push(Paint {
            how: PaintHow::Read(format!("prose projection of `{key}` for {}", self.viewer)),
            body: prose.clone(),
        });
        frame.pills = pills_in_text(&prose);

        // The affordance half. A chat channel carries these BESIDE the prose (a keyboard, a
        // component row), which is why `Menu`/`Button` are absent from the text on purpose.
        let actions = self
            .host()
            .actions_for(&key, &sid, &viewer)
            .unwrap_or_default();
        frame.controls = actions
            .iter()
            .enumerate()
            .map(|(index, a)| Control {
                index,
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
                wire: format!("{}:{}", a.turn, a.arg),
            })
            .collect();
        if actions.iter().any(|a| a.wants_text) {
            frame.note(
                "at least one affordance SOLICITS free text (`wants_text`). Telegram arms its \
                 text slot and routes the next message into it; the web surface now renders a \
                 real text field beside the button and POSTs what was typed (`name=\"text\"`). \
                 WeChat's numbered reply and Discord's buttons still carry a FIXED press only, so \
                 on those two the affordance can be pressed and can only be refused.",
            );
        }

        // ⚑ THE UNCHECKED SEAM: an offering declares its affordances TWICE — once as
        // `actions_for()` (what a chat surface paints as buttons, via `build_present_request`) and
        // once as the `Menu`/`CoordGrid`/`Button` nodes INSIDE `render_for()`'s tree (what the web
        // renderer walks, and what `deos_view::actuations` is the canonical carrier of). Nothing
        // holds the two in step: `two_web_routes_agree` compares web to web, and
        // `cross_surface_affordance_differential` compares every surface to `actuations(tree)` —
        // so a divergence between `actions()` and the TREE is invisible to both. Measure it.
        let carried = deos_view::actuations(&tree);
        if carried.len() != actions.len() {
            frame.note(format!(
                "⚠ ACTION/TREE DISAGREEMENT: `actions_for()` advertises {} affordance(s) but the \
                 rendered tree carries {} (`deos_view::actuations`). A chat surface paints the \
                 first set, the web renderer walks the second — so the two surfaces offer \
                 different moves for the SAME state, and nothing checks that they agree.",
                actions.len(),
                carried.len()
            ));
        }
        let action_labels: std::collections::BTreeSet<&str> =
            actions.iter().map(|a| a.label.as_str()).collect();
        let tree_labels: std::collections::BTreeSet<&str> =
            carried.iter().map(|a| a.label.as_str()).collect();
        let shared = action_labels.intersection(&tree_labels).count();
        if shared == 0 && !action_labels.is_empty() && !tree_labels.is_empty() {
            frame.note(format!(
                "⚠ LABEL DIVERGENCE: not ONE of the {} action labels appears among the {} tree \
                 labels. The same move is spoken differently on a chat surface and on the web — \
                 e.g. action “{}” vs tree “{}”.",
                action_labels.len(),
                tree_labels.len(),
                action_labels.iter().next().unwrap_or(&""),
                tree_labels.iter().next().unwrap_or(&""),
            ));
        }

        // The census — and the disagreement between what the tree carries and what prose says.
        let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut slot_pills = 0usize;
        census(&tree, &mut counts, &mut slot_pills);
        let dropped: Vec<String> = SILENT_IN_PROSE
            .iter()
            .filter_map(|name| counts.get(name).map(|n| format!("{name}×{n}")))
            .collect();
        let inventory: Vec<String> = counts.iter().map(|(k, v)| format!("{k}×{v}")).collect();
        frame.note(format!("tree: {}", inventory.join(" ")));
        if !dropped.is_empty() {
            frame.note(format!(
                "⚠ DROPPED BY THE PROSE PROJECTION: {}. Every chat channel shares this walk, so \
                 no chat reader learns what these nodes say.",
                dropped.join(" ")
            ));
        }
        if slot_pills > 0 {
            frame.note(format!(
                "⚠ {slot_pills} SLOT-BOUND Pill node(s): the prose walk prints nothing for them \
                 (it has no ledger to resolve the case against), while the web renderer prints \
                 the static `text` fallback. The two channels disagree about the phase word.",
            ));
        }
        if let Some(report) = self.host().verify(&key, &sid) {
            frame.note(format!(
                "chain: verified={} turns={}",
                report.verified, report.turns
            ));
        }
        self.previous = std::mem::replace(&mut self.current, frame.controls.clone());
        frame.flag_silence();
        frame
    }

    fn fire(&mut self, verb: &str, from: &[Control], index: usize) -> Frame {
        let Some(control) = from.get(index).cloned() else {
            return Frame::driver_note(
                verb,
                format!("no control at index {index} — {} on offer.", from.len()),
            );
        };
        self.advance(verb, &control.turn, control.arg, &control.label)
    }

    fn advance(&mut self, verb: &str, turn: &str, arg: i64, label: &str) -> Frame {
        let key = self.key.clone();
        let sid = self.session.clone();
        let viewer = self.identity();
        let action = Action::new(label, turn, arg, true);
        let outcome = self.host().advance(&key, &sid, action, viewer);
        let mut frame = self.look(verb);
        frame.reply = Some(match &outcome {
            Some(dreggnet_offerings::Outcome::Landed { receipt, ended }) => format!(
                "LANDED — turn_hash {}… {}",
                receipt
                    .turn_hash
                    .iter()
                    .take(6)
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>(),
                if *ended { "(session ENDED)" } else { "" }
            ),
            Some(dreggnet_offerings::Outcome::Refused(why)) => format!("REFUSED — {why}"),
            None => "NO SUCH SESSION — the host has nothing open under this key/id.".to_string(),
        });
        frame.note(format!("advanced {turn}/{arg} — “{label}”"));
        frame
    }
}

/// The `ViewNode` variants the prose walk is observed to print nothing for. Kept as a LIST OF
/// NAMES rather than a re-implementation of the walk: this crate must not become a second
/// projection, or its findings would be about itself.
const SILENT_IN_PROSE: [&str; 10] = [
    "Bind",
    "Input",
    "Gauge",
    "Divider",
    "Breadcrumb",
    "Icon",
    "Halo",
    "Slider",
    "Toggle",
    "Tile",
];

/// Count every node by variant; count slot-bound pills separately.
fn census(node: &ViewNode, out: &mut BTreeMap<&'static str, usize>, slot_pills: &mut usize) {
    let name = match node {
        ViewNode::VStack(_) => "VStack",
        ViewNode::Row(_) => "Row",
        ViewNode::Text(_) => "Text",
        ViewNode::Bind { .. } => "Bind",
        ViewNode::Button { .. } => "Button",
        ViewNode::Input { .. } => "Input",
        ViewNode::List(_) => "List",
        ViewNode::Table(_) => "Table",
        ViewNode::Section { .. } => "Section",
        ViewNode::Tabs { .. } => "Tabs",
        ViewNode::Gauge { .. } => "Gauge",
        ViewNode::Divider => "Divider",
        ViewNode::Host { .. } => "Host",
        ViewNode::Grid { .. } => "Grid",
        ViewNode::Breadcrumb { .. } => "Breadcrumb",
        ViewNode::Progress { .. } => "Progress",
        ViewNode::Pill { slot, .. } => {
            if slot.is_some() {
                *slot_pills += 1;
            }
            "Pill"
        }
        ViewNode::Icon { .. } => "Icon",
        ViewNode::Menu { .. } => "Menu",
        ViewNode::Halo { .. } => "Halo",
        ViewNode::Slider { .. } => "Slider",
        ViewNode::Toggle { .. } => "Toggle",
        ViewNode::Tile { .. } => "Tile",
        ViewNode::CoordGrid { .. } => "CoordGrid",
        ViewNode::Adept(_) => "Adept",
    };
    *out.entry(name).or_default() += 1;
    for child in children(node) {
        census(child, out, slot_pills);
    }
}

fn children(node: &ViewNode) -> Vec<&ViewNode> {
    match node {
        ViewNode::VStack(cs)
        | ViewNode::Row(cs)
        | ViewNode::List(cs)
        | ViewNode::Table(cs)
        | ViewNode::Section { children: cs, .. }
        | ViewNode::Grid { children: cs, .. }
        | ViewNode::Tabs { panels: cs, .. } => cs.iter().collect(),
        ViewNode::Host { view: Some(v), .. } => vec![v.as_ref()],
        ViewNode::Adept(v) => vec![v.as_ref()],
        _ => Vec::new(),
    }
}

impl DrivenSurface for ProseDriver {
    fn provenance(&self) -> String {
        format!(
            "prose — REAL, and NOT a stand-in. `deos_view::text::render_text` over the offering's \
             own `render_for`/`actions_for` on a real `OfferingHost` \
             (`demo_host_resumed_from({store})`). This IS the function \
             `deos_view::TelegramBackend::render` calls, so a hole found here is a hole on every \
             chat channel. NOT covered: routing (no `/commands`, no keyboard) — that is what \
             `--surface telegram` is for.",
            store = self.dir.join("sessions").display()
        )
    }

    fn open(&mut self) -> Frame {
        let key = self.key.clone();
        let sid = self.session.clone();
        match self.host().ensure_open(&key, &sid) {
            Ok(fresh) => {
                let mut frame = self.look("open");
                frame.note(if fresh {
                    "opened a FRESH session".to_string()
                } else {
                    "joined an EXISTING session (already live, or lazily resumed from the store)"
                        .to_string()
                });
                frame
            }
            Err(why) => Frame::driver_note("open", format!("the host refused to open: {why}")),
        }
    }

    fn again(&mut self) -> Frame {
        self.look("again")
    }

    fn press(&mut self, index: usize) -> Frame {
        let from = self.current.clone();
        self.fire("press", &from, index)
    }

    fn press_stale(&mut self, index: usize) -> Frame {
        let from = self.previous.clone();
        if from.is_empty() {
            return Frame::driver_note("stale", "no previous frame to press from yet.");
        }
        let mut frame = self.fire("stale", &from, index);
        frame.note("this was a control from the PREVIOUS frame.");
        frame
    }

    fn act(&mut self, turn: &str, arg: i64) -> Frame {
        self.advance("act", turn, arg, "(raw)")
    }

    fn send(&mut self, text: &str) -> Frame {
        Frame::driver_note(
            "send",
            format!(
                "the prose surface is a PROJECTION, not a router: `{text}` has nowhere to go. Use \
                 `--surface telegram` for the command surface."
            ),
        )
    }

    fn become_viewer(&mut self, who: &str) -> Frame {
        let was = std::mem::replace(&mut self.viewer, who.to_string());
        let mut frame = Frame::new("as");
        frame.controls = self.current.clone();
        let id = self.identity().0;
        frame.note(format!(
            "viewer {was} → {who} (identity {}…). NO state was touched.",
            &id[..id.len().min(16)]
        ));
        frame
    }

    fn restart(&mut self) -> Frame {
        self.host = None;
        self.host = Some(demo_host_resumed_from(self.dir.join("sessions")));
        self.restarts += 1;
        let mut frame = Frame::new("restart");
        frame.controls = self.current.clone();
        frame.note(format!(
            "RESTART #{n}: the host was dropped and rebuilt from {store}, replaying every \
             persisted move-log on boot.",
            n = self.restarts,
            store = self.dir.join("sessions").display()
        ));
        frame
    }

    fn verify(&mut self) -> Frame {
        let key = self.key.clone();
        let sid = self.session.clone();
        let report = self.host().verify(&key, &sid);
        let mut frame = Frame::new("verify");
        frame.controls = self.current.clone();
        frame.reply = Some(match report {
            Some(r) => format!("verified={} turns={} — {}", r.verified, r.turns, r.detail),
            None => "no live session under this key/id.".to_string(),
        });
        frame
    }

    fn controls(&self) -> Vec<Control> {
        self.current.clone()
    }

    fn viewer(&self) -> String {
        self.viewer.clone()
    }
}
