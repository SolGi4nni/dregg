//! **THE SURFACE→CARD BRIDGE** — `deos_reflect::Presentation → ViewNode`, so
//! "liberate any surface into a card" is ONE lossless path.
//!
//! `docs/SURFACE-ONE-GATE-FOUR-PLANES.md` move #5: retire the parallel moldable
//! projection. `deos-reflect` builds the moldable faces (RawFields · Graph ·
//! DomainVisual · Provenance) as its OWN pure-data payloads
//! ([`deos_reflect::PresentationBody`]); this module lowers each into the ONE
//! [`ViewNode`] IR the four backends (native gpui / web HTML / Discord / Telegram)
//! already walk — instead of a second renderer per face. Every datum in a face is
//! carried across (lossless: every field key+value, every graph node/edge, every
//! state/transition, every timeline event becomes a node in the tree).
//!
//! The lowering is a PURE function (no gpui, no ledger): a [`deos_reflect::Presentation`]
//! becomes a titled [`ViewNode::Section`] (title = the face label, `tag` = the face's
//! stable slug) whose children are the lowered body. A whole face-set lowers to a
//! [`ViewNode::VStack`] of such sections — the "cell as a stack of moldable cards".

use crate::tree::{PillCase, ViewNode};
use deos_reflect::present::{GraphView, SmState, SmTransition, TimelineEvent};
use deos_reflect::substance::short_hex;
use deos_reflect::{
    Field, FieldValue, Inspectable, Presentation, PresentationBody, StateMachineView, TimelineView,
};

/// Lower a moldable [`Presentation`] into the [`ViewNode`] IR — a titled section whose
/// `tag` is the face's stable slug and whose children carry every datum of the face.
pub fn presentation_to_view(p: &Presentation) -> ViewNode {
    ViewNode::Section {
        title: p.label.clone(),
        tag: p.kind.slug().to_string(),
        children: body_to_children(&p.body),
    }
}

/// Lower a WHOLE face-set (e.g. [`deos_reflect::ReflectedCell::present`]) into one
/// stacked card — the cell as a column of moldable sections.
pub fn presentations_to_view(faces: &[Presentation]) -> ViewNode {
    ViewNode::VStack(faces.iter().map(presentation_to_view).collect())
}

/// The children of a face's section — one lowering per [`PresentationBody`] variant.
fn body_to_children(body: &PresentationBody) -> Vec<ViewNode> {
    match body {
        PresentationBody::Fields(insp) => fields_children(insp),
        PresentationBody::Graph(g) => graph_children(g),
        PresentationBody::StateMachine(sm) => state_machine_children(sm),
        PresentationBody::Timeline(tl) => timeline_children(tl),
    }
}

/// **RawFields** → a summary line + one `key: value` row per field (lossless: every
/// field key and rendered value is a node).
fn fields_children(insp: &Inspectable) -> Vec<ViewNode> {
    let mut out = Vec::with_capacity(insp.fields.len() + 1);
    out.push(ViewNode::Text(format!(
        "{} — {}",
        insp.title, insp.subtitle
    )));
    for f in &insp.fields {
        out.push(field_row(f));
    }
    out
}

/// One field → a `key: value` row (a `Row` of two `Text`s so a backend can style the
/// key + value distinctly, exactly like the native inspector's key/value pair).
fn field_row(f: &Field) -> ViewNode {
    ViewNode::Row(vec![
        ViewNode::Text(format!("{}:", f.key)),
        ViewNode::Text(render_field_value(&f.value)),
    ])
}

/// Render a typed [`FieldValue`] to a stable string — the SAME readouts the native
/// inspector + the wasm card use (ids/hashes abbreviated; a committed slot shows its
/// redaction, never a value).
fn render_field_value(v: &FieldValue) -> String {
    match v {
        FieldValue::Text(s) => s.clone(),
        FieldValue::Balance(b) => b.to_string(),
        FieldValue::Count(n) => n.to_string(),
        FieldValue::Bool(b) => b.to_string(),
        FieldValue::Id(bytes) => short_hex(bytes),
        FieldValue::Hash(bytes) => short_hex(bytes),
        FieldValue::CapEdge { target, slot } => format!("→ {} @{}", short_hex(target), slot),
        FieldValue::FieldSlot { index, hex } => format!("state[{index}] = {hex}"),
        FieldValue::CommittedSlot { index, commitment } => {
            format!("state[{index}] ⟨committed {}⟩", short_hex(commitment))
        }
    }
}

/// **Graph** → the focus + one line per node + one line per edge (lossless: node
/// short/balance/lifecycle/degrees and edge holder/target/slot/rights/facet/expiry/
/// delegation are all carried).
fn graph_children(g: &GraphView) -> Vec<ViewNode> {
    let mut out = Vec::new();
    if let Some(focus) = &g.focus {
        out.push(ViewNode::Text(format!(
            "focus: {}",
            short_hex(focus.as_bytes())
        )));
    }
    let mut nodes = Vec::with_capacity(g.nodes.len());
    for n in &g.nodes {
        nodes.push(ViewNode::Text(format!(
            "{}  bal={}  {}  out={} in={}",
            n.short, n.balance, n.lifecycle, n.out_degree, n.in_degree
        )));
    }
    out.push(ViewNode::List(nodes));
    let mut edges = Vec::with_capacity(g.edges.len());
    for e in &g.edges {
        let mut line = format!(
            "{} → {} @{} {}",
            short_hex(e.holder.as_bytes()),
            short_hex(e.target.as_bytes()),
            e.slot,
            e.rights_label(),
        );
        if e.faceted {
            line.push_str(" ·faceted");
        }
        if let Some(exp) = e.expires_at {
            line.push_str(&format!(" ·expires@{exp}"));
        }
        if let Some(ep) = e.delegated_epoch {
            line.push_str(&format!(" ·delegated@{ep}"));
        }
        edges.push(ViewNode::Text(line));
    }
    out.push(ViewNode::List(edges));
    out
}

/// **DomainVisual** → a live pill for the current state + one line per state + one line
/// per transition (lossless: current + every state's terminality + every transition's
/// from/to/verb).
fn state_machine_children(sm: &StateMachineView) -> Vec<ViewNode> {
    let mut out = Vec::new();
    // The current state as a pill (the SAME `pill` vocabulary the cockpit uses for a
    // lifecycle badge); the case list makes it a live badge if a backend binds a slot.
    out.push(ViewNode::Pill {
        text: sm.current.clone(),
        tag: "accent".into(),
        slot: None,
        cases: Vec::<PillCase>::new(),
    });
    let mut states = Vec::with_capacity(sm.states.len());
    for s in &sm.states {
        states.push(state_row(s, &sm.current));
    }
    out.push(ViewNode::List(states));
    let mut trans = Vec::with_capacity(sm.transitions.len());
    for t in &sm.transitions {
        trans.push(transition_row(t));
    }
    out.push(ViewNode::List(trans));
    out
}

fn state_row(s: &SmState, current: &str) -> ViewNode {
    let mut label = s.name.clone();
    if s.terminal {
        label.push_str(" (terminal)");
    }
    if s.name == current {
        label.push_str(" ◂ current");
    }
    ViewNode::Text(label)
}

fn transition_row(t: &SmTransition) -> ViewNode {
    ViewNode::Text(format!("{} → {} : {}", t.from, t.to, t.verb))
}

/// **Provenance** → an ordered list of events (lossless: each event's ordering key,
/// label, and — if present — its navigable receipt hash).
fn timeline_children(tl: &TimelineView) -> Vec<ViewNode> {
    let mut events = Vec::with_capacity(tl.events.len());
    for e in &tl.events {
        events.push(timeline_row(e));
    }
    vec![ViewNode::List(events)]
}

fn timeline_row(e: &TimelineEvent) -> ViewNode {
    let mut line = format!("#{}  {}", e.at, e.label);
    if let Some(h) = &e.hash {
        line.push_str(&format!("  {}", short_hex(h)));
    }
    ViewNode::Text(line)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::ViewNode;
    use deos_reflect::ReflectedCell;
    use dregg_cell::{AuthRequired, Cell, Ledger};
    use dregg_types::CellId;

    fn cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        Cell::with_balance(pk, [0u8; 32], balance)
    }

    /// A treasury cell that holds a capability over a leaf cell (one ocap edge) — the
    /// same fixture the deos-reflect crawl test uses.
    fn ledger_with_grant() -> (Ledger, CellId) {
        let mut ledger = Ledger::new();
        let leaf = cell(0x10, 100);
        let leaf_id = leaf.id();
        let mut treasury = cell(0x20, 1_000_000);
        treasury
            .capabilities
            .grant(leaf_id, AuthRequired::Signature)
            .expect("grant cap");
        let treasury_id = treasury.id();
        ledger.insert_cell(leaf).unwrap();
        ledger.insert_cell(treasury).unwrap();
        (ledger, treasury_id)
    }

    /// Collect every `Text`/`Pill`/`Section-title` string in a lowered tree, so a test
    /// can assert a datum survived the lowering (the lossless check).
    fn all_text(node: &ViewNode, out: &mut Vec<String>) {
        match node {
            ViewNode::Text(s) => out.push(s.clone()),
            ViewNode::Pill { text, .. } => out.push(text.clone()),
            ViewNode::Section {
                title, children, ..
            } => {
                out.push(title.clone());
                children.iter().for_each(|c| all_text(c, out));
            }
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                cs.iter().for_each(|c| all_text(c, out))
            }
            _ => {}
        }
    }

    fn lowered_texts(v: &ViewNode) -> Vec<String> {
        let mut out = Vec::new();
        all_text(v, &mut out);
        out
    }

    #[test]
    fn lowers_all_four_faces_into_titled_sections() {
        let (ledger, treasury_id) = ledger_with_grant();
        let reflected = ReflectedCell::from_ledger(&ledger, treasury_id).unwrap();
        let faces = reflected.present(&ledger, &[]);
        assert_eq!(
            faces.len(),
            4,
            "RawFields · Graph · DomainVisual · Provenance"
        );

        let card = presentations_to_view(&faces);
        let ViewNode::VStack(sections) = &card else {
            panic!("a face-set lowers to a VStack of sections")
        };
        assert_eq!(sections.len(), 4, "one section per face");
        for s in sections {
            assert!(
                matches!(s, ViewNode::Section { .. }),
                "each face lowers to a titled Section"
            );
        }
        // The face slugs survive as the section `tag`s.
        let tags: Vec<&str> = sections
            .iter()
            .filter_map(|s| match s {
                ViewNode::Section { tag, .. } => Some(tag.as_str()),
                _ => None,
            })
            .collect();
        assert!(tags.contains(&"raw-fields"));
        assert!(tags.contains(&"graph"));
        assert!(tags.contains(&"domain-visual"));
        assert!(tags.contains(&"provenance"));
    }

    #[test]
    fn raw_fields_lowering_is_lossless_over_the_field_keys() {
        let (ledger, treasury_id) = ledger_with_grant();
        let reflected = ReflectedCell::from_ledger(&ledger, treasury_id).unwrap();
        let raw = reflected.raw_fields();
        let PresentationBody::Fields(insp) = &raw.body else {
            panic!("raw-fields body")
        };

        let lowered = presentation_to_view(&raw);
        let texts = lowered_texts(&lowered);
        // Every field key appears as a `key:` row in the lowered tree — lossless.
        for f in &insp.fields {
            assert!(
                texts.iter().any(|t| t == &format!("{}:", f.key)),
                "field key `{}` survived the lowering",
                f.key
            );
        }
        // The section is titled by the face label.
        assert!(texts.contains(&raw.label));
    }

    #[test]
    fn domain_visual_lowering_carries_the_current_state_as_a_pill() {
        let (ledger, treasury_id) = ledger_with_grant();
        let reflected = ReflectedCell::from_ledger(&ledger, treasury_id).unwrap();
        let dv = reflected.domain_visual();
        let PresentationBody::StateMachine(sm) = &dv.body else {
            panic!("state-machine body")
        };
        let current = sm.current.clone();

        let lowered = presentation_to_view(&dv);
        // The current state is present as a pill (the live-badge vocabulary).
        let mut has_pill = false;
        fn find_pill(n: &ViewNode, want: &str, found: &mut bool) {
            match n {
                ViewNode::Pill { text, .. } if text == want => *found = true,
                ViewNode::Section { children, .. } => {
                    children.iter().for_each(|c| find_pill(c, want, found))
                }
                ViewNode::VStack(cs) | ViewNode::List(cs) | ViewNode::Row(cs) => {
                    cs.iter().for_each(|c| find_pill(c, want, found))
                }
                _ => {}
            }
        }
        find_pill(&lowered, &current, &mut has_pill);
        assert!(has_pill, "current state `{current}` lowered to a Pill");
        // Every state name survives as a row.
        let texts = lowered_texts(&lowered);
        for s in &sm.states {
            assert!(
                texts.iter().any(|t| t.starts_with(&s.name)),
                "state `{}` survived",
                s.name
            );
        }
    }
}
