//! The REFLECTIVE CRAWL binding (slice 2) — JSON projections of the live image for
//! the JS `deos.world` / `deos.cell` object graph.
//!
//! The native functions in [`crate::js`] return these JSON strings; the JS prelude
//! parses them into rich `deos.world` / `deos.cell` objects. Every projection is a
//! cap-bounded, attested read off the applet's live ledger via [`deos_reflect`]:
//!
//!   - `deos.world.cells()` → [`world_cells_json`] (every cell id, id-sorted);
//!   - `deos.world.ocap()` → [`world_ocap_json`] (the capability web);
//!   - `deos.cell(id)` → [`cell_json`] (the four substances + faces);
//!   - `deos.cell(id).as(viewer)` → [`frustum_json`] (the cap-bounded view).
//!
//! Reflection is a READ that confers no authority — distinct from driving (a turn).
//! All JSON is hand-built (no serde dep) to keep the binding lean.

use deos_reflect::present::{PresentationBody, PresentationKind};
use deos_reflect::substance::{hex_encode, FieldValue};
use deos_reflect::{reflect_cell, AffordanceSurface, Frustum, OcapGraph, ReflectedCell};
use dregg_cell::{AuthRequired, Ledger};
use dregg_turn::action::Effect;
use dregg_types::CellId;

/// Parse a 64-hex-char cell id from JS. Returns `None` on a malformed id.
pub fn parse_cell_id(hex: &str) -> Option<CellId> {
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(CellId::from_bytes(bytes))
}

fn id_hex(id: &CellId) -> String {
    hex_encode(id.as_bytes())
}

/// A JSON string escape (the small subset our labels need).
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            _ => out.push(c),
        }
    }
    out
}

/// `deos.world.cells()` — every cell id on the ledger, id-sorted, as a JSON array of
/// hex strings. The unbounded crawl root (`.as(viewer)` bounds it).
pub fn world_cells_json(ledger: &Ledger) -> String {
    let mut ids: Vec<CellId> = ledger.iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    let items: Vec<String> = ids.iter().map(|id| format!("\"{}\"", id_hex(id))).collect();
    format!("[{}]", items.join(","))
}

/// `deos.world.ocap()` — the capability web: nodes (cells + degrees) and edges
/// (holder → target at rights), as JSON.
pub fn world_ocap_json(ledger: &Ledger) -> String {
    let g = OcapGraph::build(ledger);
    let nodes: Vec<String> = g
        .nodes()
        .iter()
        .map(|n| {
            format!(
                "{{\"cell\":\"{}\",\"short\":\"{}\",\"balance\":{},\"lifecycle\":\"{}\",\"out\":{},\"in\":{}}}",
                id_hex(&n.cell),
                esc(&n.short),
                n.balance,
                esc(&n.lifecycle),
                n.out_degree,
                n.in_degree,
            )
        })
        .collect();
    let edges: Vec<String> = g
        .edges()
        .iter()
        .map(|e| {
            format!(
                "{{\"holder\":\"{}\",\"target\":\"{}\",\"slot\":{},\"rights\":\"{}\",\"faceted\":{},\"delegated\":{}}}",
                id_hex(&e.holder),
                id_hex(&e.target),
                e.slot,
                e.rights_label(),
                e.faceted,
                e.is_delegated(),
            )
        })
        .collect();
    format!(
        "{{\"nodes\":[{}],\"edges\":[{}]}}",
        nodes.join(","),
        edges.join(",")
    )
}

/// `deos.cell(id)` — the full reflective view of one cell: the four substances as a
/// JSON object (`balance`, `nonce`, `caps`, `lifecycle`, `fields[]`). Reads fields
/// PUBLICLY (a `Committed` slot surfaces its commitment, never the value).
pub fn cell_json(ledger: &Ledger, id: &CellId) -> Option<String> {
    let cell = ledger.get(id)?;
    let insp = reflect_cell(id, cell);
    Some(inspectable_json(&insp))
}

/// `deos.cell(id).as(viewer)` — the cap-bounded view: which cells `viewer` may crawl
/// + whether it observes `id`. An unobservable cell yields `observable:false` (an
/// absence, never a forged read).
pub fn frustum_json(ledger: &Ledger, viewer: &CellId) -> String {
    let f = Frustum::project(ledger, *viewer);
    let visible: Vec<String> =
        f.visible_cells().iter().map(|c| format!("\"{}\"", id_hex(c))).collect();
    format!(
        "{{\"viewer\":\"{}\",\"visibleCount\":{},\"visible\":[{}]}}",
        id_hex(viewer),
        f.visible_count(),
        visible.join(","),
    )
}

/// `deos.cell(id).as(viewer).reflect(target)` — reflect `target` THROUGH `viewer`'s
/// authority. Returns the cell JSON if observable, else `null` (the attested read:
/// an unreachable cell is absent, not forged).
pub fn frustum_reflect_json(ledger: &Ledger, viewer: &CellId, target: &CellId) -> String {
    let f = Frustum::project(ledger, *viewer);
    match f.reflect(target) {
        Some(insp) => inspectable_json(&insp),
        None => "null".to_string(),
    }
}

/// Serialize an [`deos_reflect::Inspectable`] to JSON (the uniform reflective view).
fn inspectable_json(insp: &deos_reflect::Inspectable) -> String {
    let fields: Vec<String> = insp
        .fields
        .iter()
        .map(|f| {
            let (ty, val) = field_value_json(&f.value);
            format!("{{\"key\":\"{}\",\"type\":\"{}\",\"value\":{}}}", esc(&f.key), ty, val)
        })
        .collect();
    format!(
        "{{\"kind\":\"{:?}\",\"title\":\"{}\",\"subtitle\":\"{}\",\"fields\":[{}]}}",
        insp.kind,
        esc(&insp.title),
        esc(&insp.subtitle),
        fields.join(","),
    )
}

/// Render a [`FieldValue`] as `(typeTag, jsonValue)`.
fn field_value_json(v: &FieldValue) -> (&'static str, String) {
    match v {
        FieldValue::Text(s) => ("text", format!("\"{}\"", esc(s))),
        FieldValue::Balance(b) => ("balance", b.to_string()),
        FieldValue::Count(c) => ("count", c.to_string()),
        FieldValue::Bool(b) => ("bool", b.to_string()),
        FieldValue::Id(id) => ("id", format!("\"{}\"", hex_encode(id))),
        FieldValue::Hash(h) => ("hash", format!("\"{}\"", hex_encode(h))),
        FieldValue::CapEdge { target, slot } => (
            "capEdge",
            format!("{{\"target\":\"{}\",\"slot\":{}}}", hex_encode(target), slot),
        ),
        FieldValue::FieldSlot { index, hex } => {
            ("fieldSlot", format!("{{\"index\":{},\"hex\":\"{}\"}}", index, esc(hex)))
        }
        FieldValue::CommittedSlot { index, commitment } => (
            "committedSlot",
            format!(
                "{{\"index\":{},\"commitment\":\"{}\",\"redacted\":true}}",
                index,
                hex_encode(commitment)
            ),
        ),
    }
}

// ── present() — the moldable faces ────────────────────────────────────────────────

/// `deos.cell(id).present()` → the moldable faces (RawFields · Graph · DomainVisual ·
/// Provenance) as a JSON array. Each face is a distinct `obs`-projection of the same
/// cell; the gpui render maps each to a widget. `receipts` feeds the Provenance face.
pub fn cell_present_json(
    ledger: &Ledger,
    id: &CellId,
    receipts: &[dregg_turn::turn::TurnReceipt],
) -> Option<String> {
    let reflected = ReflectedCell::from_ledger(ledger, *id)?;
    let faces = reflected.present(ledger, receipts);
    let items: Vec<String> = faces
        .iter()
        .map(|p| {
            format!(
                "{{\"kind\":\"{}\",\"label\":\"{}\",\"body\":{}}}",
                face_kind_slug(p.kind),
                esc(&p.label),
                face_body_json(&p.body),
            )
        })
        .collect();
    Some(format!("[{}]", items.join(",")))
}

fn face_kind_slug(k: PresentationKind) -> &'static str {
    k.slug()
}

/// Serialize a face body to JSON (each is pure data the view layer renders).
fn face_body_json(body: &PresentationBody) -> String {
    match body {
        PresentationBody::Fields(insp) => format!("{{\"type\":\"fields\",\"value\":{}}}", inspectable_json(insp)),
        PresentationBody::Graph(gv) => {
            let nodes: Vec<String> = gv
                .nodes
                .iter()
                .map(|n| format!("\"{}\"", id_hex(&n.cell)))
                .collect();
            let edges: Vec<String> = gv
                .edges
                .iter()
                .map(|e| {
                    format!(
                        "{{\"holder\":\"{}\",\"target\":\"{}\",\"rights\":\"{}\"}}",
                        id_hex(&e.holder),
                        id_hex(&e.target),
                        e.rights_label()
                    )
                })
                .collect();
            format!(
                "{{\"type\":\"graph\",\"nodes\":[{}],\"edges\":[{}]}}",
                nodes.join(","),
                edges.join(",")
            )
        }
        PresentationBody::StateMachine(sm) => {
            let states: Vec<String> = sm
                .states
                .iter()
                .map(|s| format!("{{\"name\":\"{}\",\"terminal\":{}}}", esc(&s.name), s.terminal))
                .collect();
            let trans: Vec<String> = sm
                .transitions
                .iter()
                .map(|t| {
                    format!(
                        "{{\"from\":\"{}\",\"to\":\"{}\",\"verb\":\"{}\"}}",
                        esc(&t.from),
                        esc(&t.to),
                        esc(&t.verb)
                    )
                })
                .collect();
            format!(
                "{{\"type\":\"stateMachine\",\"current\":\"{}\",\"states\":[{}],\"transitions\":[{}]}}",
                esc(&sm.current),
                states.join(","),
                trans.join(",")
            )
        }
        PresentationBody::Timeline(tv) => {
            let events: Vec<String> = tv
                .events
                .iter()
                .map(|e| {
                    let hash = e
                        .hash
                        .map(|h| format!("\"{}\"", hex_encode(&h)))
                        .unwrap_or_else(|| "null".to_string());
                    format!("{{\"at\":{},\"label\":\"{}\",\"hash\":{}}}", e.at, esc(&e.label), hash)
                })
                .collect();
            format!("{{\"type\":\"timeline\",\"events\":[{}]}}", events.join(","))
        }
    }
}

// ── affordances(viewer) — the cap-gated message list ──────────────────────────────

/// `deos.cell(id).affordances(viewer)` → the cap-gated affordance list a holder of
/// `held` may see/fire, as JSON. Built from the registered `specs` (name + required
/// authority); projected by `is_attenuation` (`required ⊆ held`). A weaker viewer
/// receives a strictly smaller set — the frustum's affordance half.
pub fn cell_affordances_json(cell: &CellId, specs: &[(String, AuthRequired)], held: &AuthRequired) -> String {
    let mut surface = AffordanceSurface::new(*cell);
    for (name, required) in specs {
        // A representative effect template (the real turn an affordance fires touches
        // the cell's state); the *projection* is by `required` vs `held`.
        surface = surface.declare(deos_reflect::Affordance::new(
            name.clone(),
            required.clone(),
            Effect::IncrementNonce { cell: *cell },
        ));
    }
    let visible: Vec<String> = surface
        .project_for(held)
        .into_iter()
        .map(|a| {
            format!(
                "{{\"name\":\"{}\",\"required\":\"{}\"}}",
                esc(&a.name),
                auth_label(&a.required)
            )
        })
        .collect();
    format!("[{}]", visible.join(","))
}

fn auth_label(a: &AuthRequired) -> &'static str {
    match a {
        AuthRequired::None => "none",
        AuthRequired::Signature => "signature",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        AuthRequired::Custom { .. } => "custom",
    }
}

// ── spotter — fuzzy search over every object's faces ──────────────────────────────

/// `deos.search(q)` → a fuzzy search over every cell's reflective text (id, lifecycle,
/// field keys), as a JSON array of hits `{cell, score, snippet}`. A simple
/// substring+subsequence scorer (no UI-palette dep): score = matched-chars / query-len,
/// scaled. Hits sorted best-first.
pub fn spotter_json(ledger: &Ledger, query: &str) -> String {
    let q = query.to_lowercase();
    let mut hits: Vec<(i64, String, String)> = Vec::new();
    let mut ids: Vec<CellId> = ledger.iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    for id in &ids {
        if let Some(cell) = ledger.get(id) {
            let insp = reflect_cell(id, cell);
            // The searchable text: id + title + subtitle + every field key.
            let mut text = format!("{} {} {}", id_hex(id), insp.title, insp.subtitle);
            for f in &insp.fields {
                text.push(' ');
                text.push_str(&f.key);
            }
            let lower = text.to_lowercase();
            if let Some(score) = fuzzy_score(&q, &lower) {
                hits.push((score, id_hex(id), insp.title.clone()));
            }
        }
    }
    hits.sort_by(|a, b| b.0.cmp(&a.0));
    let items: Vec<String> = hits
        .iter()
        .map(|(score, cell, title)| {
            format!("{{\"cell\":\"{}\",\"score\":{},\"snippet\":\"{}\"}}", cell, score, esc(title))
        })
        .collect();
    format!("[{}]", items.join(","))
}

/// A simple fuzzy score: contiguous-substring match scores highest; otherwise an
/// in-order subsequence match scores lower; no match → `None`. (No palette dep.)
fn fuzzy_score(query: &str, text: &str) -> Option<i64> {
    if query.is_empty() {
        return Some(0);
    }
    if text.contains(query) {
        return Some(1000 - (text.len() as i64).min(900));
    }
    // subsequence: every query char appears in order
    let mut qi = query.chars();
    let mut want = qi.next();
    let mut matched = 0i64;
    for c in text.chars() {
        if Some(c) == want {
            matched += 1;
            want = qi.next();
            if want.is_none() {
                break;
            }
        }
    }
    if want.is_none() {
        Some(100 + matched)
    } else {
        None
    }
}
