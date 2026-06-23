//! THE DREGG COCKPIT MODEL, IN THE BROWSER.
//!
//! The gpui-free `Presentable`/`World` model — the same substance the native
//! cockpit renders — compiled to wasm and exposed to JS via wasm-bindgen. This
//! is `dregg-mcp`'s core tools (survey / inspect / affordances / act / ocap),
//! but in-browser: every call drives the REAL embedded executor
//! (`starbridge_v2::world::World`), not a mock and not a recorded crawl. The
//! dregg-atlas's renderer drives this live — the atlas grown up into the cockpit.
//!
//! One model, web skin.

use dregg_cell::permissions::AuthRequired;
use dregg_cell::CellId;
use serde_json::{json, Value};
use wasm_bindgen::prelude::*;

use starbridge_v2::graph::OcapGraph;
use starbridge_v2::inspect_act::{InspectAct, InspectFocus, SendResult};
use starbridge_v2::presentable::{FocusTarget, Presentation, PresentationBody, Registry};
use starbridge_v2::reflect::{FieldValue, Inspectable};
use starbridge_v2::world::{self, World};

// THE GPUI COCKPIT, IN THE BROWSER (first slice) — the REAL gpui element-tree
// renderer on the `gpui_web` backend (wasm32 + WebGPU canvas), driving the same
// embedded `World`. Gated on `gpui-web` (pulls gpui + gpui_platform → gpui_web).
// This is the FULL-COCKPIT path, not the JSON/atlas skin above; see
// `cockpit_web::boot_cockpit` and docs/deos/WEB-DEOS.md.
#[cfg(all(target_arch = "wasm32", feature = "gpui-web"))]
pub mod cockpit_web;

// THE WEB COCKPIT'S TERMINAL BACKEND — a PTY over a WebSocket. The native side is
// the WS↔PTY server (`pty_ws::serve`, behind `pty-ws-server`, run by the
// `starbridge-web-pty-ws` bin); the wasm side is the `WsTransport` client the
// in-browser terminal pane dials. One wire codec (`WireMsg`) shared by both ends.
// See docs/deos/WEB-DEOS.md (the per-app backend map: Terminal).
pub mod pty_ws;

#[wasm_bindgen]
pub struct WebImage {
    world: World,
    anchors: [CellId; 3],
}

#[wasm_bindgen]
impl WebImage {
    /// Boot a fresh, fully-seeded sovereign image (the same `demo_world` the
    /// native cockpit + the atlas crawl use).
    #[wasm_bindgen(constructor)]
    pub fn new() -> WebImage {
        let (world, anchors) = world::demo_world();
        WebImage { world, anchors }
    }

    /// The cell roster — every ledger cell with its headline fields.
    pub fn survey(&self) -> String {
        let mut cells = Vec::new();
        for (id, cell) in self.world.ledger().iter() {
            let insp = starbridge_v2::reflect::reflect_cell(id, cell);
            let mut balance = None;
            let mut caps = 0u64;
            for f in &insp.fields {
                match (&f.key[..], &f.value) {
                    ("balance", FieldValue::Balance(b)) => balance = Some(*b),
                    (_, FieldValue::CapEdge { .. }) => caps += 1,
                    _ => {}
                }
            }
            cells.push(json!({
                "id": hex32(id.as_bytes()), "short": short(id.as_bytes()),
                "kind": format!("{:?}", insp.kind), "title": insp.title,
                "subtitle": insp.subtitle, "balance": balance, "cap_edges": caps,
            }));
        }
        out(&json!({
            "cell_count": cells.len(),
            "anchors": { "treasury": short(self.anchors[0].as_bytes()), "service": short(self.anchors[1].as_bytes()), "user": short(self.anchors[2].as_bytes()) },
            "cells": cells,
        }))
    }

    /// A cell's seven presentation faces (Registry::present) + its halo ring.
    pub fn inspect(&self, cell: &str) -> String {
        let id = match self.resolve(cell) {
            Some(id) => id,
            None => return err(&format!("no cell matched `{cell}`")),
        };
        let reg = Registry::new(&self.world);
        match reg.present(FocusTarget::Cell(id), id) {
            Some(set) => out(&json!({
                "cell": hex32(id.as_bytes()), "short": short(id.as_bytes()),
                "faces": set.iter().map(presentation_json).collect::<Vec<_>>(),
            })),
            None => err(&format!("cell {} absent", short(id.as_bytes()))),
        }
    }

    /// The messages a cell understands, each with its effect + cap badge.
    pub fn affordances(&self, cell: &str) -> String {
        let id = match self.resolve(cell) {
            Some(id) => id,
            None => return err(&format!("no cell matched `{cell}`")),
        };
        let ia = InspectAct::build(&self.world, InspectFocus::Cell(id), id, AuthRequired::Either);
        out(&json!({
            "cell": short(id.as_bytes()),
            "messages": ia.messages.iter().map(|m| json!({
                "name": m.name, "effect": m.effect,
                "required": format!("{:?}", m.required), "authorized": m.authorized,
            })).collect::<Vec<_>>(),
        }))
    }

    /// FIRE a message — a real cap-gated turn through the verified executor.
    /// Mutates the live image; returns the receipt or the in-band refusal.
    pub fn act(&mut self, cell: &str, message: &str) -> String {
        let id = match self.resolve(cell) {
            Some(id) => id,
            None => return err(&format!("no cell matched `{cell}`")),
        };
        let ia = InspectAct::build(&self.world, InspectFocus::Cell(id), id, AuthRequired::Either);
        match ia.send(&mut self.world, message, AuthRequired::Either) {
            SendResult::Committed { receipt, reinspected } => out(&json!({
                "outcome": "committed", "cell": short(id.as_bytes()), "message": message,
                "receipt": { "post_state": short(&receipt.post_state_hash), "computrons": receipt.computrons_used, "actions": receipt.action_count },
                "reinspected": inspectable_json(&reinspected),
            })),
            SendResult::Refused { reason, by_executor } => out(&json!({
                "outcome": "refused", "cell": short(id.as_bytes()), "message": message,
                "by_executor": by_executor, "reason": reason,
            })),
        }
    }

    /// The whole ocap web — cells + capability edges.
    pub fn ocap(&self) -> String {
        let g = OcapGraph::build(&self.world);
        out(&json!({
            "nodes": g.nodes().iter().map(|n| json!({ "id": short(n.cell.as_bytes()), "balance": n.balance, "lifecycle": n.lifecycle, "out": n.out_degree, "in": n.in_degree })).collect::<Vec<_>>(),
            "edges": g.edges().iter().map(|e| json!({ "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()), "slot": e.slot, "rights": format!("{:?}", e.rights) })).collect::<Vec<_>>(),
        }))
    }

    fn resolve(&self, s: &str) -> Option<CellId> {
        let s = s.trim();
        match s {
            "treasury" => return Some(self.anchors[0]),
            "service" => return Some(self.anchors[1]),
            "user" => return Some(self.anchors[2]),
            _ => {}
        }
        let pfx = s.strip_prefix("0x").unwrap_or(s).to_lowercase();
        if pfx.len() == 64 {
            if let Ok(b) = hex::decode(&pfx) {
                if let Ok(arr) = <[u8; 32]>::try_from(b.as_slice()) {
                    return Some(CellId::from_bytes(arr));
                }
            }
        }
        let mut hit = None;
        for (id, _) in self.world.ledger().iter() {
            if hex::encode(id.as_bytes()).starts_with(&pfx) {
                if hit.is_some() {
                    return None;
                }
                hit = Some(*id);
            }
        }
        hit
    }
}

impl Default for WebImage {
    fn default() -> Self {
        Self::new()
    }
}

// --- JSON helpers (the dregg-mcp serializers, shared shape) -----------------

fn out(v: &Value) -> String {
    serde_json::to_string(v).unwrap_or_else(|_| "{}".into())
}
fn err(msg: &str) -> String {
    out(&json!({ "error": msg }))
}
fn hex32(b: &[u8; 32]) -> String {
    hex::encode(b)
}
fn short(b: &[u8; 32]) -> String {
    let h = hex::encode(b);
    format!("{}…{}", &h[..6], &h[h.len() - 4..])
}

fn field_value_json(v: &FieldValue) -> Value {
    match v {
        FieldValue::Text(s) => json!({ "t": "text", "v": s }),
        FieldValue::Balance(n) => json!({ "t": "balance", "v": n }),
        FieldValue::Count(n) => json!({ "t": "count", "v": n }),
        FieldValue::Bool(b) => json!({ "t": "bool", "v": b }),
        FieldValue::Id(id) => json!({ "t": "id", "v": hex32(id), "short": short(id) }),
        FieldValue::Hash(h) => json!({ "t": "hash", "v": hex32(h), "short": short(h) }),
        FieldValue::CapEdge { target, slot } => json!({ "t": "cap-edge", "target": hex32(target), "short": short(target), "slot": slot }),
        FieldValue::FieldSlot { index, hex } => json!({ "t": "slot", "index": index, "hex": hex }),
    }
}

fn inspectable_json(i: &Inspectable) -> Value {
    json!({
        "kind": format!("{:?}", i.kind), "title": i.title, "subtitle": i.subtitle,
        "fields": i.fields.iter().map(|f| json!({ "key": f.key, "value": field_value_json(&f.value) })).collect::<Vec<_>>(),
    })
}

fn body_json(b: &PresentationBody) -> Value {
    match b {
        PresentationBody::Fields(i) => json!({ "shape": "fields", "fields": inspectable_json(i) }),
        PresentationBody::Graph(g) => json!({
            "shape": "graph",
            "edges": g.edges.iter().map(|e| json!({ "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()), "slot": e.slot, "rights": format!("{:?}", e.rights) })).collect::<Vec<_>>(),
        }),
        PresentationBody::Prose(p) => json!({ "shape": "prose", "text": p }),
        PresentationBody::Timeline(t) => json!({
            "shape": "timeline",
            "events": t.events.iter().map(|e| json!({ "at": e.at, "label": e.label })).collect::<Vec<_>>(),
        }),
        PresentationBody::Gauge(g) => json!({ "shape": "gauge", "label": g.label, "value": g.value, "ceiling": g.ceiling }),
        PresentationBody::StateMachine(sm) => json!({
            "shape": "state-machine", "current": sm.current,
            "transitions": sm.transitions.iter().map(|t| json!({ "from": t.from, "to": t.to, "verb": t.verb })).collect::<Vec<_>>(),
        }),
        other => json!({ "shape": "other", "debug": format!("{other:?}") }),
    }
}

fn presentation_json(p: &Presentation) -> Value {
    json!({ "kind": p.kind.slug(), "label": p.label, "body": body_json(&p.body) })
}
