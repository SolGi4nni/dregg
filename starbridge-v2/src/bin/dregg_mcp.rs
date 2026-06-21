//! dregg-mcp — a Model Context Protocol server that drives the starbridge-v2
//! LIVE VERIFIED IMAGE so an agent (me) can inspect, act, map, and screenshot
//! the real dregg ocap world while iterating on the project.
//!
//! It is the Firebug-for-a-verified-OS harness: every tool reads or writes the
//! REAL embedded executor (`dregg_sdk::embed::DreggEngine`, via
//! `starbridge_v2::world::World`) — there is no mock. `inspect` is the
//! reflective DOM (the moldable inspector's seven presentation faces as JSON);
//! `act` fires a genuine cap-gated turn through the verified executor and shows
//! the receipt or the in-band refusal; `graph` emits the ocap web / affordance
//! map / this-session interaction trail (DOT + JSON) for a manual; `screenshot`
//! bakes the REAL gpui `Cockpit` element tree (over this session's driven state)
//! to a PNG via the headless render subprocess.
//!
//! Transport: JSON-RPC 2.0, newline-delimited, over stdio (the MCP local
//! transport — same hand-rolled shape as `node/src/mcp.rs`). The `World` is held
//! in the long-running process, so state persists across tool calls.
//!
//! Build (model tools, no gpui — fast + robust):
//!   cargo build --release --no-default-features --features embedded-executor --bin dregg-mcp
//! The `screenshot` tool shells out to a separately-built `headless-render`
//! `starbridge-v2` binary, so this process never links gpui.

use std::io::{self, BufRead, Write};

use dregg_cell::permissions::AuthRequired;
use dregg_cell::CellId;
use serde_json::{json, Value};

use starbridge_v2::graph::OcapGraph;
use starbridge_v2::inspect_act::{InspectAct, InspectFocus, SendResult};
use starbridge_v2::presentable::{
    FocusTarget, HaloCommand, Presentation, PresentationBody, Registry, Spotter,
};
use starbridge_v2::reflect::{FieldValue, Inspectable};
use starbridge_v2::world::{self, World};

// ===========================================================================
// session state — the live world the whole MCP drives
// ===========================================================================

struct Session {
    world: World,
    /// The three demo anchors (treasury, service, user) for name resolution.
    anchors: [CellId; 3],
    /// The image this session booted from (so `rewind` re-seeds identically).
    image: String,
    /// Every committed act this session, as `(cell, message)` — replayed into
    /// the screenshot bake, the `rewind` backtrack, AND the interaction graph.
    acts: Vec<(CellId, String)>,
    /// The cells inspected this session, in order — the navigation trail the
    /// interaction map draws.
    visited: Vec<CellId>,
}

impl Session {
    fn boot(image: &str) -> Self {
        let (world, anchors) = match image {
            "empty" => {
                let mut w = World::new();
                // A minimal pair so an empty image is still drivable.
                let a = w.genesis_cell(0x11, 1_000);
                let b = w.genesis_cell(0x22, 0);
                let c = w.genesis_cell(0x33, 500);
                (w, [a, b, c])
            }
            // "demo" (default) — the fully-seeded sovereign image.
            _ => world::demo_world(),
        };
        Session { world, anchors, image: image.to_string(), acts: Vec::new(), visited: Vec::new() }
    }

    /// Fire a committed act as `cell`-over-itself with the `Either` tier (the
    /// self-operator projection), recording it. Used by `rewind` replay so a
    /// game-tree branch reconstructs deterministically.
    fn apply_act(&mut self, cell: CellId, message: &str) -> bool {
        let ia = InspectAct::build(&self.world, InspectFocus::Cell(cell), cell, AuthRequired::Either);
        match ia.send(&mut self.world, message, AuthRequired::Either) {
            SendResult::Committed { .. } => {
                self.acts.push((cell, message.to_string()));
                true
            }
            SendResult::Refused { .. } => false,
        }
    }

    /// Resolve a user-supplied cell handle: an anchor NAME (`treasury`/`service`/
    /// `user`), a full 64-char hex id, or a hex-id PREFIX matched against the
    /// live ledger (the same short ids `survey` prints).
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
            if let Ok(bytes) = hex::decode(&pfx) {
                if let Ok(arr) = <[u8; 32]>::try_from(bytes.as_slice()) {
                    return Some(CellId::from_bytes(arr));
                }
            }
        }
        // Prefix match over the ledger (deterministic id order).
        let mut hit = None;
        for (id, _) in self.world.ledger().iter() {
            if hex::encode(id.as_bytes()).starts_with(&pfx) {
                if hit.is_some() {
                    return None; // ambiguous prefix — make the caller disambiguate
                }
                hit = Some(*id);
            }
        }
        hit
    }
}

fn parse_rights(v: Option<&str>) -> AuthRequired {
    match v.unwrap_or("either").to_lowercase().as_str() {
        "none" => AuthRequired::None,
        "signature" | "sig" => AuthRequired::Signature,
        "proof" => AuthRequired::Proof,
        "locked" | "never" | "impossible" => AuthRequired::Impossible,
        _ => AuthRequired::Either,
    }
}

// ===========================================================================
// JSON serialization of the moldable inspector's pure-data presentation tree
// ===========================================================================

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
        FieldValue::CapEdge { target, slot } => {
            json!({ "t": "cap-edge", "target": hex32(target), "short": short(target), "slot": slot })
        }
        FieldValue::FieldSlot { index, hex } => json!({ "t": "slot", "index": index, "hex": hex }),
    }
}

fn inspectable_json(i: &Inspectable) -> Value {
    json!({
        "kind": format!("{:?}", i.kind),
        "title": i.title,
        "subtitle": i.subtitle,
        "fields": i.fields.iter().map(|f| json!({ "key": f.key, "value": field_value_json(&f.value) })).collect::<Vec<_>>(),
    })
}

fn body_json(b: &PresentationBody) -> Value {
    match b {
        PresentationBody::Fields(i) => json!({ "shape": "fields", "fields": inspectable_json(i) }),
        PresentationBody::Graph(g) => json!({
            "shape": "graph",
            "focus": g.focus.map(|c| short(c.as_bytes())),
            "nodes": g.nodes.iter().map(|n| json!({
                "cell": short(n.cell.as_bytes()), "id": hex32(n.cell.as_bytes()),
                "balance": n.balance, "lifecycle": n.lifecycle,
                "out": n.out_degree, "in": n.in_degree,
            })).collect::<Vec<_>>(),
            "edges": g.edges.iter().map(|e| json!({
                "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()),
                "slot": e.slot, "rights": format!("{:?}", e.rights), "faceted": e.faceted,
            })).collect::<Vec<_>>(),
        }),
        PresentationBody::StateMachine(sm) => json!({
            "shape": "state-machine", "current": sm.current,
            "states": sm.states.iter().map(|s| json!({ "name": s.name, "terminal": s.terminal })).collect::<Vec<_>>(),
            "transitions": sm.transitions.iter().map(|t| json!({ "from": t.from, "to": t.to, "verb": t.verb })).collect::<Vec<_>>(),
        }),
        PresentationBody::Gauge(g) => json!({
            "shape": "gauge", "label": g.label, "value": g.value, "ceiling": g.ceiling, "rungs": g.rungs,
        }),
        PresentationBody::Timeline(t) => json!({
            "shape": "timeline",
            "events": t.events.iter().map(|e| json!({
                "at": e.at, "label": e.label, "hash": e.hash.map(|h| short(&h)),
            })).collect::<Vec<_>>(),
        }),
        PresentationBody::MerkleTree(m) => json!({
            "shape": "merkle", "label": m.label, "root": short(&m.root),
            "leaves": m.leaves, "path": m.path,
        }),
        PresentationBody::Lattice(l) => json!({
            "shape": "lattice", "nodes": l.nodes, "edges": l.edges, "current": l.current,
        }),
        PresentationBody::Trace(t) => json!({
            "shape": "trace",
            "steps": t.steps.iter().map(|s| json!({ "index": s.index, "label": s.label })).collect::<Vec<_>>(),
        }),
        PresentationBody::Prose(p) => json!({ "shape": "prose", "text": p }),
    }
}

fn presentation_json(p: &Presentation) -> Value {
    json!({ "kind": p.kind.slug(), "label": p.label, "body": body_json(&p.body) })
}

// ===========================================================================
// tools
// ===========================================================================

fn tool_survey(s: &Session) -> Value {
    let mut cells = Vec::new();
    for (id, cell) in s.world.ledger().iter() {
        let insp = starbridge_v2::reflect::reflect_cell(id, cell);
        // pull a couple of headline fields out of the reflection
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
            "id": hex32(id.as_bytes()),
            "short": short(id.as_bytes()),
            "kind": format!("{:?}", insp.kind),
            "title": insp.title,
            "subtitle": insp.subtitle,
            "balance": balance,
            "cap_edges": caps,
        }));
    }
    json!({
        "cell_count": cells.len(),
        "anchors": { "treasury": short(s.anchors[0].as_bytes()), "service": short(s.anchors[1].as_bytes()), "user": short(s.anchors[2].as_bytes()) },
        "cells": cells,
        "hint": "inspect <id|short|treasury|service|user> to open the seven presentation faces",
    })
}

fn tool_inspect(s: &mut Session, cell: &str, view_as: Option<&str>, rights: Option<&str>) -> Result<Value, String> {
    let id = s.resolve(cell).ok_or_else(|| format!("no cell matched `{cell}` (try survey)"))?;
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(id);
    let _rights = parse_rights(rights);
    s.visited.push(id);

    let reg = Registry::new(&s.world);
    let set = reg
        .present(FocusTarget::Cell(id), viewer)
        .ok_or_else(|| format!("cell {} is absent from the live world (dangling focus)", short(id.as_bytes())))?;
    let halo = reg.halo(FocusTarget::Cell(id));

    Ok(json!({
        "cell": hex32(id.as_bytes()),
        "short": short(id.as_bytes()),
        "viewer": short(viewer.as_bytes()),
        "halo": halo.commands.iter().map(halo_label).collect::<Vec<_>>(),
        "faces": set.iter().map(presentation_json).collect::<Vec<_>>(),
        "hint": "affordances <cell> for the messages it understands; act <cell> <message> to fire one",
    }))
}

fn halo_label(c: &HaloCommand) -> &'static str {
    match c {
        HaloCommand::Inspect => "inspect",
        HaloCommand::Grab => "grab",
        HaloCommand::Explain => "explain",
        HaloCommand::VerifyChain => "verify-chain",
        HaloCommand::Attenuate => "attenuate",
    }
}

fn tool_affordances(s: &Session, cell: &str, view_as: Option<&str>, rights: Option<&str>) -> Result<Value, String> {
    let id = s.resolve(cell).ok_or_else(|| format!("no cell matched `{cell}`"))?;
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(id);
    let rights = parse_rights(rights);
    let ia = InspectAct::build(&s.world, InspectFocus::Cell(id), viewer, rights);
    Ok(json!({
        "cell": short(id.as_bytes()),
        "viewer": short(viewer.as_bytes()),
        "viewer_tier": ia.viewer_tier,
        "messages": ia.messages.iter().map(|m| json!({
            "name": m.name,
            "effect": m.effect,
            "required": format!("{:?}", m.required),
            "authorized": m.authorized,
        })).collect::<Vec<_>>(),
        "authorized": ia.authorized_messages(),
        "hint": "an unauthorized message is SHOWN not hidden (anti-ghost); act fires it and shows the real refusal",
    }))
}

fn tool_act(s: &mut Session, cell: &str, message: &str, view_as: Option<&str>, rights: Option<&str>) -> Result<Value, String> {
    let id = s.resolve(cell).ok_or_else(|| format!("no cell matched `{cell}`"))?;
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(id);
    let rights = parse_rights(rights);
    let ia = InspectAct::build(&s.world, InspectFocus::Cell(id), viewer, rights.clone());
    match ia.send(&mut s.world, message, rights) {
        SendResult::Committed { receipt, reinspected } => {
            s.acts.push((id, message.to_string()));
            Ok(json!({
                "outcome": "committed",
                "cell": short(id.as_bytes()),
                "message": message,
                "receipt": {
                    "turn_hash": short(&receipt.turn_hash),
                    "pre_state": short(&receipt.pre_state_hash),
                    "post_state": short(&receipt.post_state_hash),
                    "computrons": receipt.computrons_used,
                    "actions": receipt.action_count,
                    "timestamp": receipt.timestamp,
                },
                "reinspected": inspectable_json(&reinspected),
            }))
        }
        SendResult::Refused { reason, by_executor } => Ok(json!({
            "outcome": "refused",
            "cell": short(id.as_bytes()),
            "message": message,
            "by_executor": by_executor,
            "site": if by_executor { "the verified executor rejected the turn (a guarantee fired)" } else { "the cap-gate refused before any turn (anti-ghost: required ⊄ held)" },
            "reason": reason,
        })),
    }
}

fn tool_spotter(s: &Session, query: &str, view_as: Option<&str>) -> Value {
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(s.anchors[2]);
    let sp = Spotter::new(&s.world, viewer);
    let hits = sp.search(query);
    json!({
        "query": query,
        "hits": hits.iter().map(|h| json!({
            "cell": short(h.focus.cell().as_bytes()),
            "matched_face": h.matched_kind.slug(),
            "snippet": h.snippet,
            "score": h.score,
        })).collect::<Vec<_>>(),
    })
}

fn tool_graph(s: &Session, kind: &str, format: &str) -> Result<Value, String> {
    match kind {
        "ocap" => {
            let g = OcapGraph::build(&s.world);
            let nodes: Vec<Value> = g.nodes().iter().map(|n| json!({
                "id": short(n.cell.as_bytes()), "balance": n.balance, "lifecycle": n.lifecycle,
                "out": n.out_degree, "in": n.in_degree,
            })).collect();
            let edges: Vec<Value> = g.edges().iter().map(|e| json!({
                "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()),
                "slot": e.slot, "rights": format!("{:?}", e.rights),
            })).collect();
            if format == "dot" {
                let mut dot = String::from("digraph ocap {\n  rankdir=LR; node [shape=box, fontname=monospace];\n");
                for n in g.nodes() {
                    dot.push_str(&format!("  \"{}\" [label=\"{}\\nbal {}\\n{}\"];\n", short(n.cell.as_bytes()), short(n.cell.as_bytes()), n.balance, n.lifecycle));
                }
                for e in g.edges() {
                    dot.push_str(&format!("  \"{}\" -> \"{}\" [label=\"slot {} · {:?}\"];\n", short(e.holder.as_bytes()), short(e.target.as_bytes()), e.slot, e.rights));
                }
                dot.push_str("}\n");
                Ok(json!({ "kind": "ocap", "format": "dot", "dot": dot, "node_count": nodes.len(), "edge_count": edges.len() }))
            } else {
                Ok(json!({ "kind": "ocap", "nodes": nodes, "edges": edges }))
            }
        }
        "affordance" => {
            // object → message → effect, for every cell, as the viewer-over-itself
            let mut objs = Vec::new();
            let mut dot = String::from("digraph affordances {\n  rankdir=LR; node [fontname=monospace];\n");
            let ids: Vec<CellId> = s.world.ledger().iter().map(|(id, _)| *id).collect();
            for id in ids {
                let ia = InspectAct::build(&s.world, InspectFocus::Cell(id), id, AuthRequired::Either);
                let node = short(id.as_bytes());
                dot.push_str(&format!("  \"{node}\" [shape=box, style=filled, fillcolor=\"#eef\"];\n"));
                let msgs: Vec<Value> = ia.messages.iter().map(|m| {
                    let tag = format!("{node}:{}", m.name);
                    dot.push_str(&format!("  \"{tag}\" [shape=ellipse, label=\"{} → {}\", color={}];\n", m.name, m.effect, if m.authorized { "green" } else { "red" }));
                    dot.push_str(&format!("  \"{node}\" -> \"{tag}\";\n"));
                    json!({ "message": m.name, "effect": m.effect, "authorized": m.authorized, "required": format!("{:?}", m.required) })
                }).collect();
                objs.push(json!({ "cell": node, "messages": msgs }));
            }
            dot.push_str("}\n");
            if format == "dot" { Ok(json!({ "kind": "affordance", "format": "dot", "dot": dot })) }
            else { Ok(json!({ "kind": "affordance", "objects": objs })) }
        }
        "interactions" => {
            // this session's navigation + act trail — the manual's "what an agent did"
            let mut dot = String::from("digraph session {\n  rankdir=TB; node [fontname=monospace, shape=box];\n");
            for (i, c) in s.visited.iter().enumerate() {
                dot.push_str(&format!("  \"v{i}\" [label=\"inspect {}\", style=filled, fillcolor=\"#eef\"];\n", short(c.as_bytes())));
                if i > 0 { dot.push_str(&format!("  \"v{}\" -> \"v{i}\";\n", i - 1)); }
            }
            for (i, (c, m)) in s.acts.iter().enumerate() {
                dot.push_str(&format!("  \"a{i}\" [label=\"act {} · {}\", shape=ellipse, color=green];\n", short(c.as_bytes()), m));
            }
            dot.push_str("}\n");
            Ok(json!({
                "kind": "interactions",
                "format": if format == "dot" { "dot" } else { "json" },
                "dot": if format == "dot" { Some(dot) } else { None },
                "visited": s.visited.iter().map(|c| short(c.as_bytes())).collect::<Vec<_>>(),
                "acts": s.acts.iter().map(|(c, m)| json!({ "cell": short(c.as_bytes()), "message": m })).collect::<Vec<_>>(),
            }))
        }
        other => Err(format!("unknown graph kind `{other}` (ocap | affordance | interactions)")),
    }
}

fn tool_render_html(s: &mut Session, cell: &str, out: Option<&str>) -> Result<Value, String> {
    let id = s.resolve(cell).ok_or_else(|| format!("no cell matched `{cell}`"))?;
    let reg = Registry::new(&s.world);
    let set = reg
        .present(FocusTarget::Cell(id), id)
        .ok_or_else(|| format!("cell {} absent", short(id.as_bytes())))?;
    let ia = InspectAct::build(&s.world, InspectFocus::Cell(id), id, AuthRequired::Either);

    let mut h = String::new();
    h.push_str("<!doctype html><meta charset=utf-8><title>dregg inspector</title><style>");
    h.push_str("body{background:#0d1117;color:#c9d1d9;font:13px ui-monospace,Menlo,monospace;margin:0;padding:16px}");
    h.push_str("h1{font-size:16px;color:#58a6ff;margin:0 0 2px}h2{font-size:13px;color:#7ee787;border-bottom:1px solid #21262d;padding-bottom:4px;margin:18px 0 6px}");
    h.push_str(".sub{color:#8b949e;margin-bottom:8px}table{border-collapse:collapse;width:100%}td{padding:2px 8px;border-bottom:1px solid #161b22;vertical-align:top}");
    h.push_str(".k{color:#8b949e;width:30%}.bal{color:#f0883e}.id{color:#58a6ff}.ok{color:#3fb950}.no{color:#f85149}.pre{white-space:pre-wrap;color:#a5d6ff}");
    h.push_str("</style>");
    let insp_title = ia.inspectable.as_ref().map(|i| i.title.clone()).unwrap_or_else(|| short(id.as_bytes()));
    h.push_str(&format!("<h1>{}</h1><div class=sub>{} · viewer-over-self</div>", html_esc(&insp_title), short(id.as_bytes())));

    // affordances first (the act surface)
    h.push_str("<h2>affordances · messages it understands</h2><table>");
    for m in &ia.messages {
        let badge = if m.authorized { "<span class=ok>● may send</span>" } else { "<span class=no>○ refused</span>" };
        h.push_str(&format!("<tr><td class=k>{}</td><td>{} <span class=sub>({}, {:?})</span></td><td>{}</td></tr>", html_esc(&m.name), html_esc(&m.effect), "", m.required, badge));
    }
    h.push_str("</table>");

    // each presentation face
    for p in &set {
        h.push_str(&format!("<h2>{} · {}</h2>", p.kind.slug(), html_esc(&p.label)));
        h.push_str(&render_body_html(&p.body));
    }
    h.push_str(&format!("<p class=sub>generated by dregg-mcp · {} faces</p>", set.len()));

    let path = out.map(|s| s.to_string()).unwrap_or_else(|| format!("/tmp/dregg-inspect-{}.html", short(id.as_bytes()).replace('…', "_")));
    std::fs::write(&path, h).map_err(|e| format!("write {path}: {e}"))?;
    Ok(json!({ "path": path, "cell": short(id.as_bytes()), "faces": set.len(), "hint": "open in a browser, or pass to screenshot tooling" }))
}

fn render_body_html(b: &PresentationBody) -> String {
    match b {
        PresentationBody::Fields(i) => {
            let mut t = String::from("<table>");
            for f in &i.fields {
                let v = match &f.value {
                    FieldValue::Balance(n) => format!("<span class=bal>{n}</span>"),
                    FieldValue::Id(id) | FieldValue::Hash(id) => format!("<span class=id>{}</span>", short(id)),
                    FieldValue::Count(n) => n.to_string(),
                    FieldValue::Bool(b) => b.to_string(),
                    FieldValue::Text(s) => html_esc(s),
                    FieldValue::CapEdge { target, slot } => format!("→ <span class=id>{}</span> slot {slot}", short(target)),
                    FieldValue::FieldSlot { index, hex } => format!("[{index}] {hex}"),
                };
                t.push_str(&format!("<tr><td class=k>{}</td><td>{v}</td></tr>", html_esc(&f.key)));
            }
            t.push_str("</table>");
            t
        }
        PresentationBody::Graph(g) => {
            let mut t = String::from("<table>");
            for e in &g.edges {
                t.push_str(&format!("<tr><td class=id>{}</td><td>→ <span class=id>{}</span> slot {} · {:?}</td></tr>", short(e.holder.as_bytes()), short(e.target.as_bytes()), e.slot, e.rights));
            }
            t.push_str("</table>");
            t
        }
        PresentationBody::Prose(p) => format!("<div class=pre>{}</div>", html_esc(p)),
        PresentationBody::Timeline(tl) => {
            let mut t = String::from("<table>");
            for e in &tl.events { t.push_str(&format!("<tr><td class=k>@{}</td><td>{}</td></tr>", e.at, html_esc(&e.label))); }
            t.push_str("</table>"); t
        }
        PresentationBody::Gauge(g) => format!("<div>{}: <span class=bal>{}</span>{}</div>", html_esc(&g.label), g.value, g.ceiling.map(|c| format!(" / {c}")).unwrap_or_default()),
        PresentationBody::StateMachine(sm) => {
            let mut t = format!("<div>current: <b>{}</b></div><table>", html_esc(&sm.current));
            for tr in &sm.transitions { t.push_str(&format!("<tr><td class=k>{} → {}</td><td>{}</td></tr>", html_esc(&tr.from), html_esc(&tr.to), html_esc(&tr.verb))); }
            t.push_str("</table>"); t
        }
        other => format!("<div class=pre>{}</div>", html_esc(&format!("{other:?}"))),
    }
}

fn html_esc(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

/// Bake a real cockpit PNG over THIS session's driven state, via the
/// `headless-render` subprocess (replaying the committed act-trail). `size` is a
/// logical `WxH` (default 1280x832 — the full cockpit, no truncation; pass
/// `800x600` for the seL4-framebuffer geometry). `tab` selects a surface.
fn tool_screenshot(s: &Session, out: Option<&str>, size: Option<&str>, tab: Option<&str>) -> Result<Value, String> {
    let out = out.unwrap_or("/tmp/dregg-cockpit").to_string();
    let size = size.unwrap_or("1280x832");
    // Locate the headless-render binary next to this one (target/release/).
    let bin = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|d| d.join("starbridge-v2")))
        .filter(|p| p.exists())
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| "target/release/starbridge-v2".to_string());

    let mut cmd = std::process::Command::new(&bin);
    cmd.arg("--render-cockpit").arg(&out);
    cmd.arg("--render-size").arg(size);
    if let Some(t) = tab {
        cmd.arg("--render-tab").arg(t);
    }
    for (cell, msg) in &s.acts {
        cmd.arg("--replay").arg(format!("{}:{}", hex32(cell.as_bytes()), msg));
    }
    cmd.env("ZED_OFFSCREEN_PREFER_CPU", "1");
    let output = cmd.output().map_err(|e| format!("spawn {bin}: {e} (build it: cd starbridge-v2 && cargo build --release --features headless-render)"))?;
    let png = format!("{out}.png");
    if std::path::Path::new(&png).exists() {
        Ok(json!({
            "png": png,
            "size": size,
            "tab": tab,
            "replayed_acts": s.acts.len(),
            "note": String::from_utf8_lossy(&output.stdout).trim().to_string(),
        }))
    } else {
        Err(format!("render produced no PNG. stderr: {}", String::from_utf8_lossy(&output.stderr)))
    }
}

/// Rewind the world to a prefix of the act-trail — reboot the image and replay
/// the first `to` committed acts. The backtracking primitive the game-tree crawl
/// needs (try an action, rewind, try the next). `to` defaults to 0 (full reset).
fn tool_rewind(s: &mut Session, to: usize) -> Value {
    let keep: Vec<(CellId, String)> = s.acts.iter().take(to).cloned().collect();
    let image = s.image.clone();
    *s = Session::boot(&image);
    let mut replayed = 0usize;
    for (cell, msg) in &keep {
        if s.apply_act(*cell, msg) {
            replayed += 1;
        }
    }
    json!({
        "rewound_to": replayed,
        "requested": to,
        "acts_now": s.acts.len(),
        "cell_count": s.world.ledger().iter().count(),
        "note": "the world was re-seeded and the act-prefix replayed — game-tree backtrack point",
    })
}

/// The full crawl dump for the atlas site-builder: meta + every cell's faces +
/// affordances + halo + the ocap graph + the session act-trail, as ONE JSON
/// object written to `out`. The exhaustive snapshot the builder ingests.
fn tool_export(s: &Session, out: Option<&str>) -> Result<Value, String> {
    let path = out.unwrap_or("/tmp/dregg-atlas-export.json").to_string();
    let reg = Registry::new(&s.world);
    let mut cells = Vec::new();
    for (id, _) in s.world.ledger().iter() {
        let viewer = *id;
        let faces = reg.present(FocusTarget::Cell(*id), viewer).unwrap_or_default();
        let halo = reg.halo(FocusTarget::Cell(*id));
        let ia = InspectAct::build(&s.world, InspectFocus::Cell(*id), viewer, AuthRequired::Either);
        cells.push(json!({
            "id": hex32(id.as_bytes()),
            "short": short(id.as_bytes()),
            "halo": halo.commands.iter().map(halo_label).collect::<Vec<_>>(),
            "faces": faces.iter().map(presentation_json).collect::<Vec<_>>(),
            "affordances": ia.messages.iter().map(|m| json!({
                "name": m.name, "effect": m.effect,
                "required": format!("{:?}", m.required), "authorized": m.authorized,
            })).collect::<Vec<_>>(),
        }));
    }
    let g = OcapGraph::build(&s.world);
    let blob = json!({
        "image": s.image,
        "cell_count": s.world.ledger().iter().count(),
        "anchors": { "treasury": hex32(s.anchors[0].as_bytes()), "service": hex32(s.anchors[1].as_bytes()), "user": hex32(s.anchors[2].as_bytes()) },
        "cells": cells,
        "ocap": {
            "nodes": g.nodes().iter().map(|n| json!({ "id": short(n.cell.as_bytes()), "balance": n.balance, "lifecycle": n.lifecycle, "out": n.out_degree, "in": n.in_degree })).collect::<Vec<_>>(),
            "edges": g.edges().iter().map(|e| json!({ "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()), "slot": e.slot, "rights": format!("{:?}", e.rights) })).collect::<Vec<_>>(),
        },
        "acts": s.acts.iter().map(|(c, m)| json!({ "cell": hex32(c.as_bytes()), "message": m })).collect::<Vec<_>>(),
    });
    std::fs::write(&path, serde_json::to_string_pretty(&blob).unwrap_or_default())
        .map_err(|e| format!("write {path}: {e}"))?;
    Ok(json!({ "path": path, "cells": cells.len(), "hint": "feed to the dregg-atlas site builder" }))
}

/// The protocol reference surface: the AuthRequired lattice + the effect/verb
/// vocabulary seen across the live world's affordances + the refusal taxonomy.
fn tool_protocol(s: &Session) -> Value {
    // collect the distinct effects + required tiers seen across all affordances
    let mut effects = std::collections::BTreeSet::new();
    let mut tiers = std::collections::BTreeSet::new();
    for (id, _) in s.world.ledger().iter() {
        let ia = InspectAct::build(&s.world, InspectFocus::Cell(*id), *id, AuthRequired::Either);
        for m in &ia.messages {
            effects.insert(m.effect.clone());
            tiers.insert(format!("{:?}", m.required));
        }
    }
    json!({
        "auth_required_lattice": {
            "order": "Impossible ⊏ {Signature, Proof} ⊏ Either ⊏ None (None is the TOP/widest)",
            "tiers": ["None", "Signature", "Proof", "Either", "Impossible", "Custom{vk_hash}"],
            "note": "is_attenuation(held, req) = req.is_narrower_or_equal(held); see the None cap-badge anomaly in HORIZONLOG",
        },
        "effects_seen": effects.into_iter().collect::<Vec<_>>(),
        "required_tiers_seen": tiers.into_iter().collect::<Vec<_>>(),
        "refusal_taxonomy": {
            "cap_gate": "by_executor=false — required ⊄ held, refused before any turn (the anti-ghost tooth)",
            "executor": "by_executor=true — a kernel guarantee fired (conservation, non-amplification, a permissions gate)",
        },
        "the_eight_verbs": ["Transfer", "SetField", "GrantCapability", "RevokeCapability", "IncrementNonce/touch", "EmitEvent/peek", "CreateCell", "the cap-write family (attenuate/revoke/delegate)"],
    })
}

fn tool_view(s: &Session) -> Value {
    json!({
        "image": "starbridge-v2 live verified ocap world",
        "cell_count": s.world.ledger().iter().count(),
        "anchors": { "treasury": short(s.anchors[0].as_bytes()), "service": short(s.anchors[1].as_bytes()), "user": short(s.anchors[2].as_bytes()) },
        "acts_committed": s.acts.len(),
        "cells_visited": s.visited.len(),
    })
}

// ===========================================================================
// MCP tool registry + dispatch
// ===========================================================================

fn tool_schemas() -> Value {
    let str_prop = |desc: &str| json!({ "type": "string", "description": desc });
    json!([
        { "name": "boot", "description": "(Re)boot the session world. image: 'demo' (fully-seeded sovereign image, default) | 'empty'. Returns the cell roster.",
          "inputSchema": { "type": "object", "properties": { "image": str_prop("demo|empty") } } },
        { "name": "survey", "description": "List every cell in the live ledger (id, kind, title, balance, cap-edges) — the top of the inspectable tree.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "inspect", "description": "Open a cell's SEVEN presentation faces (raw-fields, graph, affordances, provenance, invariant, source, domain-visual) + its halo ring, as structured JSON — the reflective inspect-element.",
          "inputSchema": { "type": "object", "properties": { "cell": str_prop("id | short-id | treasury|service|user"), "as": str_prop("inspect AS this principal (default: the cell itself)"), "rights": str_prop("none|signature|either|locked") }, "required": ["cell"] } },
        { "name": "affordances", "description": "The messages a cell understands, each with its real effect + cap badge (authorized? for the viewer). Anti-ghost: refused messages are shown, not hidden.",
          "inputSchema": { "type": "object", "properties": { "cell": str_prop("cell handle"), "as": str_prop("view as principal"), "rights": str_prop("viewer rights") }, "required": ["cell"] } },
        { "name": "act", "description": "FIRE a message on a cell — a real cap-gated turn through the verified executor. Returns the receipt + reinspected post-state, or the in-band refusal (cap-gate vs executor). This mutates the live world.",
          "inputSchema": { "type": "object", "properties": { "cell": str_prop("cell handle"), "message": str_prop("e.g. peek|touch|write|grant"), "as": str_prop("act as principal"), "rights": str_prop("viewer rights") }, "required": ["cell", "message"] } },
        { "name": "spotter", "description": "Fuzzy-search every object's every presentation face (the ⌘K palette). Returns ranked hits.",
          "inputSchema": { "type": "object", "properties": { "query": str_prop("search text"), "as": str_prop("viewer") }, "required": ["query"] } },
        { "name": "graph", "description": "Emit an interaction map. kind: 'ocap' (the capability web) | 'affordance' (object→message→effect) | 'interactions' (this session's nav+act trail). format: 'json' | 'dot' (Graphviz).",
          "inputSchema": { "type": "object", "properties": { "kind": str_prop("ocap|affordance|interactions"), "format": str_prop("json|dot") }, "required": ["kind"] } },
        { "name": "render", "description": "Render a cell's full inspector view to a self-contained dark-theme HTML file (the portable, annotatable Firebug DOM). Returns the path.",
          "inputSchema": { "type": "object", "properties": { "cell": str_prop("cell handle"), "out": str_prop("output .html path") }, "required": ["cell"] } },
        { "name": "screenshot", "description": "Bake the REAL gpui Cockpit element tree (over this session's driven state — replays the committed act-trail) to a PNG via the headless render subprocess. size: logical WxH (default 1280x832 = full cockpit, no truncation; 800x600 = seL4 framebuffer geometry). tab: which surface (home|inspector|graph|proofs|objects|debugger|replay|web-of-cells|wonder|workspace|inspect-act|trust|docs|…). Returns the PNG path.",
          "inputSchema": { "type": "object", "properties": { "out": str_prop("output path stem (default /tmp/dregg-cockpit)"), "size": str_prop("logical WxH, e.g. 1280x832 or 1600x1000"), "tab": str_prop("cockpit surface name") } } },
        { "name": "rewind", "description": "Backtrack the world to a prefix of the act-trail (reboot + replay the first `to` committed acts). The game-tree backtracking primitive: try an action, rewind, try the next. `to`=0 fully resets.",
          "inputSchema": { "type": "object", "properties": { "to": { "type": "integer", "description": "keep the first N committed acts (0 = reset)" } } } },
        { "name": "export", "description": "Dump the FULL crawl (meta + every cell's faces/affordances/halo + the ocap graph + the act-trail) as one JSON file for the atlas site-builder.",
          "inputSchema": { "type": "object", "properties": { "out": str_prop("output .json path") } } },
        { "name": "protocol", "description": "The protocol reference: the AuthRequired lattice, the effect/verb vocabulary seen live, and the refusal taxonomy (cap-gate vs executor).",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "view", "description": "Describe the current session: cell count, anchors, acts committed, cells visited.",
          "inputSchema": { "type": "object", "properties": {} } },
    ])
}

fn dispatch(s: &mut Session, name: &str, args: &Value) -> Result<Value, String> {
    let str_arg = |k: &str| args.get(k).and_then(|v| v.as_str());
    match name {
        "boot" => {
            *s = Session::boot(str_arg("image").unwrap_or("demo"));
            Ok(tool_survey(s))
        }
        "survey" => Ok(tool_survey(s)),
        "inspect" => tool_inspect(s, str_arg("cell").ok_or("missing `cell`")?, str_arg("as"), str_arg("rights")),
        "affordances" => tool_affordances(s, str_arg("cell").ok_or("missing `cell`")?, str_arg("as"), str_arg("rights")),
        "act" => tool_act(s, str_arg("cell").ok_or("missing `cell`")?, str_arg("message").ok_or("missing `message`")?, str_arg("as"), str_arg("rights")),
        "spotter" => Ok(tool_spotter(s, str_arg("query").ok_or("missing `query`")?, str_arg("as"))),
        "graph" => tool_graph(s, str_arg("kind").ok_or("missing `kind`")?, str_arg("format").unwrap_or("json")),
        "render" => tool_render_html(s, str_arg("cell").ok_or("missing `cell`")?, str_arg("out")),
        "screenshot" => tool_screenshot(s, str_arg("out"), str_arg("size"), str_arg("tab")),
        "rewind" => Ok(tool_rewind(s, args.get("to").and_then(|v| v.as_u64()).unwrap_or(0) as usize)),
        "export" => tool_export(s, str_arg("out")),
        "protocol" => Ok(tool_protocol(s)),
        "view" => Ok(tool_view(s)),
        other => Err(format!("unknown tool `{other}`")),
    }
}

// ===========================================================================
// JSON-RPC 2.0 stdio loop
// ===========================================================================

fn main() {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut session = Session::boot("demo");
    eprintln!("dregg-mcp: live verified image up ({} cells)", session.world.ledger().iter().count());

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) if !l.trim().is_empty() => l,
            Ok(_) => continue,
            Err(_) => break,
        };
        let req: Value = match serde_json::from_str(&line) {
            Ok(v) => v,
            Err(e) => {
                let _ = writeln!(stdout, "{}", json!({ "jsonrpc": "2.0", "id": null, "error": { "code": -32700, "message": format!("parse error: {e}") } }));
                let _ = stdout.flush();
                continue;
            }
        };
        let id = req.get("id").cloned();
        let method = req.get("method").and_then(|m| m.as_str()).unwrap_or("");
        let params = req.get("params").cloned().unwrap_or(json!({}));

        // Notifications (no id) — acknowledge by doing nothing.
        if id.is_none() {
            continue;
        }
        let id = id.unwrap();

        let result: Result<Value, (i64, String)> = match method {
            "initialize" => Ok(json!({
                "protocolVersion": "2024-11-05",
                "capabilities": { "tools": { "listChanged": false } },
                "serverInfo": { "name": "dregg-mcp", "version": "0.1.0" },
                "instructions": "Drives the starbridge-v2 live verified ocap image. Start with `survey`, then `inspect <cell>`, `affordances`, `act <cell> <message>`. `graph` maps the ocap/affordance/interaction surface; `render` makes an HTML inspector page; `screenshot` bakes the real cockpit PNG.",
            })),
            "tools/list" => Ok(json!({ "tools": tool_schemas() })),
            "tools/call" => {
                let tname = params.get("name").and_then(|n| n.as_str()).unwrap_or("");
                let targs = params.get("arguments").cloned().unwrap_or(json!({}));
                match dispatch(&mut session, tname, &targs) {
                    Ok(v) => Ok(json!({ "content": [ { "type": "text", "text": serde_json::to_string_pretty(&v).unwrap_or_default() } ] })),
                    Err(e) => Ok(json!({ "content": [ { "type": "text", "text": format!("error: {e}") } ], "isError": true })),
                }
            }
            "ping" => Ok(json!({})),
            other => Err((-32601, format!("method not found: {other}"))),
        };

        let resp = match result {
            Ok(r) => json!({ "jsonrpc": "2.0", "id": id, "result": r }),
            Err((code, msg)) => json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": msg } }),
        };
        let _ = writeln!(stdout, "{resp}");
        let _ = stdout.flush();
    }
}
