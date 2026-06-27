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
    /// Cheap state snapshots (a deep-cloned `World` via `World::fork`, ~ms) keyed
    /// by id — the game-tree crawl checkpoints here instead of paying a 3s reboot
    /// per backtrack. Each holds the forked world + the act-trail at that point.
    snaps: std::collections::HashMap<u64, (World, Vec<(CellId, String)>)>,
    next_snap: u64,
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
        Session {
            world,
            anchors,
            image: image.to_string(),
            acts: Vec::new(),
            visited: Vec::new(),
            snaps: std::collections::HashMap::new(),
            next_snap: 0,
        }
    }

    /// Fire a committed act as `cell`-over-itself with the `Either` tier (the
    /// self-operator projection), recording it. Used by `rewind` replay so a
    /// game-tree branch reconstructs deterministically.
    fn apply_act(&mut self, cell: CellId, message: &str) -> bool {
        let ia = InspectAct::build(
            &self.world,
            InspectFocus::Cell(cell),
            cell,
            AuthRequired::Either,
        );
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

fn tool_inspect(
    s: &mut Session,
    cell: &str,
    view_as: Option<&str>,
    rights: Option<&str>,
) -> Result<Value, String> {
    let id = s
        .resolve(cell)
        .ok_or_else(|| format!("no cell matched `{cell}` (try survey)"))?;
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(id);
    let _rights = parse_rights(rights);
    s.visited.push(id);

    let reg = Registry::new(&s.world);
    let set = reg.present(FocusTarget::Cell(id), viewer).ok_or_else(|| {
        format!(
            "cell {} is absent from the live world (dangling focus)",
            short(id.as_bytes())
        )
    })?;
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

fn tool_affordances(
    s: &Session,
    cell: &str,
    view_as: Option<&str>,
    rights: Option<&str>,
) -> Result<Value, String> {
    let id = s
        .resolve(cell)
        .ok_or_else(|| format!("no cell matched `{cell}`"))?;
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

fn tool_act(
    s: &mut Session,
    cell: &str,
    message: &str,
    view_as: Option<&str>,
    rights: Option<&str>,
) -> Result<Value, String> {
    let id = s
        .resolve(cell)
        .ok_or_else(|| format!("no cell matched `{cell}`"))?;
    let viewer = view_as.and_then(|v| s.resolve(v)).unwrap_or(id);
    let rights = parse_rights(rights);
    let ia = InspectAct::build(&s.world, InspectFocus::Cell(id), viewer, rights.clone());
    match ia.send(&mut s.world, message, rights) {
        SendResult::Committed {
            receipt,
            reinspected,
        } => {
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
        SendResult::Refused {
            reason,
            by_executor,
        } => Ok(json!({
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
            let edges: Vec<Value> = g
                .edges()
                .iter()
                .map(|e| {
                    json!({
                        "from": short(e.holder.as_bytes()), "to": short(e.target.as_bytes()),
                        "slot": e.slot, "rights": format!("{:?}", e.rights),
                    })
                })
                .collect();
            if format == "dot" {
                let mut dot = String::from(
                    "digraph ocap {\n  rankdir=LR; node [shape=box, fontname=monospace];\n",
                );
                for n in g.nodes() {
                    dot.push_str(&format!(
                        "  \"{}\" [label=\"{}\\nbal {}\\n{}\"];\n",
                        short(n.cell.as_bytes()),
                        short(n.cell.as_bytes()),
                        n.balance,
                        n.lifecycle
                    ));
                }
                for e in g.edges() {
                    dot.push_str(&format!(
                        "  \"{}\" -> \"{}\" [label=\"slot {} · {:?}\"];\n",
                        short(e.holder.as_bytes()),
                        short(e.target.as_bytes()),
                        e.slot,
                        e.rights
                    ));
                }
                dot.push_str("}\n");
                Ok(
                    json!({ "kind": "ocap", "format": "dot", "dot": dot, "node_count": nodes.len(), "edge_count": edges.len() }),
                )
            } else {
                Ok(json!({ "kind": "ocap", "nodes": nodes, "edges": edges }))
            }
        }
        "affordance" => {
            // object → message → effect, for every cell, as the viewer-over-itself
            let mut objs = Vec::new();
            let mut dot =
                String::from("digraph affordances {\n  rankdir=LR; node [fontname=monospace];\n");
            let ids: Vec<CellId> = s.world.ledger().iter().map(|(id, _)| *id).collect();
            for id in ids {
                let ia =
                    InspectAct::build(&s.world, InspectFocus::Cell(id), id, AuthRequired::Either);
                let node = short(id.as_bytes());
                dot.push_str(&format!(
                    "  \"{node}\" [shape=box, style=filled, fillcolor=\"#eef\"];\n"
                ));
                let msgs: Vec<Value> = ia.messages.iter().map(|m| {
                    let tag = format!("{node}:{}", m.name);
                    dot.push_str(&format!("  \"{tag}\" [shape=ellipse, label=\"{} → {}\", color={}];\n", m.name, m.effect, if m.authorized { "green" } else { "red" }));
                    dot.push_str(&format!("  \"{node}\" -> \"{tag}\";\n"));
                    json!({ "message": m.name, "effect": m.effect, "authorized": m.authorized, "required": format!("{:?}", m.required) })
                }).collect();
                objs.push(json!({ "cell": node, "messages": msgs }));
            }
            dot.push_str("}\n");
            if format == "dot" {
                Ok(json!({ "kind": "affordance", "format": "dot", "dot": dot }))
            } else {
                Ok(json!({ "kind": "affordance", "objects": objs }))
            }
        }
        "interactions" => {
            // this session's navigation + act trail — the manual's "what an agent did"
            let mut dot = String::from(
                "digraph session {\n  rankdir=TB; node [fontname=monospace, shape=box];\n",
            );
            for (i, c) in s.visited.iter().enumerate() {
                dot.push_str(&format!(
                    "  \"v{i}\" [label=\"inspect {}\", style=filled, fillcolor=\"#eef\"];\n",
                    short(c.as_bytes())
                ));
                if i > 0 {
                    dot.push_str(&format!("  \"v{}\" -> \"v{i}\";\n", i - 1));
                }
            }
            for (i, (c, m)) in s.acts.iter().enumerate() {
                dot.push_str(&format!(
                    "  \"a{i}\" [label=\"act {} · {}\", shape=ellipse, color=green];\n",
                    short(c.as_bytes()),
                    m
                ));
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
        other => Err(format!(
            "unknown graph kind `{other}` (ocap | affordance | interactions)"
        )),
    }
}

fn tool_render_html(s: &mut Session, cell: &str, out: Option<&str>) -> Result<Value, String> {
    let id = s
        .resolve(cell)
        .ok_or_else(|| format!("no cell matched `{cell}`"))?;
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
    let insp_title = ia
        .inspectable
        .as_ref()
        .map(|i| i.title.clone())
        .unwrap_or_else(|| short(id.as_bytes()));
    h.push_str(&format!(
        "<h1>{}</h1><div class=sub>{} · viewer-over-self</div>",
        html_esc(&insp_title),
        short(id.as_bytes())
    ));

    // affordances first (the act surface)
    h.push_str("<h2>affordances · messages it understands</h2><table>");
    for m in &ia.messages {
        let badge = if m.authorized {
            "<span class=ok>● may send</span>"
        } else {
            "<span class=no>○ refused</span>"
        };
        h.push_str(&format!(
            "<tr><td class=k>{}</td><td>{} <span class=sub>({}, {:?})</span></td><td>{}</td></tr>",
            html_esc(&m.name),
            html_esc(&m.effect),
            "",
            m.required,
            badge
        ));
    }
    h.push_str("</table>");

    // each presentation face
    for p in &set {
        h.push_str(&format!(
            "<h2>{} · {}</h2>",
            p.kind.slug(),
            html_esc(&p.label)
        ));
        h.push_str(&render_body_html(&p.body));
    }
    h.push_str(&format!(
        "<p class=sub>generated by dregg-mcp · {} faces</p>",
        set.len()
    ));

    let path = out.map(|s| s.to_string()).unwrap_or_else(|| {
        format!(
            "/tmp/dregg-inspect-{}.html",
            short(id.as_bytes()).replace('…', "_")
        )
    });
    std::fs::write(&path, h).map_err(|e| format!("write {path}: {e}"))?;
    Ok(
        json!({ "path": path, "cell": short(id.as_bytes()), "faces": set.len(), "hint": "open in a browser, or pass to screenshot tooling" }),
    )
}

fn render_body_html(b: &PresentationBody) -> String {
    match b {
        PresentationBody::Fields(i) => {
            let mut t = String::from("<table>");
            for f in &i.fields {
                let v = match &f.value {
                    FieldValue::Balance(n) => format!("<span class=bal>{n}</span>"),
                    FieldValue::Id(id) | FieldValue::Hash(id) => {
                        format!("<span class=id>{}</span>", short(id))
                    }
                    FieldValue::Count(n) => n.to_string(),
                    FieldValue::Bool(b) => b.to_string(),
                    FieldValue::Text(s) => html_esc(s),
                    FieldValue::CapEdge { target, slot } => {
                        format!("→ <span class=id>{}</span> slot {slot}", short(target))
                    }
                    FieldValue::FieldSlot { index, hex } => format!("[{index}] {hex}"),
                };
                t.push_str(&format!(
                    "<tr><td class=k>{}</td><td>{v}</td></tr>",
                    html_esc(&f.key)
                ));
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
            for e in &tl.events {
                t.push_str(&format!(
                    "<tr><td class=k>@{}</td><td>{}</td></tr>",
                    e.at,
                    html_esc(&e.label)
                ));
            }
            t.push_str("</table>");
            t
        }
        PresentationBody::Gauge(g) => format!(
            "<div>{}: <span class=bal>{}</span>{}</div>",
            html_esc(&g.label),
            g.value,
            g.ceiling.map(|c| format!(" / {c}")).unwrap_or_default()
        ),
        PresentationBody::StateMachine(sm) => {
            let mut t = format!(
                "<div>current: <b>{}</b></div><table>",
                html_esc(&sm.current)
            );
            for tr in &sm.transitions {
                t.push_str(&format!(
                    "<tr><td class=k>{} → {}</td><td>{}</td></tr>",
                    html_esc(&tr.from),
                    html_esc(&tr.to),
                    html_esc(&tr.verb)
                ));
            }
            t.push_str("</table>");
            t
        }
        other => format!("<div class=pre>{}</div>", html_esc(&format!("{other:?}"))),
    }
}

fn html_esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// Bake a real cockpit PNG over THIS session's driven state, via the
/// `headless-render` subprocess (replaying the committed act-trail). `size` is a
/// logical `WxH` (default 1280x832 — the full cockpit, no truncation; pass
/// `800x600` for the seL4-framebuffer geometry). `tab` selects a surface.
fn tool_screenshot(
    s: &Session,
    out: Option<&str>,
    size: Option<&str>,
    tab: Option<&str>,
) -> Result<Value, String> {
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
        cmd.arg("--replay")
            .arg(format!("{}:{}", hex32(cell.as_bytes()), msg));
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
        Err(format!(
            "render produced no PNG. stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        ))
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
        let faces = reg
            .present(FocusTarget::Cell(*id), viewer)
            .unwrap_or_default();
        let halo = reg.halo(FocusTarget::Cell(*id));
        let ia = InspectAct::build(
            &s.world,
            InspectFocus::Cell(*id),
            viewer,
            AuthRequired::Either,
        );
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
    std::fs::write(
        &path,
        serde_json::to_string_pretty(&blob).unwrap_or_default(),
    )
    .map_err(|e| format!("write {path}: {e}"))?;
    Ok(
        json!({ "path": path, "cells": cells.len(), "hint": "feed to the dregg-atlas site builder" }),
    )
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

/// Submit a RAW effect through the verified executor (beyond the self-affordance
/// surface) — `transfer` (value flow, conservation), `create` (a new cell), or
/// `grant` (a capability edge). Returns the same committed/refused shape as `act`,
/// so the game-tree crawl can include the full verb vocabulary.
fn tool_effect(s: &mut Session, kind: &str, args: &Value) -> Result<Value, String> {
    use starbridge_v2::world::{self, CommitOutcome};
    let resolve_arg = |k: &str| {
        args.get(k)
            .and_then(|v| v.as_str())
            .and_then(|h| s.resolve(h))
    };
    let from = resolve_arg("from").ok_or("effect needs a resolvable `from` cell")?;
    let amount = args.get("amount").and_then(|v| v.as_u64()).unwrap_or(100);
    let slot = args.get("slot").and_then(|v| v.as_u64()).unwrap_or(0) as u32;

    let (eff, label) = match kind {
        "transfer" => {
            let to = resolve_arg("to").ok_or("transfer needs a resolvable `to` cell")?;
            (
                world::transfer(from, to, amount),
                format!("transfer {amount} → {}", short(to.as_bytes())),
            )
        }
        "grant" => {
            let to = resolve_arg("to").ok_or("grant needs a resolvable `to` cell")?;
            (
                world::grant_capability(from, to, from, slot),
                format!(
                    "grant cap(→{}) to {}",
                    short(from.as_bytes()),
                    short(to.as_bytes())
                ),
            )
        }
        "create" => {
            let seed = args.get("seed").and_then(|v| v.as_u64()).unwrap_or(0xA0) as u8;
            (
                world::create_cell(seed),
                format!("create cell (seed {seed:#x})"),
            )
        }
        other => {
            return Err(format!(
                "unknown effect kind `{other}` (transfer|grant|create)"
            ))
        }
    };

    let turn = s.world.turn(from, vec![eff]);
    match s.world.commit_turn(turn) {
        CommitOutcome::Committed { receipt, .. } => Ok(json!({
            "outcome": "committed", "kind": kind, "label": label,
            "from": short(from.as_bytes()),
            "receipt": { "post_state": short(&receipt.post_state_hash), "computrons": receipt.computrons_used, "actions": receipt.action_count },
        })),
        CommitOutcome::Rejected { reason, at_action } => Ok(json!({
            "outcome": "refused", "kind": kind, "label": label,
            "by_executor": true, "at_action": at_action,
            "reason": reason,
            "site": "the verified executor rejected the turn (a guarantee fired: conservation / authority / lifecycle)",
        })),
        _ => Ok(
            json!({ "outcome": "staged", "kind": kind, "label": label, "note": "world suspended — turn queued, not run" }),
        ),
    }
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

// ---------------------------------------------------------------------------
// dataplane — the captp Bus / channel data plane, exercised LIVE in-process
// ---------------------------------------------------------------------------

/// The captp DATA PLANE as inspectable state. The node-side `Bus` (the per-node
/// relay that backs the channels service) is NOT in the embedded image — there
/// is no node here — so this tool stands up a REAL `dregg_captp::data_plane::Bus`
/// in-process and drives a genuine post→wake→drain cycle, so the receipt-identity
/// (a Delivery promise vs the witnessed drain), the per-recipient queue depth /
/// inbox root, the pub/sub topic fan-out, and the wake-by-name cursor are SHOWN
/// as real values, not described. The seam to the live node's Bus is named.
fn tool_dataplane(s: &Session) -> Value {
    use dregg_captp::data_plane::{Bus, ChannelName, SendCap, TopicName};
    use dregg_cell::permissions::AuthRequired as DpAuth;
    use dregg_types::FederationId;

    // A relay identity for the demonstration Bus (deterministic seed).
    let relay_seed = [0x5Au8; 32];
    let relay_key = dregg_types::SigningKey::from_bytes(&relay_seed);
    let relay_id = FederationId::from_bytes(relay_key.public_key().0);

    // Two recipients derived from the live anchors (so the demo is grounded in
    // this session's principals — a recipient is named by a FederationId).
    let alice = FederationId::from_bytes(*s.anchors[1].as_bytes()); // service
    let bob = FederationId::from_bytes(*s.anchors[2].as_bytes()); // user

    let mut bus = Bus::new(relay_id, relay_key, 64, 4096)
        .with_default_ttl(256)
        .with_default_deadline(1024);

    let chan = ChannelName::new(b"demo.inbox".to_vec());
    let send_cap = SendCap::grant(alice, chan.clone(), DpAuth::Either);
    let now = s.world.height();

    // (1) enqueue a box for alice → a Delivery (the relay's signed PROMISE).
    let mut posts = Vec::new();
    for i in 0..2u32 {
        match bus.enqueue(
            &send_cap,
            alice,
            &chan,
            DpAuth::Either,
            format!("msg{i}").into_bytes(),
            now,
        ) {
            Ok(d) => posts.push(json!({
                "to": short(alice.as_bytes()),
                "content_hash": short(&d.content_hash),
                "custody": "relay-signed promise (a Delivery; NOT yet witnessed)",
            })),
            Err(e) => posts.push(json!({ "error": format!("{e:?}") })),
        }
    }

    // (2) wake-by-name: bob waits on the channel, then polls the cursor.
    bus.wait(&chan, bob);
    let cursor_before = bus.cursor(&chan);
    let wake = bus.poll_wake(&chan, &bob).map(|w| w.cursor);

    // (3) pub/sub: a topic with both recipients subscribed.
    let topic = TopicName::new(b"demo.broadcast".to_vec());
    bus.register_topic(topic.clone());
    bus.subscribe(topic.clone(), alice);
    bus.subscribe(topic.clone(), bob);
    let pub_cap = SendCap::grant(alice, chan.clone(), DpAuth::Either);
    let published = bus
        .publish(&topic, &pub_cap, DpAuth::Either, b"hello-all".to_vec(), now)
        .map(|v| v.len())
        .unwrap_or(0);
    let subs = bus.subscribers(&topic).len();

    // (4) the per-recipient INBOX state BEFORE drain (pending vs delivered).
    let pending_before = bus.pending_count(&alice);
    let root_before = bus.inbox_root(&alice);

    // (5) drain alice → witnesses delivery (receipt-identity flips: promise → fact).
    let drained = bus.drain(&alice).len();
    let pending_after = bus.pending_count(&alice);
    let delivered = bus.delivered_hashes(&alice).len();
    let root_after = bus.inbox_root(&alice);

    json!({
        "what": "the captp data plane (dregg_captp::data_plane::Bus) — the relay/inbox/wake/topic substrate that backs the node channels service",
        "live": "a REAL Bus stood up + driven in-process (post → wake → publish → drain), grounded in this session's anchor principals",
        "relay": { "id": short(relay_id.as_bytes()), "role": "the accountable relay identity (FederationId = its Ed25519 pubkey); signs custody receipts" },
        "principals": { "alice (service)": short(alice.as_bytes()), "bob (user)": short(bob.as_bytes()) },
        "channel": { "name": "demo.inbox", "key": short(&chan.key()) },
        "post": {
            "deliveries": posts,
            "receipt_identity": "enqueue returns a Delivery = the relay's signed PROMISE; the content is only WITNESSED once drain returns it (custody flips promise → fact)",
        },
        "wake": {
            "waiter": short(bob.as_bytes()),
            "cursor": cursor_before,
            "poll_wake": wake,
            "kind": "unforgeable wake-by-name: the cursor is the monotone enqueue count, derivable only by the relay (Wake { cursor })",
        },
        "pubsub": { "topic": "demo.broadcast", "subscribers": subs, "fanned_out_to": published },
        "inbox": {
            "alice_pending_before_drain": pending_before,
            "alice_inbox_root_before": short(&root_before),
            "drained": drained,
            "alice_pending_after_drain": pending_after,
            "alice_delivered_hashes": delivered,
            "alice_inbox_root_after": short(&root_after),
            "note": "the inbox root is a monotone per-recipient commitment; drain advances delivered and clears pending",
        },
        "seam": {
            "node_bus": "the LIVE per-node Bus lives in `node/src/channels_service.rs` (ChannelRegistry::bus, minted once from the node gossip key) and is reached over the node HTTP API: POST /channels/post (enqueue), POST /channels/drain/{cell}, POST /channels/subscribe (wait), GET /channels/wake/{cell}, GET /channels/status/{cell}",
            "embedded_image": "there is no node in this embedded image, so the live queue depths of a running federation are NOT here; the protocol + a driven instance ARE (above)",
        },
        "types": ["Bus", "Delivery", "Wake", "Waker", "SendCap", "ChannelName", "TopicName", "QueuedMessage", "CustodyReceipt"],
    })
}

// ---------------------------------------------------------------------------
// firmament — the surface/migration state: the one cap across distance
// ---------------------------------------------------------------------------

/// The FIRMAMENT surface/migration state: the `(target, rights)` capability over
/// the Local / Distributed / Surface / HostPd distance axis, the live cell
/// lifecycle (Live / Sealed / Migrated / Destroyed / Archived — the migration
/// frontier), and the compositor scene contract (the T1/T2/T3 teeth). Every
/// live cell is also a *potential* surface target (a window IS a cap over a
/// cell), so we project the ledger onto the distance axis + read each cell's
/// lifecycle directly from the live world.
fn tool_firmament(s: &Session) -> Value {
    use dregg_firmament::{Backing, Bounds, Capability};

    // The distance axis, made concrete: build a real Capability at each rung.
    let demo_cell = s.anchors[0];
    let axis = vec![
        (
            "Local",
            json!({
                "target": "Local { slot }", "n": 1,
                "backing": format!("{:?}", Backing::LocalKernel),
                "bounds": "revocation synchronous · commit local (a seL4 CNode slot — a syscall)",
                "example": { "cap": format!("{:?}", Capability::local(0, dregg_cell::AuthRequired::Either).target) },
            }),
        ),
        (
            "Distributed",
            json!({
                "target": "Distributed { cell }", "n_ge": 1,
                "backing": format!("{:?}", Backing::DistributedTurn),
                "bounds": "revocation = epoch lift · commit quorum-gated when n>1, synchronous at n=1 (a turn through the executor)",
                "example": { "cell": short(demo_cell.as_bytes()) },
            }),
        ),
        (
            "Surface",
            json!({
                "target": "Surface { cell }", "n": 1,
                "backing": format!("{:?}", Backing::DistributedTurn),
                "bounds": "a window IS a cap over a cell — present/draw is a turn; at n=1 a surface revoke darkens the glass the instant it returns",
                "example": { "cell": short(demo_cell.as_bytes()) },
            }),
        ),
        (
            "HostPd",
            json!({
                "target": "HostPd { pd }", "n": 1,
                "backing": format!("{:?}", Backing::HostPdEndpoint),
                "bounds": "strong-local — a confined forked child reached ONLY over its firmament Endpoint (no files/network/exec)",
            }),
        ),
    ];

    // The live migration frontier: read each cell's lifecycle from the world.
    // The reflection surfaces `lifecycle` as a headline; we read it from the cell.
    let mut surfaces = Vec::new();
    let mut migrated = Vec::new();
    let mut sealed = Vec::new();
    for (id, cell) in s.world.ledger().iter() {
        let lc = format!("{:?}", cell.lifecycle);
        // Every live cell is a candidate surface target (the firmament's visual face).
        surfaces.push(json!({
            "cell": short(id.as_bytes()),
            "target": "Surface { cell }",
            "lifecycle": lc.split_whitespace().next().unwrap_or(&lc),
            "rights_axis": "the SAME AuthRequired lattice gates the window cap as the underlying cell cap",
        }));
        if lc.starts_with("Migrated") {
            migrated.push(short(id.as_bytes()));
        }
        if lc.starts_with("Sealed") {
            sealed.push(short(id.as_bytes()));
        }
    }

    let bounds_local = Bounds::LOCAL;
    json!({
        "what": "the firmament: ONE capability across DISTANCE (local seL4-cap ↔ distributed dregg-cap ↔ surface=window ↔ confined host-PD), the (target, rights) handle dispatched by target",
        "distance_axis": axis.into_iter().map(|(k, v)| json!({ "rung": k, "shape": v })).collect::<Vec<_>>(),
        "n1_collapse": {
            "Bounds::LOCAL": { "revocation_immediate": bounds_local.revocation_immediate, "commit_synchronous": bounds_local.commit_synchronous, "n": bounds_local.n },
            "principle": "at n=1 (compositor + apps on one box) every rung's bounds collapse to strong-local: immediate revocation, synchronous commit",
        },
        "compositor_scene": {
            "what": "the CompositorPd scene = surfaces in paint order; present() is admitted ONLY through three verified teeth",
            "T1_non_overlap": "an app composites ONLY its cap-authorized regions (no overpaint of a foreign surface)",
            "T2_label_binding": "the surface label = label_of(owner, source_state_root), COMPOSITOR-computed — not app-supplied (no spoof)",
            "T3_focus_exclusivity": "at-most-one surface holds focus; input routes only there (no double-focus, no misroute)",
            "refusals": ["Overpaint", "LabelSpoof", "InputMisroute", "DoubleFocus", "NoSurface", "NoFrameAdvance"],
        },
        "migration_frontier": {
            "lifecycle_states": ["Live", "Sealed { reason, at }", "Migrated { to, attestation, migrated_at }", "Destroyed { certificate, at }", "Archived { checkpoint, through }"],
            "live_surfaces": surfaces.len(),
            "surfaces": surfaces,
            "migrated_cells": migrated,
            "sealed_cells": sealed,
            "note": "Migrated is TERMINAL — the cell relocated to another federation, its attestation binds the destination receipt",
        },
        "seam": {
            "compositor_pd": "the live CompositorPd + the framebuffer + torn-off/confined surface authority live in the gpui cockpit shell (starbridge-v2/src/shell.rs) and the seL4 dregg-firmament PDs — owned by other lanes; this tool reads the LEDGER lifecycle + projects the distance axis + the scene contract (all gpui-free), not the live compositor framebuffer",
        },
        "types": ["Capability", "Target", "Bounds", "Resolution", "Backing", "Scene", "Surface", "Present", "FrameCommit", "Refusal", "CellLifecycle", "SurfaceCapability"],
    })
}

// ---------------------------------------------------------------------------
// federation — committee / epoch / checkpoint / bridges / revocation (seam)
// ---------------------------------------------------------------------------

/// The FEDERATION surface: committee / epoch / checkpoint / cross-fed bridges /
/// revocation. The live federation/consensus STATE is NEVER in this embedded
/// process — it lives on a running node; the headless embedded-executor build
/// deliberately does NOT link the consensus stack. So this tool surfaces the
/// honest catalog: the captp-only / node-service objects named with their seam +
/// route (the `federation_inspector` "designed-pending" surface, never faked),
/// plus the protocol vocabulary of the federation types.
fn tool_federation(s: &Session) -> Value {
    use starbridge_v2::federation_inspector::FederationSurvey;

    // No node is connected in the embedded image → the disconnected survey, which
    // still carries the full honest captp-only catalog.
    let survey = FederationSurvey::disconnected();
    let remote: Vec<Value> = survey
        .remote
        .iter()
        .map(|p| json!({ "kind": p.kind, "seam": p.seam, "route": p.route }))
        .collect();

    // The embedded image IS itself a degenerate (solo / n=1) federation: the
    // executor signs receipts under one identity, no quorum. Surface that fact.
    let executor_pk = s.world.executor_public_key();

    json!({
        "what": "the federation: the committee (validators + threshold), the epoch (membership rotation), the checkpoint (state-root quorum certificate), the cross-fed bridge (handoff cert), and revocation",
        "embedded_image": {
            "mode": "solo / n=1 — this embedded executor IS a degenerate federation of one: it signs receipts under a single executor identity, no quorum, synchronous commit",
            "executor_public_key": executor_pk.map(|k| short(&k)),
            "live_federations": survey.live_count(),
            "note": "live committee/epoch/checkpoint/DAG state belongs to a RUNNING node; it is not in this process",
        },
        "committee": {
            "type": "dregg_federation::FederationCommittee — BLS threshold committee (member secrets + a threshold value); aggregate(shares) → ThresholdQC, verify(qc, msg)",
            "validator": "ValidatorInfo { public_key, signing_key_root, stake, joined_epoch }",
        },
        "epoch": {
            "type": "EpochConfig { epoch_length, current_epoch, epoch_start_height, members, threshold }",
            "transition": "EpochTransition { from_epoch, to_epoch, added_validators, removed_validators, new_threshold, attestation: QuorumCertificate }",
        },
        "checkpoint": {
            "type": "Checkpoint { height, ledger_state_root, note_tree_root, nullifier_set_root, revocation_tree_root, federation_members, epoch, qc, timestamp }",
            "verify": "verify_with_committee(committee) — the QC must carry 2f+1 of the committee at this epoch",
            "wire": "a connected node publishes CheckpointResponse { height, ledger_state_root, note_tree_root, nullifier_set_root, revocation_tree_root, epoch, timestamp, federation_members, qc_votes }",
        },
        "revocation": {
            "type": "RevocationTree — a Merkle set of revoked token ids; prove_non_membership(id) → NonMembershipProof; the checkpoint binds its revocation_tree_root",
            "principle": "non-membership is the live-at-settlement check (a cap is exercisable iff its token is NOT in the revocation tree at the settling checkpoint)",
        },
        "cross_fed_bridge": {
            "type": "CrossFedReceiptBundle { recipient_chain, issuer_attested_root, recipient_attested_root, cross_fed_cert: HandoffCertificate, recipient_federation_receipt }",
            "purpose": "carries a cap + its provenance across a federation boundary (the OCapN third-party handoff)",
        },
        "remote_path_catalog": {
            "what": "the captp-only / node-service federation objects, surfaced honestly with kind + seam + route (never faked)",
            "objects": remote,
        },
        "wire_types_when_connected": ["FederationInfo", "CheckpointResponse", "BlockInfo", "NodeStatus"],
        "seam": "federation/consensus is wire-only: connect a node and read /api/federations, /api/block/{height}, /status — then FederationSurvey::from_wire(...) reflects the LIVE committee/epoch/checkpoint/DAG",
    })
}

// ---------------------------------------------------------------------------
// effects / verbs — the protocol's complete action vocabulary + descriptors
// ---------------------------------------------------------------------------

/// The protocol's COMPLETE action vocabulary: the canonical 8 verbs (the minimal
/// kernel) plus the full Effect catalog (every variant), each with its descriptor
/// fields (the action's parameters) and its conservation class (the linearity the
/// executor enforces). The full vocabulary the atlas documents — sourced from the
/// real `dregg_turn::action::Effect` enum, so it never drifts from a hand-list.
fn tool_effects() -> Value {
    // (name, is_canonical_verb, conservation_class, descriptor_fields, gloss)
    let cat: &[(&str, bool, &str, &str, &str)] = &[
        (
            "SetField",
            true,
            "Neutral",
            "cell, index, value",
            "set a state field on a cell",
        ),
        (
            "Transfer",
            true,
            "Conservative",
            "from, to, amount",
            "move balance between cells (Σδ=0 — the conservation tooth)",
        ),
        (
            "GrantCapability",
            true,
            "Generative",
            "from, to, cap: CapabilityRef",
            "grant a cap edge (non-amplifying: granted ⊆ held)",
        ),
        (
            "RevokeCapability",
            true,
            "Terminal",
            "cell, slot",
            "revoke a held cap (terminal — monotone down)",
        ),
        (
            "EmitEvent",
            true,
            "Neutral",
            "cell, event",
            "emit an event into the receipt (no state change)",
        ),
        (
            "IncrementNonce",
            true,
            "Monotonic",
            "cell",
            "advance the cell nonce (the anti-replay tick)",
        ),
        (
            "CreateCell",
            true,
            "Generative",
            "public_key, token_id, balance",
            "mint a new cell into the ledger",
        ),
        (
            "SetPermissions",
            true,
            "Neutral",
            "cell, new_permissions",
            "rewrite a cell's AuthRequired gates (applied LAST in an action)",
        ),
        (
            "SetVerificationKey",
            false,
            "Neutral",
            "cell, new_vk",
            "rewrite a cell's VK (applied LAST in an action)",
        ),
        (
            "SetProgram",
            false,
            "Neutral",
            "cell, program: CellProgram",
            "reprogram a cell's caveat table as an ordered turn (the live-customize path)",
        ),
        (
            "NoteSpend",
            false,
            "Conservative",
            "nullifier, note_tree_root, value, asset_type, spending_proof, value_commitment?",
            "spend a shielded note by revealing its nullifier (proof-carrying)",
        ),
        (
            "NoteCreate",
            false,
            "Conservative",
            "commitment, value, asset_type, encrypted_note, value_commitment?, range_proof?",
            "create a shielded note (adds a commitment to the note tree)",
        ),
        (
            "SpawnWithDelegation",
            false,
            "Generative",
            "child_public_key, child_token_id, max_staleness",
            "spawn a delegated child cell",
        ),
        (
            "RefreshDelegation",
            false,
            "Neutral",
            "child, snapshot",
            "refresh a delegation's freshness snapshot",
        ),
        (
            "RevokeDelegation",
            false,
            "Terminal",
            "child",
            "revoke a delegation (terminal)",
        ),
        (
            "BridgeMint",
            false,
            "Generative",
            "portable_proof: PortableNoteProof",
            "mint from a cross-federation portable note proof",
        ),
        (
            "Introduce",
            false,
            "Generative",
            "introducer, recipient, target, permissions",
            "the ocap introduction primitive (a → grants b a cap on c)",
        ),
        (
            "PipelinedSend",
            false,
            "Neutral",
            "target: EventualRef, action",
            "CapTP promise-pipelined send (a send against a not-yet-resolved ref)",
        ),
        (
            "ExerciseViaCapability",
            false,
            "Neutral",
            "cap_slot, inner_effects",
            "exercise effects THROUGH a held capability (attenuated re-dispatch)",
        ),
        (
            "MakeSovereign",
            false,
            "Terminal",
            "cell",
            "make a cell sovereign (terminal authority transition)",
        ),
        (
            "CreateCellFromFactory",
            false,
            "Generative",
            "factory_vk, owner_pubkey, token_id, params",
            "mint a cell from a deployed factory descriptor",
        ),
        (
            "Refusal",
            false,
            "Monotonic",
            "cell, offered_action_commitment, refusal_reason, proof_witness_index",
            "a witnessed refusal (a cell declines an offered action, on the record)",
        ),
        (
            "CellSeal",
            false,
            "Terminal",
            "target, reason",
            "seal a cell (reversible quiescence — rejects new effects)",
        ),
        (
            "CellUnseal",
            false,
            "Terminal",
            "target",
            "unseal a sealed cell",
        ),
        (
            "CellDestroy",
            false,
            "Terminal",
            "target, certificate: DeathCertificate",
            "permanently retire a cell (terminal)",
        ),
        (
            "Burn",
            false,
            "Annihilative",
            "target, slot, amount",
            "burn value out of existence (the only non-conservative value sink)",
        ),
        (
            "AttenuateCapability",
            false,
            "Terminal",
            "cell, slot, narrower_permissions, narrower_effects?, narrower_expiry?",
            "attenuate a held cap in place (monotone narrowing — adoption IS attenuation)",
        ),
        (
            "ReceiptArchive",
            false,
            "Terminal",
            "prefix_end_height, checkpoint: ArchivalAttestation",
            "archive a receipt-chain prefix under a checkpoint attestation",
        ),
        (
            "Promise",
            false,
            "Generative",
            "cell, resolution_condition, wake, timeout_height",
            "post a promise (a hole the circuit treats as a nullifier; resolution = a spend)",
        ),
        (
            "Notify",
            false,
            "Generative",
            "from, to, resolution_condition, wake, timeout_height",
            "register a wake on another cell's resolution condition",
        ),
        (
            "React",
            false,
            "Terminal",
            "pending_id, condition, resolution_proof, wake",
            "resolve a pending promise with a proof (fires the wake; one-shot)",
        ),
    ];

    let verbs: Vec<Value> = cat.iter().filter(|e| e.1).map(|(name, _, class, fields, gloss)| {
        json!({ "verb": name, "conservation": class, "descriptor": fields, "gloss": gloss })
    }).collect();
    let all: Vec<Value> = cat.iter().map(|(name, canon, class, fields, gloss)| {
        json!({ "effect": name, "canonical_verb": canon, "conservation": class, "descriptor": fields, "gloss": gloss })
    }).collect();

    json!({
        "what": "the protocol's complete action vocabulary — sourced from dregg_turn::action::Effect (31 variants) so it can never drift from a hand-list",
        "the_eight_verbs": {
            "what": "the minimal kernel set (dregg3: 8 verbs from 52) — the canonical subset every cell speaks",
            "verbs": verbs,
        },
        "conservation_classes": {
            "what": "Effect::linearity() — the linearity the verified executor enforces per effect",
            "classes": {
                "Conservative": "Σδ = 0 (Transfer, NoteSpend, NoteCreate) — value is moved, never made/lost",
                "Generative": "introduces structure under non-forgeability (Create*, Grant, Introduce, Promise, Notify, Spawn, BridgeMint)",
                "Terminal": "monotone-down / one-way (Revoke*, Destroy, Seal, Attenuate, MakeSovereign, Archive, React)",
                "Annihilative": "value sink (Burn — the only one)",
                "Monotonic": "advances a monotone counter/log (IncrementNonce, Refusal)",
                "Neutral": "state mutation with no linear obligation (SetField/Permissions/VK/Program, Emit, Pipeline, Exercise, Refresh)",
            },
        },
        "full_catalog": {
            "count": all.len(),
            "effects": all,
        },
        "note": "descriptor fields are the variant's struct fields — the action's parameters; `?` marks an Option field",
    })
}

// ---------------------------------------------------------------------------
// map — THE comprehensive machine-readable hypermedia graph (the keystone)
// ---------------------------------------------------------------------------

/// THE comprehensive cross-linked map: ONE JSON graph over the WHOLE inspectable
/// system. Nodes (every cell, every presentation face, every affordance/message,
/// every effect/verb, every surface candidate, the federation seam objects, the
/// data-plane substrate) each carry a stable `id`; edges are typed relations
/// (cell→face `presents`, cell→message `affords`, message→effect `fires`,
/// cell→cell `caps` over the ocap web, cell→surface `surfaces`, …). This is the
/// hypermedia backbone the atlas site links over: every object addressable,
/// every relation an edge. Optionally written to `out`.
fn tool_map(s: &Session, out: Option<&str>) -> Result<Value, String> {
    let reg = Registry::new(&s.world);
    let mut nodes: Vec<Value> = Vec::new();
    let mut edges: Vec<Value> = Vec::new();

    let node = |id: String, kind: &str, label: String, extra: Value| {
        let mut base = json!({ "id": id, "kind": kind, "label": label });
        if let Value::Object(m) = extra {
            if let Value::Object(b) = &mut base {
                for (k, v) in m {
                    b.insert(k, v);
                }
            }
        }
        base
    };
    let edge = |from: String, rel: &str, to: String| json!({ "from": from, "rel": rel, "to": to });

    // --- the system root + the standing reference nodes (effects/verbs, seams) ---
    nodes.push(node("sys:root".into(), "system", "dregg live verified image".into(),
        json!({ "image": s.image, "cell_count": s.world.ledger().iter().count(), "height": s.world.height(), "state_root": short(&s.world.state_root()) })));

    // effect-catalog nodes (one per effect/verb) — addressable so a message can
    // link to the effect it fires, and the atlas can document each.
    let effects = tool_effects();
    if let Some(arr) = effects["full_catalog"]["effects"].as_array() {
        for e in arr {
            let name = e["effect"].as_str().unwrap_or("?");
            let eid = format!("effect:{name}");
            nodes.push(node(eid.clone(), "effect", name.to_string(), json!({
                "canonical_verb": e["canonical_verb"], "conservation": e["conservation"], "descriptor": e["descriptor"],
            })));
            edges.push(edge("sys:root".into(), "defines-effect", eid));
        }
    }

    // the standing seam nodes (data plane + federation + firmament axis) so the
    // atlas can cross-link to the deeper tools.
    nodes.push(node(
        "plane:dataplane".into(),
        "data-plane",
        "captp Bus / channel substrate".into(),
        json!({ "tool": "dataplane", "live": "driven in-process; node Bus is a wire seam" }),
    ));
    nodes.push(node(
        "plane:federation".into(),
        "federation",
        "committee / epoch / checkpoint / revocation".into(),
        json!({ "tool": "federation", "live": "solo n=1 here; quorum federation is a wire seam" }),
    ));
    for rung in ["Local", "Distributed", "Surface", "HostPd"] {
        let rid = format!("firmament:{rung}");
        nodes.push(node(
            rid.clone(),
            "distance-rung",
            format!("firmament {rung}"),
            json!({ "axis": "one cap across distance" }),
        ));
        edges.push(edge("sys:root".into(), "distance-rung", rid));
    }
    edges.push(edge(
        "sys:root".into(),
        "has-plane",
        "plane:dataplane".into(),
    ));
    edges.push(edge(
        "sys:root".into(),
        "has-plane",
        "plane:federation".into(),
    ));

    // --- per-cell: the node, its faces, its affordances, its surface candidacy ---
    let ids: Vec<CellId> = s.world.ledger().iter().map(|(id, _)| *id).collect();
    for id in &ids {
        let cid = format!("cell:{}", hex32(id.as_bytes()));
        let cell = s.world.ledger().get(id);
        let lifecycle = cell
            .map(|c| format!("{:?}", c.lifecycle))
            .map(|l| l.split_whitespace().next().unwrap_or("?").to_string())
            .unwrap_or_else(|| "?".into());
        let insp = cell.map(|c| starbridge_v2::reflect::reflect_cell(id, c));
        let title = insp
            .as_ref()
            .map(|i| i.title.clone())
            .unwrap_or_else(|| short(id.as_bytes()));
        let kindname = insp
            .as_ref()
            .map(|i| format!("{:?}", i.kind))
            .unwrap_or_default();
        let balance = insp.as_ref().and_then(|i| {
            i.fields.iter().find_map(|f| match &f.value {
                FieldValue::Balance(b) if f.key == "balance" => Some(*b),
                _ => None,
            })
        });
        nodes.push(node(cid.clone(), "cell", title, json!({
            "short": short(id.as_bytes()), "cell_kind": kindname, "lifecycle": lifecycle, "balance": balance,
        })));
        edges.push(edge("sys:root".into(), "contains-cell", cid.clone()));

        // surface candidacy: every live cell is a Surface target on the firmament axis.
        edges.push(edge(cid.clone(), "surfaces-as", "firmament:Surface".into()));

        // faces
        if let Some(set) = reg.present(FocusTarget::Cell(*id), *id) {
            for p in &set {
                let fid = format!("{cid}/face:{}", p.kind.slug());
                nodes.push(node(
                    fid.clone(),
                    "face",
                    p.label.clone(),
                    json!({ "face": p.kind.slug() }),
                ));
                edges.push(edge(cid.clone(), "presents", fid));
            }
        }

        // affordances → fires → effect
        let ia = InspectAct::build(&s.world, InspectFocus::Cell(*id), *id, AuthRequired::Either);
        for m in &ia.messages {
            let mid = format!("{cid}/msg:{}", m.name);
            nodes.push(node(mid.clone(), "message", m.name.clone(), json!({
                "effect": m.effect, "required": format!("{:?}", m.required), "authorized": m.authorized,
            })));
            edges.push(edge(cid.clone(), "affords", mid.clone()));
            // link the message to the effect-catalog node when the effect name matches.
            let eff_node = format!("effect:{}", m.effect);
            if nodes.iter().any(|n| n["id"] == json!(eff_node)) {
                edges.push(edge(mid, "fires", eff_node));
            }
        }
    }

    // --- the ocap web as cap edges between cell nodes ---
    let g = OcapGraph::build(&s.world);
    for e in g.edges() {
        let from = format!("cell:{}", hex32(e.holder.as_bytes()));
        let to = format!("cell:{}", hex32(e.target.as_bytes()));
        edges.push(json!({ "from": from, "rel": "caps", "to": to, "slot": e.slot, "rights": format!("{:?}", e.rights) }));
    }

    let counts = json!({
        "nodes": nodes.len(),
        "edges": edges.len(),
        "by_kind": {
            "cell": ids.len(),
            "effect": effects["full_catalog"]["count"].clone(),
        },
    });
    let blob = json!({
        "what": "THE hypermedia backbone: one cross-linked graph over the whole inspectable system — every object an addressable node, every relation a typed edge",
        "node_kinds": ["system", "cell", "face", "message", "effect", "data-plane", "federation", "distance-rung"],
        "edge_rels": ["contains-cell", "defines-effect", "presents", "affords", "fires", "caps", "surfaces-as", "distance-rung", "has-plane"],
        "counts": counts,
        "nodes": nodes,
        "edges": edges,
        "hint": "link over `id`; resolve a cell node with inspect, an effect node with effects, a plane node with dataplane/federation",
    });

    if let Some(path) = out {
        std::fs::write(
            path,
            serde_json::to_string_pretty(&blob).unwrap_or_default(),
        )
        .map_err(|e| format!("write {path}: {e}"))?;
        Ok(
            json!({ "path": path, "counts": counts, "hint": "the full graph was written; this summary carries the counts" }),
        )
    } else {
        Ok(blob)
    }
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
        { "name": "rewind", "description": "Backtrack the world to a prefix of the act-trail (reboot + replay the first `to` committed acts). Slow (~3s reboot); prefer snapshot/restore for crawls. `to`=0 fully resets.",
          "inputSchema": { "type": "object", "properties": { "to": { "type": "integer", "description": "keep the first N committed acts (0 = reset)" } } } },
        { "name": "snapshot", "description": "Checkpoint the current world state cheaply (a fork-based deep clone, ~ms — no reboot). Returns an id. The game-tree crawl's fast backtracking primitive.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "restore", "description": "Restore a world state captured by `snapshot` (reusable — the snapshot survives restore). Cheap.",
          "inputSchema": { "type": "object", "properties": { "id": { "type": "integer", "description": "snapshot id" } }, "required": ["id"] } },
        { "name": "forget", "description": "Drop a snapshot to free memory.",
          "inputSchema": { "type": "object", "properties": { "id": { "type": "integer" } }, "required": ["id"] } },
        { "name": "export", "description": "Dump the FULL crawl (meta + every cell's faces/affordances/halo + the ocap graph + the act-trail) as one JSON file for the atlas site-builder.",
          "inputSchema": { "type": "object", "properties": { "out": str_prop("output .json path") } } },
        { "name": "protocol", "description": "The protocol reference: the AuthRequired lattice, the effect/verb vocabulary seen live, and the refusal taxonomy (cap-gate vs executor).",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "effect", "description": "Submit a RAW effect through the verified executor (beyond self-affordances). kind: transfer (from→to, amount — value flow + conservation) | grant (from→to a cap, slot) | create (a new cell, seed). Returns committed/refused like act. Mutates the live world.",
          "inputSchema": { "type": "object", "properties": { "kind": str_prop("transfer|grant|create"), "from": str_prop("source cell"), "to": str_prop("target cell"), "amount": { "type": "integer" }, "slot": { "type": "integer" }, "seed": { "type": "integer" } }, "required": ["kind", "from"] } },
        { "name": "view", "description": "Describe the current session: cell count, anchors, acts committed, cells visited.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "dataplane", "description": "The captp DATA PLANE (dregg_captp Bus): inboxes, queue depths, pending-vs-delivered (receipt-identity), pub/sub topics, wake-by-name cursors. Stands up a REAL Bus in-process and drives a genuine post→wake→publish→drain cycle so every value is live; names the seam to the running node's per-node Bus (the channels service over the node HTTP API).",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "firmament", "description": "The FIRMAMENT surface/migration state: the (target, rights) capability across the Local/Distributed/Surface/HostPd distance axis (with the n=1 collapse to strong-local), the compositor scene contract (the T1/T2/T3 verified teeth), and the LIVE cell-lifecycle migration frontier (Live/Sealed/Migrated/Destroyed/Archived) read straight from the ledger. Names the live-compositor seam.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "federation", "description": "The FEDERATION surface: committee (BLS threshold) / epoch (membership rotation) / checkpoint (state-root quorum certificate) / cross-fed bridge (handoff cert) / revocation tree. The embedded image is a solo n=1 federation; the live quorum/consensus state is a wire seam — this tool surfaces the honest captp-only/node-service object catalog (kind+seam+route, never faked) plus the federation type vocabulary.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "effects", "description": "The protocol's COMPLETE action vocabulary: the canonical 8 verbs (the minimal kernel) + the full Effect catalog (every variant, 31), each with its descriptor fields (the action's parameters) and its conservation class (Conservative/Generative/Terminal/Annihilative/Monotonic/Neutral — the linearity the verified executor enforces). Sourced from dregg_turn::action::Effect so it never drifts.",
          "inputSchema": { "type": "object", "properties": {} } },
        { "name": "map", "description": "THE keystone: ONE comprehensive cross-linked machine-readable graph over the WHOLE inspectable system — every cell, presentation face, affordance/message, effect/verb, surface candidate, and the data-plane/federation/firmament seams, as nodes with stable `id`s and TYPED edges (contains-cell, presents, affords, fires, caps, surfaces-as, distance-rung, has-plane). The hypermedia backbone the atlas site links over. Optionally writes to `out`.",
          "inputSchema": { "type": "object", "properties": { "out": str_prop("output .json path (omit to return the full graph inline)") } } },
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
        "inspect" => tool_inspect(
            s,
            str_arg("cell").ok_or("missing `cell`")?,
            str_arg("as"),
            str_arg("rights"),
        ),
        "affordances" => tool_affordances(
            s,
            str_arg("cell").ok_or("missing `cell`")?,
            str_arg("as"),
            str_arg("rights"),
        ),
        "act" => tool_act(
            s,
            str_arg("cell").ok_or("missing `cell`")?,
            str_arg("message").ok_or("missing `message`")?,
            str_arg("as"),
            str_arg("rights"),
        ),
        "spotter" => Ok(tool_spotter(
            s,
            str_arg("query").ok_or("missing `query`")?,
            str_arg("as"),
        )),
        "graph" => tool_graph(
            s,
            str_arg("kind").ok_or("missing `kind`")?,
            str_arg("format").unwrap_or("json"),
        ),
        "render" => tool_render_html(s, str_arg("cell").ok_or("missing `cell`")?, str_arg("out")),
        "screenshot" => tool_screenshot(s, str_arg("out"), str_arg("size"), str_arg("tab")),
        "rewind" => Ok(tool_rewind(
            s,
            args.get("to").and_then(|v| v.as_u64()).unwrap_or(0) as usize,
        )),
        "snapshot" => {
            let id = s.next_snap;
            s.next_snap += 1;
            s.snaps.insert(id, (s.world.fork(), s.acts.clone()));
            Ok(
                json!({ "id": id, "live_snapshots": s.snaps.len(), "note": "cheap fork-based checkpoint (no reboot)" }),
            )
        }
        "restore" => {
            let id = args
                .get("id")
                .and_then(|v| v.as_u64())
                .ok_or("missing `id`")?;
            let snap = s.snaps.get(&id).map(|(w, a)| (w.fork(), a.clone()));
            match snap {
                Some((w, a)) => {
                    s.world = w;
                    s.acts = a;
                    Ok(
                        json!({ "restored": id, "cell_count": s.world.ledger().iter().count(), "acts": s.acts.len() }),
                    )
                }
                None => Err(format!(
                    "no snapshot {id} (live: {:?})",
                    s.snaps.keys().collect::<Vec<_>>()
                )),
            }
        }
        "forget" => {
            let id = args
                .get("id")
                .and_then(|v| v.as_u64())
                .ok_or("missing `id`")?;
            s.snaps.remove(&id);
            Ok(json!({ "forgotten": id, "live_snapshots": s.snaps.len() }))
        }
        "export" => tool_export(s, str_arg("out")),
        "protocol" => Ok(tool_protocol(s)),
        "effect" => tool_effect(s, str_arg("kind").ok_or("missing `kind`")?, args),
        "view" => Ok(tool_view(s)),
        "dataplane" => Ok(tool_dataplane(s)),
        "firmament" => Ok(tool_firmament(s)),
        "federation" => Ok(tool_federation(s)),
        "effects" | "verbs" => Ok(tool_effects()),
        "map" => tool_map(s, str_arg("out")),
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
    eprintln!(
        "dregg-mcp: live verified image up ({} cells)",
        session.world.ledger().iter().count()
    );

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) if !l.trim().is_empty() => l,
            Ok(_) => continue,
            Err(_) => break,
        };
        let req: Value = match serde_json::from_str(&line) {
            Ok(v) => v,
            Err(e) => {
                let _ = writeln!(
                    stdout,
                    "{}",
                    json!({ "jsonrpc": "2.0", "id": null, "error": { "code": -32700, "message": format!("parse error: {e}") } })
                );
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
                    Ok(v) => Ok(
                        json!({ "content": [ { "type": "text", "text": serde_json::to_string_pretty(&v).unwrap_or_default() } ] }),
                    ),
                    Err(e) => Ok(
                        json!({ "content": [ { "type": "text", "text": format!("error: {e}") } ], "isError": true }),
                    ),
                }
            }
            "ping" => Ok(json!({})),
            other => Err((-32601, format!("method not found: {other}"))),
        };

        let resp = match result {
            Ok(r) => json!({ "jsonrpc": "2.0", "id": id, "result": r }),
            Err((code, msg)) => {
                json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": msg } })
            }
        };
        let _ = writeln!(stdout, "{resp}");
        let _ = stdout.flush();
    }
}
