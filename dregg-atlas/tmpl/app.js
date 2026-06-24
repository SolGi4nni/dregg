/* THE DREGG ATLAS — the SPA. A map of the live verified ocap image, newcomer
   first: the SURFACES gallery (what you'd see + touch), the CELLS & CAPS ocap
   web, a small TURNS view (what a turn is, near-genesis — not a 600-state dump),
   the PROTOCOL reference, the COMPONENTS pillar, and an adept WEB of typed
   cross-links with a ⌘K spotter over everything. Reads window.ATLAS. */
(function () {
  const A = window.ATLAS || {};
  const $ = (s, r) => (r || document).querySelector(s);
  const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));
  const esc = (s) => String(s == null ? "" : s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
  if (window.cytoscape && window.cytoscapeDagre) { try { cytoscape.use(window.cytoscapeDagre); } catch (e) {} }

  const cells = (A.cells && A.cells.cells) || [];
  const surfaces = A.surfaces || [];
  const protocol = A.protocol || {};

  // The components pillar — the generator lane (data/components.json) owns this
  // file; it emits either a bare array (the site-builder fallback) or the richer
  // {meta, components:[…]} catalog. Normalise both to one shape the SPA reads.
  const surfTabSet = new Set(surfaces.map(s => s.tab));
  function normComp(c) {
    const group = c.group || c.kind || "widgets";
    const rawSurf = c.surfaces || c.used_surfaces || [];
    const surfs = [];
    rawSurf.forEach(t => {
      const k = String(t).toLowerCase();
      const tab = surfTabSet.has(k) ? k : (surfTabSet.has(k.replace(/-/g, "")) ? k.replace(/-/g, "") : null);
      if (tab && !surfs.includes(tab)) surfs.push(tab);
    });
    const KG = { action: "▣", input: "⌶", display: "ᴬ", feedback: "✦", container: "▢", navigation: "▭", overlay: "◰", data: "▦", layout: "◳", dev: "⌗", widgets: "❖" };
    return {
      name: c.name || "?",
      group, glyph: c.glyph || KG[group] || "❖",
      module: c.module ? (/::/.test(c.module) ? c.module : "gpui_component::" + c.module) : "",
      summary: c.what || c.summary || c.role || "",
      surfaces: surfs,
      verbs: c.verbs || [],
      variants: c.variants || [],
      used_in_deos: !!c.used_in_deos,
    };
  }
  const _rawComp = A.components;
  const components = (Array.isArray(_rawComp) ? _rawComp
    : (_rawComp && _rawComp.components) || []).map(normComp);
  const componentsMeta = (_rawComp && !Array.isArray(_rawComp) && _rawComp.meta) || null;

  // ─── the OBJECT REGISTRY: every navigable thing, by stable id ───────────
  // id scheme: cell:<short> · surface:<tab> · component:<name> · effect:<name>
  //            · verb:<name> · state:<digest>
  const REG = new Map();
  function reg(o) { REG.set(o.id, o); return o; }
  const rel = (o, k, id) => { (o.rel[k] = o.rel[k] || []); if (!o.rel[k].includes(id)) o.rel[k].push(id); };

  // verbs (from protocol) ----------------------------------------------------
  const VERBS = (protocol.the_eight_verbs || []).map(v => {
    const name = v.split(/[/(]/)[0].trim();
    return reg({ id: "verb:" + name, type: "verb", name, label: v, rel: {} });
  });
  // a loose effect→verb classifier (the effect vocabulary is small + stable)
  function verbOf(effect) {
    const e = String(effect || "");
    if (/Transfer|Balance/i.test(e)) return "Transfer";
    if (/SetField/i.test(e)) return "SetField";
    if (/Grant/i.test(e)) return "GrantCapability";
    if (/Revoke/i.test(e)) return "RevokeCapability";
    if (/Nonce/i.test(e)) return "IncrementNonce";
    if (/Emit|Event|peek/i.test(e)) return "EmitEvent";
    if (/Create/i.test(e)) return "CreateCell";
    return null;
  }
  const verbById = n => REG.get("verb:" + n);

  // effects (from protocol + cells) -----------------------------------------
  const effSet = new Set(protocol.effects_seen || []);
  cells.forEach(c => (c.affordances || []).forEach(a => a.effect && effSet.add(a.effect)));
  effSet.forEach(e => {
    const o = reg({ id: "effect:" + e, type: "effect", name: e, label: e, rel: {} });
    const vn = verbOf(e);
    if (vn) { const v = verbById(vn); if (v) { rel(o, "verb", v.id); rel(v, "effect", o.id); } }
  });
  const effById = e => REG.get("effect:" + e);

  // cells + affordances ------------------------------------------------------
  cells.forEach(c => {
    const o = reg({ id: "cell:" + c.short, type: "cell", name: c.short, label: "Cell " + c.short, data: c, rel: {} });
    (c.affordances || []).forEach(a => {
      const e = effById(a.effect);
      if (e) { rel(o, "effect", e.id); rel(e, "cell", o.id); }
    });
  });
  // ocap edges → cell↔cell capability grants
  ((A.cells && A.cells.ocap && A.cells.ocap.edges) || []).forEach(e => {
    const f = REG.get("cell:" + e.from), t = REG.get("cell:" + e.to);
    if (f && t) { rel(f, "grants", t.id); rel(t, "granted-by", f.id); }
  });

  // surfaces -----------------------------------------------------------------
  surfaces.forEach(s => {
    reg({ id: "surface:" + s.tab, type: "surface", name: s.tab, label: s.tab, data: s, rel: {} });
  });

  // components (generator pillar; degrade gracefully if absent) --------------
  components.forEach(cmp => {
    const o = reg({ id: "component:" + cmp.name, type: "component", name: cmp.name, label: cmp.name, data: cmp, rel: {} });
    (cmp.surfaces || []).forEach(tab => {
      const s = REG.get("surface:" + tab);
      if (s) { rel(o, "surface", s.id); rel(s, "component", o.id); }
    });
    (cmp.verbs || []).forEach(vn => {
      const v = verbById(vn); if (v) { rel(o, "verb", v.id); rel(v, "component", o.id); }
    });
  });

  // ── densify the web: a surface→component association layer ────────────────
  // The generator only cross-links *live-used* widgets (a sparse grep). For a
  // genuinely navigable atlas we also assert which widgets each surface is built
  // from, matching component names loosely (case/word-insensitive). This makes
  // every surface link to its building blocks and back.
  const SURFACE_WIDGETS = {
    home: ["TitleBar", "TabBar / Tab", "Label", "Badge", "Icon"],
    inspector: ["Tree", "DescriptionList", "TabBar / Tab", "Scrollbar / Scrollable"],
    "inspect-act": ["Button", "Input", "DescriptionList", "Tree"],
    graph: ["Tooltip", "Badge", "Scrollbar / Scrollable"],
    "web-of-cells": ["Tree", "Tooltip", "Badge", "Scrollbar / Scrollable"],
    objects: ["Table / DataTable", "List", "Tag", "Scrollbar / Scrollable"],
    proofs: ["Charts", "Table / DataTable", "Badge", "Progress / ProgressCircle"],
    debugger: ["Table / DataTable", "Tree", "Button", "TabBar / Tab", "Input"],
    replay: ["Slider", "Button", "Table / DataTable", "Progress / ProgressCircle"],
    workspace: ["Dock", "ResizablePanelGroup", "TabBar / Tab", "Sidebar"],
    wonder: ["Icon", "Label", "HoverCard", "Badge"],
    lanes: ["Table / DataTable", "List", "Badge", "Progress / ProgressCircle"],
    powerbox: ["Dialog / AlertDialog", "List", "Combobox", "Button"],
    "links-here": ["List", "Link", "Tag"],
    organs: ["Accordion", "GroupBox", "Badge", "Label"],
    cipherclerk: ["Form / Field", "Input", "Button", "Badge"],
    editor: ["Input", "Dock", "TabBar / Tab", "Scrollbar / Scrollable", "StatusBar"],
    composer: ["Input", "Button", "Separator"],
    simulate: ["Button", "Slider", "Charts", "Table / DataTable"],
    agent: ["Input", "List", "Avatar / AvatarGroup", "Badge", "Spinner"],
    swarm: ["List", "Avatar / AvatarGroup", "Badge", "Progress / ProgressCircle", "Table / DataTable"],
    shell: ["Input", "Scrollbar / Scrollable", "StatusBar"],
    terminal: ["Input", "Scrollbar / Scrollable", "StatusBar", "TabBar / Tab"],
    buffer: ["Input", "Scrollbar / Scrollable", "TabBar / Tab"],
    trust: ["Table / DataTable", "Badge", "Tag", "Tree"],
    docs: ["Scrollbar / Scrollable", "Breadcrumb", "Link", "Sidebar"],
    time: ["Slider", "Table / DataTable", "Label"],
    share: ["Dialog / AlertDialog", "Button", "Input", "Clipboard"],
    "deos-chat": ["Input", "List", "Avatar / AvatarGroup", "Badge", "HoverCard"],
    "deos-editor": ["Input", "Dock", "TabBar / Tab", "Scrollbar / Scrollable"],
    "deos-docviewer": ["Scrollbar / Scrollable", "Breadcrumb", "Sidebar", "Link"],
  };
  const compByName = {};
  components.forEach(c => { compByName[c.name.toLowerCase()] = c; });
  const findComp = nm => compByName[nm.toLowerCase()] || compByName[nm.split(" / ")[0].toLowerCase().trim()];
  Object.entries(SURFACE_WIDGETS).forEach(([tab, widgets]) => {
    const s = REG.get("surface:" + tab); if (!s) return;
    widgets.forEach(w => {
      const cmp = findComp(w); if (!cmp) return;
      const o = REG.get("component:" + cmp.name); if (!o) return;
      rel(s, "component", o.id); rel(o, "surface", s.id);
    });
  });

  const ICON = { cell: "◈", surface: "▦", component: "❖", effect: "⚡", verb: "▸", state: "⬡" };
  const TYPES = ["cell", "surface", "component", "effect", "verb"];

  // a clickable cross-link chip ---------------------------------------------
  function chip(id) {
    const o = REG.get(id); if (!o) return "";
    return `<a class="chip ${o.type}" data-go="${esc(id)}" title="${esc(o.type)}: ${esc(o.label)}">${esc(o.name)}</a>`;
  }
  function chips(ids) { return (ids || []).map(chip).join(""); }
  function relBlock(o, label, key) {
    const v = o.rel[key]; if (!v || !v.length) return "";
    return `<div class=relgroup><span class=lbl>${esc(label)}</span><div class=chips>${chips(v)}</div></div>`;
  }

  // central navigation: open ANY object in its natural home + detail ---------
  function go(id) {
    const o = REG.get(id); if (!o) return;
    if (o.type === "cell") { activate("ocap"); selectOcap(o.name); }
    else if (o.type === "surface") { activate("surfaces"); openSurface(o.name); }
    else if (o.type === "component") { activate("components"); openComponent(o.name); }
    else if (o.type === "state") { activate("gametree"); selectState(o.name); }
    else { activate("map"); selectMap(id); }
  }
  document.addEventListener("click", e => {
    const a = e.target.closest("[data-go]");
    if (a) { e.preventDefault(); closeSpotter(); go(a.dataset.go); }
  });

  // ─── nav (with #hash deep-links) ─────────────────────────────────────────
  function activate(v) {
    $$("nav.tabs button").forEach(x => x.classList.toggle("on", x.dataset.v === v));
    $$(".view").forEach(x => x.classList.toggle("on", x.dataset.v === v));
    if (v === "gametree" && gt) { gt.resize(); gt.fit(null, 40); }
    if (v === "ocap" && oc) { oc.resize(); oc.fit(null, 40); }
    if (v === "map" && mp) { mp.resize(); mp.fit(null, 50); }
    if (location.hash.slice(1) !== v) history.replaceState(null, "", "#" + v);
  }
  $("#tabs").addEventListener("click", e => {
    const b = e.target.closest("button"); if (!b) return;
    location.hash = b.dataset.v;
  });
  window.addEventListener("hashchange", () => activate(location.hash.slice(1) || "surfaces"));

  $("#stat").textContent =
    `${surfaces.length} surfaces · ${cells.length} cells · ${components.length} components`;

  // ═══ ATLAS WEB (the cross-linked hypermedia map) ════════════════════════
  let mp = null, mapFilter = new Set(TYPES);
  function mapLayout() {
    // concentric by degree: the well-connected hubs (cells, busy surfaces) sit
    // central; lightly-linked + palette nodes ring outward. Always reads as an
    // intentional structure regardless of how sparse the cross-links are.
    return {
      name: "concentric", animate: false, fit: true, padding: 40,
      concentric: n => n.degree(),
      levelWidth: () => 2,
      minNodeSpacing: 26, spacingFactor: 1.05, equidistant: false,
      startAngle: 3 / 2 * Math.PI,
    };
  }
  function buildMap() {
    const els = [];
    REG.forEach(o => {
      if (o.type === "state") return;
      els.push({ data: { id: o.id, label: o.name, ty: o.type } });
    });
    const seenEdge = new Set();
    REG.forEach(o => {
      Object.keys(o.rel).forEach(k => (o.rel[k] || []).forEach(tid => {
        if (!REG.get(tid) || REG.get(tid).type === "state") return;
        const key = [o.id, tid].sort().join("|");
        if (seenEdge.has(key)) return; seenEdge.add(key);
        els.push({ data: { id: "m" + seenEdge.size, source: o.id, target: tid } });
      }));
    });
    const C = { cell: "#58a6ff", surface: "#3fb950", component: "#bc8cff", effect: "#f0883e", verb: "#d29922" };
    mp = cytoscape({
      container: $("#cymap"), elements: els,
      style: [
        { selector: "node", style: { "background-color": ele => C[ele.data("ty")] || "#888", "label": "data(label)", "color": "#c9d1d9", "font-size": 9, "width": 18, "height": 18, "border-width": 1.5, "border-color": "#0a0e14", "text-valign": "bottom", "text-margin-y": 3, "min-zoomed-font-size": 7, "text-max-width": 90, "text-wrap": "ellipsis" } },
        { selector: 'node[ty = "verb"]', style: { "shape": "round-rectangle", "width": 22, "height": 16 } },
        { selector: 'node[ty = "surface"]', style: { "shape": "round-rectangle" } },
        { selector: 'node[ty = "cell"]', style: { "shape": "hexagon", "width": 22, "height": 22 } },
        { selector: "edge", style: { "width": 1, "line-color": "#30363d", "curve-style": "bezier", "opacity": 0.7 } },
        { selector: ".sel", style: { "border-color": "#fff", "border-width": 3, "font-size": 12, "z-index": 99 } },
        { selector: ".nb", style: { "border-color": "#f0883e", "border-width": 2 } },
        { selector: "edge.nb", style: { "line-color": "#f0883e", "width": 2, "opacity": 1, "z-index": 80 } },
        { selector: ".faded", style: { "opacity": 0.08 } },
        { selector: ".hidden", style: { "display": "none" } },
      ],
      layout: mapLayout(),
      wheelSensitivity: 0.3,
    });
    mp.on("tap", "node", ev => selectMap(ev.target.id()));
    mp.on("tap", ev => { if (ev.target === mp) { mp.elements().removeClass("faded sel nb"); $("#mapPanel").innerHTML = mapIntro; } });
    mp.ready(() => mp.fit(null, 50));
    mp.one("layoutstop", () => mp.fit(null, 50));
    buildMapFilter();
  }
  function buildMapFilter() {
    const C = { cell: "#58a6ff", surface: "#3fb950", component: "#bc8cff", effect: "#f0883e", verb: "#d29922" };
    $("#mapfilter").innerHTML = TYPES.map(t =>
      `<button data-ty="${t}"><i style="background:${C[t]}"></i>${t}s</button>`).join("");
    $("#mapfilter").addEventListener("click", e => {
      const b = e.target.closest("button"); if (!b) return;
      const t = b.dataset.ty;
      if (mapFilter.has(t)) mapFilter.delete(t); else mapFilter.add(t);
      b.classList.toggle("off", !mapFilter.has(t));
      mp.batch(() => mp.nodes().forEach(n => n.toggleClass("hidden", !mapFilter.has(n.data("ty")))));
    });
  }
  const mapIntro = $("#mapPanel") ? $("#mapPanel").innerHTML : "";
  function selectMap(id) {
    const o = REG.get(id); if (!o || !mp) return;
    const node = mp.getElementById(id); if (!node.length) return;
    mp.elements().removeClass("sel nb").addClass("faded");
    node.removeClass("faded").addClass("sel");
    node.neighborhood().removeClass("faded").addClass("nb");
    node.connectedEdges().removeClass("faded").addClass("nb");
    mp.animate({ center: { eles: node }, zoom: Math.max(mp.zoom(), 1.1) }, { duration: 220 });
    $("#mapPanel").innerHTML = detailHtml(o);
  }

  // a uniform detail card for any object (used by the map panel + spotter open)
  function detailHtml(o) {
    let h = `<h2><span class="chip ${o.type}" style="cursor:default">${esc(o.type)}</span> ${esc(o.label)}</h2>`;
    if (o.type === "cell" && o.data) {
      h += `<p class=muted>${esc(o.data.id || "")}</p>`;
      h += `<p>Halo: ${(o.data.halo || []).map(esc).join(" · ") || "—"} · <a href="pages/cells/${esc(o.name.replace(/…/g, "_"))}.html" target=_blank>static page ↗</a></p>`;
      h += relBlock(o, "fires effects", "effect");
      h += relBlock(o, "grants capability to", "grants");
      h += relBlock(o, "granted by", "granted-by");
      h += "<h3>Affordances</h3><table>";
      (o.data.affordances || []).forEach(a => { h += `<tr><td class=k>${esc(a.name)}</td><td>${chip("effect:" + a.effect)}<span class=muted> (${esc(a.required)})</span></td><td>${a.authorized ? '<span class=ok>●</span>' : '<span class=no>○</span>'}</td></tr>`; });
      h += "</table>";
    } else if (o.type === "surface" && o.data) {
      if (o.data.file) h += `<a class=shot href="screenshots/${esc(o.data.file)}" data-light="${esc(o.data.file)}" data-cap="${esc(o.name)}"><img src="screenshots/${esc(o.data.file)}" loading=lazy style="width:100%;border:1px solid #21262d;border-radius:6px;margin:6px 0"></a>`;
      h += `<p class=muted>${esc(o.data.explainer || "")}</p>`;
      h += relBlock(o, "built from components", "component");
      h += `<p class=minilink><a href="pages/surfaces/${esc(o.name)}.html" target=_blank>full explainer ↗</a></p>`;
    } else if (o.type === "component" && o.data) {
      h += `<p class=muted>${esc(o.data.summary || o.data.role || "gpui-component widget")}</p>`;
      h += `<p>Group: <b>${esc(o.data.group || "widgets")}</b>${o.data.module ? ` · <code>${esc(o.data.module)}</code>` : ""}${o.data.used_in_deos ? ' · <span class=ok>● live in cockpit</span>' : ''}</p>`;
      if ((o.data.variants || []).length) h += `<div class=relgroup><span class=lbl>variants</span><div class=tagrow>${(o.data.variants).map(v => `<span class="chip" style="cursor:default">${esc(v)}</span>`).join("")}</div></div>`;
      h += relBlock(o, "renders surfaces", "surface");
      h += relBlock(o, "drives verbs", "verb");
    } else if (o.type === "effect") {
      h += relBlock(o, "verb", "verb");
      h += relBlock(o, "fired by cells", "cell");
    } else if (o.type === "verb") {
      h += `<p class=muted>${esc(o.label)}</p>`;
      h += relBlock(o, "effects", "effect");
      h += relBlock(o, "components", "component");
    }
    return h;
  }

  // ═══ TURNS (what a turn is) ═══════════════════════════════════════════════
  // The crawl reaches a large reachable state-space, but it is the SAME small
  // move vocabulary (peek/touch/write/grant + cross-cell transfers) exploded
  // across states — big, not illuminating. We render only the near-genesis
  // FRONTIER: genesis, every state reachable within TURNS_HOPS committed turns
  // (a BFS ball, not the crawler's DFS depth). That shows the whole shape of a
  // turn — every effect, commit vs refuse, the snapshot — without a 600-node
  // combinatorial dump. The full space stays regenerable via crawl.py; this view
  // is for understanding, not enumeration.
  const TURNS_HOPS = 2;
  let gt = null;
  function buildGameTree() {
    const G = A.gametree || { nodes: [], edges: [] };
    // BFS ball of radius TURNS_HOPS from genesis over committed edges
    const committedFrom = {};
    G.edges.forEach(e => { if (e.outcome === "committed") (committedFrom[e.from] = committedFrom[e.from] || []).push(e.to); });
    const root = (G.nodes.find(n => (n.depth || 0) === 0) || G.nodes[0] || {}).digest || "genesis";
    const keepNode = new Set([root]);
    let frontier = [root];
    for (let hop = 0; hop < TURNS_HOPS; hop++) {
      const next = [];
      frontier.forEach(d => (committedFrom[d] || []).forEach(t => { if (!keepNode.has(t)) { keepNode.add(t); next.push(t); } }));
      frontier = next;
    }
    const nodes = G.nodes.filter(n => keepNode.has(n.digest));
    const els = [], seen = new Set();
    const refusedBy = {}, committedBy = {};
    G.edges.forEach(e => {
      if (!keepNode.has(e.from)) return;
      const bag = e.outcome === "committed" ? committedBy : refusedBy;
      (bag[e.from] = bag[e.from] || []).push(e);
    });
    nodes.forEach(n => {
      seen.add(n.digest);
      const committed = committedBy[n.digest] || [];
      els.push({ data: { id: n.digest, label: n.digest === "genesis" ? "genesis" : n.digest.slice(0, 8), depth: n.depth, snap: n.snapshot, refused: refusedBy[n.digest] || [], committed, leaf: committed.length === 0 } });
      reg({ id: "state:" + n.digest, type: "state", name: n.digest, label: n.digest === "genesis" ? "genesis" : n.digest.slice(0, 10), rel: {} });
    });
    let ei = 0;
    G.edges.forEach(e => {
      if (e.outcome !== "committed" || !seen.has(e.from) || !seen.has(e.to)) return;
      els.push({ data: { id: "e" + (ei++), source: e.from, target: e.to, outcome: "committed", label: e.cell + " · " + e.message, info: e } });
    });
    gt = cytoscape({
      container: $("#cy"), elements: els,
      style: [
        { selector: "node", style: { "background-color": "#1f6feb", "label": "data(label)", "color": "#8b949e", "font-size": 8, "width": 15, "height": 15, "border-width": 1.5, "border-color": "#30363d", "text-valign": "bottom", "text-margin-y": 2, "min-zoomed-font-size": 7 } },
        { selector: 'node[depth = 0]', style: { "background-color": "#3fb950", "border-color": "#56d364", "width": 26, "height": 26, "color": "#c9d1d9", "font-size": 11 } },
        { selector: 'node[depth = 1]', style: { "background-color": "#2ea043" } },
        { selector: 'node[depth = 2]', style: { "background-color": "#1f6feb" } },
        { selector: 'node[depth = 3]', style: { "background-color": "#8957e5" } },
        { selector: 'node[depth = 4]', style: { "background-color": "#bc8cff" } },
        { selector: 'node[depth >= 5]', style: { "background-color": "#db61a2" } },
        { selector: 'node[?leaf]', style: { "shape": "diamond" } },
        { selector: "edge", style: { "width": 1.3, "curve-style": "bezier", "target-arrow-shape": "triangle", "arrow-scale": 0.7, "font-size": 6, "color": "#6e7681", "text-rotation": "autorotate", "line-color": "#3fb95066", "target-arrow-color": "#3fb950", "min-zoomed-font-size": 8 } },
        { selector: ".sel", style: { "border-color": "#f0883e", "border-width": 4, "color": "#f0883e" } },
        { selector: "edge.sel", style: { "width": 3.5, "line-color": "#f0883e", "target-arrow-color": "#f0883e", "label": "data(label)", "color": "#f0883e", "z-index": 99 } },
        { selector: ".faded", style: { "opacity": 0.12 } },
      ],
      layout: { name: "concentric", concentric: n => 100 - (n.data("depth") || 0), levelWidth: () => 1, minNodeSpacing: 14, spacingFactor: 1.0, animate: false },
      wheelSensitivity: 0.3,
    });
    gt.on("tap", "node", ev => { showState(ev.target); highlightSubtree(ev.target); });
    gt.on("tap", "edge", ev => showTransition(ev.target));
    gt.on("tap", ev => { if (ev.target === gt) gt.elements().removeClass("faded sel"); });
    gt.ready(() => gt.fit(null, 40));
    gt.one("layoutstop", () => gt.fit(null, 40));
  }
  function selectState(digest) {
    if (!gt) return;
    const n = gt.getElementById(digest) || gt.nodes(`[label = "${digest.slice(0, 8)}"]`).first();
    if (n && n.length) { gt.fit(n.closedNeighborhood(), 80); showState(n); highlightSubtree(n); }
  }
  function highlightSubtree(root) {
    const keep = new Set([root.id()]); let frontier = [root];
    while (frontier.length) {
      const next = [];
      frontier.forEach(n => n.outgoers("edge").forEach(e => { const t = e.target(); if (!keep.has(t.id())) { keep.add(t.id()); next.push(t); } }));
      frontier = next;
    }
    gt.batch(() => {
      gt.elements().addClass("faded").removeClass("sel");
      gt.nodes().forEach(n => { if (keep.has(n.id())) n.removeClass("faded"); });
      gt.edges().forEach(e => { if (keep.has(e.source().id()) && keep.has(e.target().id())) e.removeClass("faded"); });
      root.addClass("sel").removeClass("faded");
    });
  }
  function showState(node) {
    gt.elements().removeClass("sel"); node.addClass("sel");
    const s = node.data("snap") || {};
    const committed = node.data("committed") || [], refused = node.data("refused") || [];
    let h = `<h2>State ${esc(node.id() === "genesis" ? "genesis" : node.id())}</h2>`;
    h += `<p class=muted>depth ${node.data("depth")} · ${s.cell_count || 0} cells · ${committed.length} committed / ${refused.length} refused turns from here</p>`;
    h += "<h3>Cell snapshot</h3><table>";
    (s.cells || []).forEach(c => { h += `<tr><td class=id>${esc(c.short)}</td><td><span class=bal>${c.balance == null ? "" : c.balance}</span> ${esc(c.kind)} · ${c.cap_edges} caps</td></tr>`; });
    h += "</table>";
    if (committed.length) {
      h += "<h3>Committed turns →</h3>";
      committed.forEach(i => { h += `<div class=kv><span class="badge committed">✓</span> <span>${esc(i.cell)} · <b>${esc(i.message)}</b> ${chip("effect:" + i.effect)}${i.to_existing ? ' <span class=muted>↺ rejoins</span>' : ''}</span></div>`; });
    }
    if (refused.length) {
      h += "<h3>Refused turns ✕</h3>";
      refused.forEach(i => { h += `<div class=kv><span class="badge refused">${i.by_executor ? "exec" : "cap"}</span> <span>${esc(i.cell)} · <b>${esc(i.message)}</b> ${chip("effect:" + i.effect)}</span></div>`; });
    }
    $("#gtPanel").innerHTML = h;
  }
  function showTransition(edge) {
    gt.elements().removeClass("sel"); edge.addClass("sel");
    const i = edge.data("info");
    let h = `<h2>Turn: ${esc(i.message)}</h2>`;
    h += `<div class=kv><b>on cell</b><span>${chip("cell:" + i.cell)}</span></div>`;
    h += `<div class=kv><b>effect</b><span>${chip("effect:" + i.effect)}</span></div>`;
    h += `<div class=kv><b>requires</b><span>${esc(i.required)}</span></div>`;
    h += `<div class=kv><b>authorized</b><span>${i.authorized ? "yes" : "no"}</span></div>`;
    h += `<div class=kv><b>outcome</b><span class="badge ${i.outcome}">${i.outcome}</span></div>`;
    if (i.outcome === "committed") {
      h += `<div class=kv><b>computrons</b><span>${i.computrons}</span></div>`;
      h += `<div class=kv><b>post-state</b><span class="chip state" data-go="state:${esc(i.to)}">${esc(i.to === "genesis" ? "genesis" : i.to.slice(0, 8))}</span></div>`;
      h += `<p class=muted>A real verified turn. The world advanced to a new state.</p>`;
    } else {
      h += `<div class=kv><b>refused by</b><span>${i.by_executor ? "the verified executor (a guarantee fired)" : "the cap-gate (anti-ghost, before any turn)"}</span></div>`;
      h += `<div class=prose>${esc(i.reason || "")}</div>`;
    }
    $("#gtPanel").innerHTML = h;
  }

  // ═══ OCAP WEB ═══════════════════════════════════════════════════════════
  let oc = null;
  function buildOcap() {
    const O = (A.cells && A.cells.ocap) || { nodes: [], edges: [] };
    const els = [];
    O.nodes.forEach(n => els.push({ data: { id: n.id, label: n.id, balance: n.balance, lifecycle: n.lifecycle } }));
    O.edges.forEach((e, i) => els.push({ data: { id: "oe" + i, source: e.from, target: e.to, label: "slot " + e.slot + " · " + e.rights } }));
    oc = cytoscape({
      container: $("#cyo"), elements: els,
      style: [
        { selector: "node", style: { "background-color": "#1f6feb", "border-color": "#58a6ff", "border-width": 2, "label": "data(label)", "color": "#c9d1d9", "font-size": 10, "width": 30, "height": 30, "text-valign": "bottom", "text-margin-y": 4 } },
        { selector: 'node[balance < 0]', style: { "background-color": "#bc8cff", "border-color": "#bc8cff" } },
        { selector: "edge", style: { "width": 2, "line-color": "#8b949e", "target-arrow-color": "#8b949e", "target-arrow-shape": "triangle", "curve-style": "bezier", "label": "data(label)", "font-size": 8, "color": "#8b949e", "text-rotation": "autorotate" } },
        { selector: ".sel", style: { "border-color": "#f0883e", "border-width": 4 } },
      ],
      layout: { name: "cose", animate: false, nodeRepulsion: 9000, idealEdgeLength: 120 },
      wheelSensitivity: 0.25,
    });
    oc.on("tap", "node", ev => selectOcap(ev.target.id()));
  }
  function selectOcap(short) {
    if (oc) { oc.elements().removeClass("sel"); const n = oc.getElementById(short); if (n.length) n.addClass("sel"); }
    const o = REG.get("cell:" + short);
    if (o) { $("#ocapPanel").innerHTML = detailHtml(o); return; }
    const c = cells.find(x => x.short === short);
    $("#ocapPanel").innerHTML = c ? detailHtml(REG.get("cell:" + c.short)) : `<h2>${esc(short)}</h2><p class=muted>no detail</p>`;
  }

  // ═══ SURFACES (the visual UI atlas) ═════════════════════════════════════
  // The FIVE MODES (cockpit/frame.rs · CockpitMode) — the coherent frame the
  // ~30 surfaces are re-homed under. The gallery groups by `surface.mode`.
  const MODES = [
    ["inhabit", "🏡 Inhabit", "your living world"],
    ["author",  "✎ Author",   "make things"],
    ["dev",     "⌨ Dev",       "the IDE"],
    ["inspect", "🔍 Inspect",  "understand"],
    ["operate", "⚙ Operate",   "the machinery"],
  ];
  const MODE_LABEL = Object.fromEntries(MODES.map(m => [m[0], m[1]]));
  function surfaceCard(s) {
    const reg = REG.get("surface:" + s.tab) || { rel: {} };
    const modeBadge = s.mode ? `<span class=tag title="${esc(MODE_LABEL[s.mode] || s.mode)}">${esc(MODE_LABEL[s.mode] || s.mode)}</span>` : "";
    return `
      <div class=card data-card="surface:${esc(s.tab)}">
        ${s.file
          ? `<a class=shot href="screenshots/${esc(s.file)}" data-light="${esc(s.file)}" data-cap="${esc(s.tab)}"><img src="screenshots/${esc(s.file)}" loading=lazy alt="${esc(s.tab)}"></a>`
          : `<div class=noshot>no screenshot yet — run shoot.py</div>`}
        <div class=cap><b>${esc(s.label || s.tab)}</b> <span class=muted>${esc(s.size || "")}</span> ${modeBadge}
          <div class=desc>${esc(s.explainer || "")}</div>
          ${(reg.rel.component || []).length ? `<div class=relgroup><span class=lbl>components</span><div class=tagrow>${chips(reg.rel.component)}</div></div>` : ""}
          <div class=minilink><a href="pages/surfaces/${esc(s.tab)}.html" target=_blank>full explainer →</a> · <a data-go="surface:${esc(s.tab)}">in the web →</a></div>
        </div>
      </div>`;
  }
  function buildGallery() {
    const g = $("#gallery");
    if (!surfaces.length) { g.innerHTML = `<p class=muted style="padding:18px">No surface screenshots yet — run shoot.py.</p>`; return; }
    let h = `<div class=galhead><h2>Surface atlas — ${surfaces.length} cockpit surfaces</h2>
      <p>Every rendered surface of the live cockpit, shot from the real embedded executor — now inside the coherent <b>five-mode frame</b> (a top bar, a left rail of the five modes, a mode sub-nav, a dev dock). Click a shot to enlarge; click through for its full explainer + the components it is built from.</p></div>`;
    const byTab = Object.fromEntries(surfaces.map(s => [s.tab, s]));
    const claimed = new Set();
    // 1) the frame itself (the chrome), then 2) each mode's surfaces, then 3) the rest.
    if (byTab.frame) { h += `<div class=galsec><h3>The frame · the persistent chrome</h3></div>` + surfaceCard(byTab.frame); claimed.add("frame"); }
    for (const [mid, mlabel, blurb] of MODES) {
      const inMode = surfaces.filter(s => s.mode === mid);
      if (!inMode.length) continue;
      h += `<div class=galsec><h3>${esc(mlabel)} <span class=muted>· ${esc(blurb)}</span></h3></div>`;
      h += inMode.map(s => { claimed.add(s.tab); return surfaceCard(s); }).join("");
    }
    const rest = surfaces.filter(s => !claimed.has(s.tab));
    if (rest.length) {
      h += `<div class=galsec><h3>Beyond the frame <span class=muted>· demonstrations + external bakes</span></h3></div>`;
      h += rest.map(surfaceCard).join("");
    }
    g.innerHTML = h;
  }
  function openSurface(tab) {
    activate("surfaces");
    const card = $(`[data-card="surface:${cssesc(tab)}"]`);
    if (card) { card.scrollIntoView({ behavior: "smooth", block: "center" }); flash(card); }
  }

  // ═══ COMPONENTS (the gpui-component widget pillar) ══════════════════════
  function buildComponents() {
    const g = $("#components");
    if (!components.length) {
      g.innerHTML = `<div class=galhead><h2>Components</h2>
        <p>The gpui-component widget pillar — the visual building blocks the cockpit
        surfaces are made of. Not populated yet: <code>data/components.json</code> is
        absent. Run the generator to populate this pillar.</p></div>`;
      return;
    }
    const groups = {};
    components.forEach(c => { (groups[c.group || "widgets"] = groups[c.group || "widgets"] || []).push(c); });
    const live = components.filter(c => c.used_in_deos).length;
    let h = `<div class=galhead><h2>Component pillar — ${components.length} widgets</h2>
      <p>The gpui-component library (vendored, Apache-2.0) the cockpit is built from —
      the visual building blocks beneath every surface. <span class=ok>●</span> ${live}
      are driven directly in the live cockpit today; the rest of the palette is
      available + documented here. Each widget links to the surfaces that render it.</p></div>`;
    Object.keys(groups).sort().forEach(grp => {
      h += `<div class=compgroup><h3>${esc(grp)} · ${groups[grp].length}</h3></div>`;
      h += groups[grp].map(c => {
        const o = REG.get("component:" + c.name);
        return `<div class="card comp" data-card="component:${esc(c.name)}">
          <div class=swatch>${esc(c.glyph || ICON.component)}</div>
          <div class=cap><b>${esc(c.name)}</b> ${c.used_in_deos ? '<span class="badge committed" title="used in the live cockpit">live</span>' : ''}
            <div class=desc>${esc(c.summary || c.role || "")}</div>
            ${o && (o.rel.surface || []).length ? `<div class=relgroup><span class=lbl>renders</span><div class=tagrow>${chips(o.rel.surface)}</div></div>` : ""}
            ${o && (o.rel.verb || []).length ? `<div class=relgroup><span class=lbl>drives</span><div class=tagrow>${chips(o.rel.verb)}</div></div>` : ""}
            <div class=minilink><a data-go="component:${esc(c.name)}">in the web →</a></div>
          </div></div>`;
      }).join("");
    });
    g.innerHTML = h;
  }
  function openComponent(name) {
    activate("components");
    const card = $(`[data-card="component:${cssesc(name)}"]`);
    if (card) { card.scrollIntoView({ behavior: "smooth", block: "center" }); flash(card); }
  }

  // ═══ PROTOCOL ═══════════════════════════════════════════════════════════
  function buildProtocol() {
    const p = protocol; const lat = p.auth_required_lattice || {};
    let h = "<h2>Protocol reference</h2>";
    h += "<h3>The AuthRequired lattice</h3>";
    h += `<p class=mono>${esc(lat.order || "")}</p>`;
    h += `<p>Tiers: ${(lat.tiers || []).map(esc).join(" · ")}</p>`;
    h += `<p class=muted>${esc(lat.note || "")}</p>`;
    h += "<h3>The eight verbs</h3><div class=chips>" + VERBS.map(v => chip(v.id)).join("") + "</div>";
    h += "<h3>Effects seen live</h3><div class=chips>" + (p.effects_seen || []).map(e => chip("effect:" + e)).join("") + "</div>";
    h += "<h3>Refusal taxonomy</h3><ul>" + Object.entries(p.refusal_taxonomy || {}).map(([k, v]) => `<li><strong>${esc(k)}</strong>: ${esc(v)}</li>`).join("") + "</ul>";
    const sec = A.sections || {};
    ["thesis", "verbs", "substances", "auth-lattice", "refusal", "receipts", "scripts", "macros-as-custom-vk"].forEach(slug => { if (sec[slug]) h += `<h3 id="${slug}">${slug}</h3>` + sec[slug]; });
    h += `<hr style="border-color:#21262d;margin:20px 0">`;
    h += `<p><a href="pages/faces.html" target=_blank>↗ the presentation faces (deep)</a> &nbsp;·&nbsp; <a href="pages/protocol-deep.html" target=_blank>↗ protocol (deep)</a> &nbsp;·&nbsp; <a href="pages/protocol.html" target=_blank>↗ protocol summary</a></p>`;
    $("#protocol").innerHTML = h;
  }

  // ═══ ABOUT ══════════════════════════════════════════════════════════════
  function buildAbout() {
    const ex = (A.explainers && A.explainers.about) || "The Dregg Atlas — a self-built map of the live verified ocap image.";
    $("#about").innerHTML = mdLite(ex);
  }
  function mdLite(t) {
    const out = []; let inCode = false, inList = false;
    t.split("\n").forEach(l => {
      if (l.trim().startsWith("```")) { out.push(inCode ? "</code></pre>" : "<pre><code>"); inCode = !inCode; return; }
      if (inCode) { out.push(esc(l)); return; }
      if (l.startsWith("## ")) { if (inList) { out.push("</ul>"); inList = false; } return out.push(`<h3>${esc(l.slice(3))}</h3>`); }
      if (l.startsWith("# ")) { if (inList) { out.push("</ul>"); inList = false; } return out.push(`<h2>${esc(l.slice(2))}</h2>`); }
      if (l.trim().startsWith("- ")) { if (!inList) { out.push("<ul>"); inList = true; } return out.push(`<li>${esc(l.trim().slice(2))}</li>`); }
      if (inList) { out.push("</ul>"); inList = false; }
      if (l.trim()) out.push(`<p>${esc(l)}</p>`);
    });
    if (inList) out.push("</ul>"); if (inCode) out.push("</code></pre>");
    return out.join("");
  }

  // ═══ ⌘K SPOTTER ═════════════════════════════════════════════════════════
  const spotIndex = [];
  REG.forEach(o => { if (o.type !== "state") spotIndex.push(o); });
  let spotSel = 0, spotMatches = [];
  function openSpotter() {
    $("#spotter").hidden = false;
    const inp = $("#spotinput"); inp.value = ""; inp.focus();
    runSpot("");
  }
  function closeSpotter() { $("#spotter").hidden = true; }
  function runSpot(q) {
    q = q.trim().toLowerCase();
    let m = spotIndex;
    if (q) {
      m = spotIndex.map(o => {
        const n = o.name.toLowerCase(), l = o.label.toLowerCase();
        let score = 0;
        if (n === q) score = 100; else if (n.startsWith(q)) score = 70; else if (n.includes(q)) score = 40;
        else if (l.includes(q)) score = 20; else if (o.type.startsWith(q)) score = 10;
        return { o, score };
      }).filter(x => x.score > 0).sort((a, b) => b.score - a.score).map(x => x.o);
    } else {
      const order = { surface: 0, component: 1, cell: 2, verb: 3, effect: 4 };
      m = spotIndex.slice().sort((a, b) => (order[a.type] - order[b.type]) || a.name.localeCompare(b.name));
    }
    spotMatches = m.slice(0, 60); spotSel = 0; renderSpot();
  }
  function renderSpot() {
    $("#spotresults").innerHTML = spotMatches.map((o, i) => {
      const sub = o.type === "cell" ? (o.data && o.data.id || "") :
        o.type === "surface" ? (o.data && o.data.explainer || "") :
        o.type === "component" ? (o.data && (o.data.summary || o.data.module) || "") :
        o.type === "effect" ? "effect" : o.label;
      return `<div class="spotrow ${i === spotSel ? "sel" : ""}" data-i="${i}">
        <span class="ty ${o.type}">${esc(o.type)}</span>
        <span class=nm>${esc(o.label)}</span>
        <span class=sub>${esc(sub)}</span></div>`;
    }).join("") || `<div class=spotrow><span class=nm class=muted>no match</span></div>`;
  }
  function spotOpen(i) { const o = spotMatches[i]; if (o) { closeSpotter(); go(o.id); } }
  $("#spotbtn").addEventListener("click", openSpotter);
  $("#spotinput").addEventListener("input", e => runSpot(e.target.value));
  $("#spotresults").addEventListener("click", e => { const r = e.target.closest(".spotrow"); if (r && r.dataset.i != null) spotOpen(+r.dataset.i); });
  $("#spotresults").addEventListener("mousemove", e => { const r = e.target.closest(".spotrow"); if (r && r.dataset.i != null) { spotSel = +r.dataset.i; renderSpot(); } });
  $("#spotter").addEventListener("click", e => { if (e.target.id === "spotter") closeSpotter(); });
  document.addEventListener("keydown", e => {
    if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "k") { e.preventDefault(); $("#spotter").hidden ? openSpotter() : closeSpotter(); return; }
    if ($("#spotter").hidden) { if (e.key === "/" && document.activeElement.tagName !== "INPUT") { e.preventDefault(); openSpotter(); } return; }
    if (e.key === "Escape") closeSpotter();
    else if (e.key === "ArrowDown") { e.preventDefault(); spotSel = Math.min(spotSel + 1, spotMatches.length - 1); renderSpot(); scrollSel(); }
    else if (e.key === "ArrowUp") { e.preventDefault(); spotSel = Math.max(spotSel - 1, 0); renderSpot(); scrollSel(); }
    else if (e.key === "Enter") { e.preventDefault(); spotOpen(spotSel); }
  });
  function scrollSel() { const el = $(".spotrow.sel"); if (el) el.scrollIntoView({ block: "nearest" }); }

  // ═══ LIGHTBOX (enlarge any screenshot) ══════════════════════════════════
  const lb = document.createElement("div"); lb.className = "lightbox";
  lb.innerHTML = `<img><div class=lbcap></div>`; document.body.appendChild(lb);
  lb.addEventListener("click", () => lb.classList.remove("on"));
  document.addEventListener("click", e => {
    const a = e.target.closest("[data-light]"); if (!a) return;
    e.preventDefault();
    const f = a.dataset.light;
    lb.querySelector("img").src = a.dataset.raw ? f : "screenshots/" + f;
    lb.querySelector(".lbcap").textContent = a.dataset.cap || "";
    lb.classList.add("on");
  });

  // misc helpers
  function cssesc(s) { return String(s).replace(/["\\]/g, "\\$&"); }
  function flash(el) { el.style.transition = "box-shadow .2s"; el.style.boxShadow = "0 0 0 2px #f0883e"; setTimeout(() => { el.style.boxShadow = ""; }, 900); }

  // ─── boot ────────────────────────────────────────────────────────────────
  buildGameTree(); buildOcap(); buildGallery(); buildComponents(); buildProtocol(); buildAbout(); buildMap();
  activate(location.hash.slice(1) || "surfaces");

  const params = new URLSearchParams(location.search);
  const sel = params.get("select");
  if (sel && gt) { activate("gametree"); selectState(sel); }
  const goId = params.get("go");
  if (goId && REG.get(goId)) go(goId);
})();
