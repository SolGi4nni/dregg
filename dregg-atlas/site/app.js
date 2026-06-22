/* THE DREGG ATLAS — the SPA. Renders the game tree + ocap web as live cytoscape
   graphs over the crawl data (window.ATLAS), with click-through detail panels,
   a screenshot gallery and the protocol reference. */
(function () {
  const A = window.ATLAS || {};
  const $ = (s, r) => (r || document).querySelector(s);
  const esc = (s) => String(s == null ? "" : s).replace(/[&<>]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
  if (window.cytoscape && window.cytoscapeDagre) cytoscape.use(window.cytoscapeDagre);

  // ---- nav (with #hash deep-links) ----------------------------------------
  function activate(v) {
    document.querySelectorAll("nav.tabs button").forEach(x => x.classList.toggle("on", x.dataset.v === v));
    document.querySelectorAll(".view").forEach(x => x.classList.toggle("on", x.dataset.v === v));
    if (v === "gametree" && gt) { gt.resize(); gt.fit(null, 40); }
    if (v === "ocap" && oc) { oc.resize(); oc.fit(null, 40); }
    if (v === "uitree" && ut) { ut.resize(); ut.fit(null, 40); }
  }
  $("#tabs").addEventListener("click", e => {
    const b = e.target.closest("button"); if (!b) return;
    location.hash = b.dataset.v;
  });
  window.addEventListener("hashchange", () => activate(location.hash.slice(1) || "gametree"));

  const gtm = (A.gametree && A.gametree.meta) || {};
  const uic = (A.uitree && A.uitree.node_count) || 0;
  $("#stat").textContent =
    `${gtm.node_count || 0} states · ${gtm.committed_edges || 0} committed · ${gtm.refused_edges || 0} refused · ${uic} UI states · ${(A.cells.cells || []).length} cells`;

  // ---- GAME TREE ----------------------------------------------------------
  let gt = null;
  function buildGameTree() {
    const G = A.gametree || { nodes: [], edges: [] };
    const els = [];
    const seen = new Set();
    // refused moves are annotations on their source state, not graph edges
    // (they are self-loops that would wreck the layout); collect them per node.
    const refusedBy = {}, committedBy = {};
    G.edges.forEach(e => {
      (e.outcome === "committed" ? committedBy : refusedBy)[e.from] =
        ((e.outcome === "committed" ? committedBy : refusedBy)[e.from]) || [];
      (e.outcome === "committed" ? committedBy : refusedBy)[e.from].push(e);
    });
    G.nodes.forEach(n => {
      seen.add(n.digest);
      const committed = committedBy[n.digest] || [];
      els.push({ data: { id: n.digest, label: n.digest === "genesis" ? "genesis" : n.digest.slice(0, 8), depth: n.depth, snap: n.snapshot, refused: refusedBy[n.digest] || [], committed, leaf: committed.length === 0 } });
    });
    let ei = 0;
    G.edges.forEach(e => {
      if (e.outcome !== "committed") return;       // only committed edges form the DAG
      if (!seen.has(e.to)) return;
      els.push({
        data: { id: "e" + (ei++), source: e.from, target: e.to, outcome: "committed", label: e.cell + " · " + e.message, info: e }
      });
    });
    gt = cytoscape({
      container: $("#cy"),
      elements: els,
      style: [
        // nodes coloured by depth so the tree's strata read at a glance
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
      layout: {
        name: "concentric",
        concentric: n => 100 - (n.data("depth") || 0),   // genesis (depth 0) at the centre
        levelWidth: () => 1,
        minNodeSpacing: 14,
        spacingFactor: 1.0,
        animate: false,
      },
      wheelSensitivity: 0.3,
    });
    gt.on("tap", "node", ev => { showState(ev.target); highlightSubtree(ev.target); });
    gt.on("tap", "edge", ev => showTransition(ev.target));
    gt.on("tap", ev => { if (ev.target === gt) { gt.elements().removeClass("faded sel"); } });
    gt.ready(() => gt.fit(null, 40));
    gt.one("layoutstop", () => gt.fit(null, 40));
  }

  // highlight a state's reachable subtree (committed descendants), fade the rest
  function highlightSubtree(root) {
    const keep = new Set([root.id()]);
    let frontier = [root];
    while (frontier.length) {
      const next = [];
      frontier.forEach(n => n.outgoers("edge").forEach(e => {
        const t = e.target();
        if (!keep.has(t.id())) { keep.add(t.id()); next.push(t); }
      }));
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
    (s.cells || []).forEach(c => {
      h += `<tr><td class=id>${esc(c.short)}</td><td><span class=bal>${c.balance == null ? "" : c.balance}</span> ${esc(c.kind)} · ${c.cap_edges} caps</td></tr>`;
    });
    h += "</table>";
    if (committed.length) {
      h += "<h3>Committed turns →</h3>";
      committed.forEach(i => {
        h += `<div class=kv><span class="badge committed">✓</span> <span>${esc(i.cell)} · <b>${esc(i.message)}</b> <span class=muted>(${esc(i.effect)})</span>${i.to_existing ? ' <span class=muted>↺ rejoins</span>' : ''}</span></div>`;
      });
    }
    if (refused.length) {
      h += "<h3>Refused turns ✕</h3>";
      refused.forEach(i => {
        h += `<div class=kv><span class="badge refused">${i.by_executor ? "exec" : "cap"}</span> <span>${esc(i.cell)} · <b>${esc(i.message)}</b> <span class=muted>(${esc(i.effect)})</span></span></div>`;
      });
    }
    $("#gtPanel").innerHTML = h;
  }

  function showTransition(edge) {
    gt.elements().removeClass("sel"); edge.addClass("sel");
    const i = edge.data("info");
    let h = `<h2>Turn: ${esc(i.message)}</h2>`;
    h += `<div class=kv><b>on cell</b><span class=id>${esc(i.cell)}</span></div>`;
    h += `<div class=kv><b>effect</b><span>${esc(i.effect)}</span></div>`;
    h += `<div class=kv><b>requires</b><span>${esc(i.required)}</span></div>`;
    h += `<div class=kv><b>authorized</b><span>${i.authorized ? "yes" : "no"}</span></div>`;
    h += `<div class=kv><b>outcome</b><span class="badge ${i.outcome}">${i.outcome}</span></div>`;
    if (i.outcome === "committed") {
      h += `<div class=kv><b>computrons</b><span>${i.computrons}</span></div>`;
      h += `<div class=kv><b>post-state</b><span class=id>${esc(i.to)}</span></div>`;
      h += `<p class=muted>A real verified turn. The world advanced to a new state.</p>`;
    } else {
      h += `<div class=kv><b>refused by</b><span>${i.by_executor ? "the verified executor (a guarantee fired)" : "the cap-gate (anti-ghost, before any turn)"}</span></div>`;
      h += `<div class=prose>${esc(i.reason || "")}</div>`;
    }
    $("#gtPanel").innerHTML = h;
  }

  // ---- UI TREE ------------------------------------------------------------
  let ut = null;
  function buildUiTree() {
    const U = A.uitree || { nodes: [], edges: [] };
    if (!U.nodes.length) { $("#cyui").innerHTML = '<p class=muted style="padding:18px">No UI-exploration crawl yet — run --explore-ui.</p>'; return; }
    const byKey = {}; U.nodes.forEach(n => byKey[n.key] = n);
    const els = [];
    U.nodes.forEach(n => {
      const tab = n.tab || (n.key.split("|")[0]);
      const isBase = (n.key.split("|")[1] || "") === "";
      els.push({ data: { id: n.key, label: isBase ? tab : (n.key.split("|")[1] || tab), tab, png: n.png, base: isBase } });
    });
    let ei = 0;
    U.edges.forEach(e => {
      if (!byKey[e.from] || !byKey[e.to]) return;
      if (e.from === e.to) return;
      els.push({ data: { id: "u" + (ei++), source: e.from, target: e.to, label: e.label } });
    });
    ut = cytoscape({
      container: $("#cyui"), elements: els,
      style: [
        { selector: "node", style: { "background-color": "#1f6feb", "label": "data(label)", "color": "#8b949e", "font-size": 8, "width": 12, "height": 12, "border-width": 1, "border-color": "#30363d", "text-valign": "bottom", "text-margin-y": 2, "min-zoomed-font-size": 6 } },
        { selector: 'node[?base]', style: { "background-color": "#3fb950", "border-color": "#56d364", "width": 20, "height": 20, "color": "#c9d1d9", "font-size": 10, "shape": "round-rectangle" } },
        { selector: 'node[id = "HOME|"]', style: { "background-color": "#f0883e", "border-color": "#f0883e", "width": 28, "height": 28, "font-size": 12 } },
        { selector: "edge", style: { "width": 1.1, "curve-style": "bezier", "target-arrow-shape": "triangle", "arrow-scale": 0.6, "line-color": "#30363d", "target-arrow-color": "#484f58", "font-size": 6, "color": "#6e7681", "label": "data(label)", "text-rotation": "autorotate", "min-zoomed-font-size": 9 } },
        { selector: ".sel", style: { "border-color": "#f0883e", "border-width": 4, "background-color": "#f0883e" } },
        { selector: ".faded", style: { "opacity": 0.1 } },
      ],
      layout: { name: "breadthfirst", roots: ["HOME|"], circle: true, spacingFactor: 1.4, avoidOverlap: true, animate: false },
      wheelSensitivity: 0.3,
    });
    ut.on("tap", "node", ev => showUiState(ev.target));
    ut.on("tap", ev => { if (ev.target === ut) ut.elements().removeClass("faded sel"); });
    ut.ready(() => ut.fit(null, 40));
    ut.one("layoutstop", () => ut.fit(null, 40));
  }

  function showUiState(node) {
    ut.elements().removeClass("sel faded"); node.addClass("sel");
    const out = node.outgoers("edge");
    let h = `<h2>${esc(node.data("tab"))}</h2><p class=muted>${esc(node.id())}</p>`;
    if (node.data("png")) h += `<img src="${esc(node.data("png"))}" loading=lazy>`;
    h += `<h3>Interactions from here</h3>`;
    if (!out.length) h += `<p class=muted>(leaf — no further navigation explored)</p>`;
    out.forEach(e => {
      h += `<div class=kv><span class=badge>${esc(e.data("label"))}</span> <span>→ ${esc((e.target().data("key") || e.target().id()).split("|")[1] || e.target().data("tab"))}</span></div>`;
    });
    $("#uiPanel").innerHTML = h;
  }

  // ---- OCAP WEB -----------------------------------------------------------
  let oc = null;
  function buildOcap() {
    const O = (A.cells && A.cells.ocap) || { nodes: [], edges: [] };
    const cellByShort = {}; (A.cells.cells || []).forEach(c => cellByShort[c.short] = c);
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
    oc.on("tap", "node", ev => {
      oc.elements().removeClass("sel"); ev.target.addClass("sel");
      showCell(ev.target.id());
    });
  }

  function showCell(short) {
    const c = (A.cells.cells || []).find(x => x.short === short);
    if (!c) { $("#ocapPanel").innerHTML = `<h2>${esc(short)}</h2><p class=muted>no detail</p>`; return; }
    let h = `<h2>Cell ${esc(c.short)}</h2><p class=muted>${esc(c.id)}</p>`;
    h += `<p>Halo: ${(c.halo || []).map(esc).join(" · ")} · <a href="pages/cells/${esc(c.short.replace(/…/g, "_"))}.html" target=_blank>static page ↗</a></p>`;
    h += "<h3>Affordances</h3><table>";
    (c.affordances || []).forEach(a => {
      h += `<tr><td class=k>${esc(a.name)}</td><td>${esc(a.effect)} <span class=muted>(${esc(a.required)})</span></td><td>${a.authorized ? '<span class=ok>●</span>' : '<span class=no>○</span>'}</td></tr>`;
    });
    h += "</table>";
    (c.faces || []).forEach(f => { h += faceHtml(f); });
    $("#ocapPanel").innerHTML = h;
  }

  function faceHtml(f) {
    const b = f.body || {}; let inner = "";
    if (b.shape === "fields") {
      inner = "<table>" + (b.fields.fields || []).map(fl => `<tr><td class=k>${esc(fl.key)}</td><td>${fieldVal(fl.value)}</td></tr>`).join("") + "</table>";
    } else if (b.shape === "graph") {
      inner = "<table>" + (b.edges || []).map(e => `<tr><td class=id>${esc(e.from)}</td><td>→ ${esc(e.to)} · ${esc(e.rights)}</td></tr>`).join("") + "</table>";
    } else if (b.shape === "prose") {
      inner = `<div class=prose>${esc(b.text)}</div>`;
    } else {
      inner = `<div class=prose>${esc(JSON.stringify(b).slice(0, 400))}</div>`;
    }
    return `<div class=face><h4>${esc(f.kind)} · ${esc(f.label)}</h4>${inner}</div>`;
  }
  function fieldVal(v) {
    if (!v) return "";
    if (v.t === "balance") return `<span class=bal>${v.v}</span>`;
    if (v.t === "id" || v.t === "hash") return `<span class=id title="${esc(v.v)}">${esc(v.short)}</span>`;
    if (v.t === "cap-edge") return `→ <span class=id>${esc(v.short)}</span> slot ${v.slot}`;
    return esc(v.v);
  }

  // ---- UI ATLAS (screenshots) --------------------------------------------
  function buildGallery() {
    const g = $("#gallery");
    const surf = A.surfaces || [];
    if (!surf.length) { g.innerHTML = `<p class=muted style="padding:18px">No surface screenshots yet — run shoot.py.</p>`; return; }
    g.innerHTML = surf.map(s => `
      <div class=card>
        <a href="pages/surfaces/${esc(s.tab)}.html" target=_blank><img src="screenshots/${esc(s.file)}" loading=lazy alt="${esc(s.tab)}"></a>
        <div class=cap><b>${esc(s.tab)}</b> <span class=muted>${esc(s.size || "")}</span>
        <div>${esc(s.explainer || "")}</div>
        <div style="margin-top:6px"><a href="pages/surfaces/${esc(s.tab)}.html" target=_blank>read the full explainer →</a></div></div>
      </div>`).join("");
  }

  // ---- PROTOCOL -----------------------------------------------------------
  function buildProtocol() {
    const p = A.protocol || {}; const lat = p.auth_required_lattice || {};
    let h = "<h2>Protocol reference</h2>";
    h += "<h3>The AuthRequired lattice</h3>";
    h += `<p class=mono>${esc(lat.order || "")}</p>`;
    h += `<p>Tiers: ${(lat.tiers || []).map(esc).join(" · ")}</p>`;
    h += `<p class=muted>${esc(lat.note || "")}</p>`;
    h += "<h3>The eight verbs</h3><ul>" + (p.the_eight_verbs || []).map(v => `<li>${esc(v)}</li>`).join("") + "</ul>";
    h += "<h3>Effects seen live</h3><ul>" + (p.effects_seen || []).map(e => `<li><code>${esc(e)}</code></li>`).join("") + "</ul>";
    h += "<h3>Refusal taxonomy</h3><ul>" + Object.entries(p.refusal_taxonomy || {}).map(([k, v]) => `<li><strong>${esc(k)}</strong>: ${esc(v)}</li>`).join("") + "</ul>";
    // the deep, code-grounded explainers (rendered inline, from explainers/protocol.md)
    const sec = A.sections || {};
    ["thesis", "verbs", "substances", "auth-lattice", "refusal", "receipts", "scripts", "macros-as-custom-vk"].forEach(slug => {
      if (sec[slug]) { h += `<h3 id="${slug}">${slug}</h3>` + sec[slug]; }
    });
    h += `<hr style="border-color:#21262d;margin:20px 0">`;
    h += `<p><a href="pages/faces.html" target=_blank>↗ the seven presentation faces (deep)</a> &nbsp;·&nbsp; <a href="pages/protocol-deep.html" target=_blank>↗ protocol (deep, standalone)</a> &nbsp;·&nbsp; <a href="pages/protocol.html" target=_blank>↗ protocol summary</a></p>`;
    $("#protocol").innerHTML = h;
  }

  // ---- ABOUT --------------------------------------------------------------
  function buildAbout() {
    const ex = (A.explainers && A.explainers.about) || "The Dregg Atlas — a self-built map of the live verified ocap image.";
    $("#about").innerHTML = mdLite(ex);
  }
  function mdLite(t) {
    return t.split("\n").map(l => {
      if (l.startsWith("## ")) return `<h3>${esc(l.slice(3))}</h3>`;
      if (l.startsWith("# ")) return `<h2>${esc(l.slice(2))}</h2>`;
      if (l.startsWith("- ")) return `<li>${esc(l.slice(2))}</li>`;
      if (l.trim()) return `<p>${esc(l)}</p>`;
      return "";
    }).join("");
  }

  // ---- boot ---------------------------------------------------------------
  buildGameTree(); buildUiTree(); buildOcap(); buildGallery(); buildProtocol(); buildAbout();
  activate(location.hash.slice(1) || "gametree");
  // deep-link a UI state: ?uistate=<index> (verification / sharing)
  const uiIdx = new URLSearchParams(location.search).get("uistate");
  if (uiIdx != null && ut) {
    const n = ut.nodes()[parseInt(uiIdx, 10) || 0];
    if (n) { activate("uitree"); ut.fit(n.closedNeighborhood(), 80); showUiState(n); }
  }
  // deep-link a selected state: ?select=<digest|genesis>
  const sel = new URLSearchParams(location.search).get("select");
  if (sel && gt) {
    const n = gt.getElementById(sel) || gt.nodes(`[label = "${sel}"]`).first();
    const node = (n && n.length) ? n : gt.getElementById("genesis");
    if (node && node.length) { gt.fit(node.closedNeighborhood(), 80); showState(node); highlightSubtree(node); }
  }
})();
