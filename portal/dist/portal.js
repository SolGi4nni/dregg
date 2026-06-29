
(function () {
  "use strict";
  var params = new URLSearchParams(location.search);
  // API base: ?api= override, else same-origin (Caddy proxies /api/* to the edge bot).
  var API = (params.get("api") || "").replace(/\/$/, "");
  function api(path) { return API + path; }
  function esc(s) {
    return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }
  function shortId(id) { return id && id.length > 18 ? id.slice(0, 10) + "…" + id.slice(-6) : id; }

  // ---- the live network view (index.html) ----------------------------------
  var cellsEl = document.getElementById("portal-cells");
  if (cellsEl) initNetworkView();

  function initNetworkView() {
    var statusEl = document.getElementById("portal-status");
    var graphSvg = document.getElementById("portal-graph-svg");

    function loadCells() {
      fetch(api("/api/cells"), { headers: { accept: "application/json" } })
        .then(function (r) { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
        .then(function (cells) {
          renderCells(cells);
          renderGraph(graphSvg, cells);
        })
        .catch(function (e) {
          cellsEl.innerHTML = '<div class="portal-err">could not load /api/cells: ' + esc(e.message) +
            '<br>if you are testing from another origin, append <code>?api=https://portal.dregg.studio</code></div>';
        });
    }

    function renderCells(cells) {
      if (!cells || !cells.length) { cellsEl.innerHTML = '<div class="portal-err">no cells reported.</div>'; return; }
      cellsEl.innerHTML = cells.map(function (c, i) {
        var hub = i === 0; // list_cells returns the bot/custodial cell first
        var tags = "";
        if (hub) tags += '<span class="portal-tag hub">custodial hub</span>';
        if (c.has_program) tags += '<span class="portal-tag prog">service cell</span>';
        if (c.nullifier_known) tags += '<span class="portal-tag">spent-seen</span>';
        return '<a class="portal-cell" href="./cell.html?id=' + encodeURIComponent(c.id) +
          (API ? "&api=" + encodeURIComponent(API) : "") + '">' +
          '<span class="portal-cell-id">' + esc(shortId(c.id)) + '</span>' +
          '<span class="portal-cell-row">balance <b>' + esc(c.balance) + '</b></span>' +
          '<span class="portal-cell-row">nonce <b>' + esc(c.nonce) + '</b></span>' +
          '<span class="portal-cell-row">capabilities <b>' + esc(c.capability_count) + '</b></span>' +
          (tags ? '<span class="portal-cell-tags">' + tags + '</span>' : '') +
          '</a>';
      }).join("");
    }

    function renderGraph(svg, cells) {
      if (!svg) return;
      var W = 600, H = 360, cx = W / 2, cy = H / 2;
      var hub = cells[0], spokes = cells.slice(1);
      var R = Math.min(W, H) / 2 - 50;
      var parts = [];
      // edges: hub -> each cell (the custodial relationship the read API exposes)
      spokes.forEach(function (c, i) {
        var a = (2 * Math.PI * i) / Math.max(1, spokes.length) - Math.PI / 2;
        var x = cx + R * Math.cos(a), y = cy + R * Math.sin(a);
        parts.push('<line class="edge" x1="' + cx + '" y1="' + cy + '" x2="' + x + '" y2="' + y + '"/>');
      });
      // spoke nodes
      spokes.forEach(function (c, i) {
        var a = (2 * Math.PI * i) / Math.max(1, spokes.length) - Math.PI / 2;
        var x = cx + R * Math.cos(a), y = cy + R * Math.sin(a);
        var r = 8 + Math.min(14, Math.log10(1 + Number(c.balance || 0)) * 4);
        parts.push('<a href="./cell.html?id=' + encodeURIComponent(c.id) + (API ? "&api=" + encodeURIComponent(API) : "") + '">' +
          '<circle class="node node-cell" cx="' + x + '" cy="' + y + '" r="' + r.toFixed(1) + '"><title>' + esc(c.id) + '</title></circle>' +
          '<text class="node-label" x="' + x + '" y="' + (y + r + 12) + '" text-anchor="middle">' + esc(shortId(c.id)) + '</text></a>');
      });
      // hub node (drawn last, on top)
      if (hub) {
        parts.push('<a href="./cell.html?id=' + encodeURIComponent(hub.id) + (API ? "&api=" + encodeURIComponent(API) : "") + '">' +
          '<circle class="node node-hub" cx="' + cx + '" cy="' + cy + '" r="18"><title>' + esc(hub.id) + ' (custodial hub)</title></circle>' +
          '<text class="node-label" x="' + cx + '" y="' + (cy + 32) + '" text-anchor="middle">hub</text></a>');
      }
      svg.innerHTML = parts.join("");
    }

    // liveness via the SSE observability stream (hello + 15s pings)
    function connectStream() {
      try {
        var es = new EventSource(api("/observability/stream"));
        es.addEventListener("hello", function (ev) {
          setLive("live · " + safeField(ev.data, "apps", "?") + " apps · " + safeField(ev.data, "nullifiers", "0") + " nullifiers seen");
          loadCells();
        });
        es.addEventListener("ping", function (ev) {
          setLive("live · seq " + safeField(ev.data, "seq", "?") + " · " + safeField(ev.data, "nullifiers", "0") + " nullifiers seen");
        });
        es.onerror = function () { if (statusEl) statusEl.classList.remove("live"); };
      } catch (e) { /* EventSource unsupported: the poll below still drives it */ }
    }
    function safeField(json, k, dflt) { try { var o = JSON.parse(json); return o[k] != null ? o[k] : dflt; } catch (e) { return dflt; } }
    function setLive(text) { if (statusEl) { statusEl.classList.add("live"); statusEl.innerHTML = '<span class="dot"></span>' + esc(text); } }

    loadCells();
    connectStream();
    setInterval(loadCells, 20000); // gentle refresh in case SSE is proxied without flush
  }

  // ---- the trustless cell card (cell.html) ---------------------------------
  var content = document.getElementById("deos-content");
  if (content && params.get("id")) initCellView(content, params.get("id"));

  function initCellView(content, id) {
    fetch(api("/api/cell/" + encodeURIComponent(id)), { headers: { accept: "application/json" } })
      .then(function (r) { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
      .then(function (c) { fillCell(content, c); })
      .catch(function (e) {
        content.innerHTML = '<div class="deos-vstack"><span class="portal-err">could not load this cell: ' + esc(e.message) + '</span></div>';
      });
  }

  function fillCell(content, c) {
    var found = c.found;
    var rows = [
      ["cell", c.id],
      ["found on chain", found ? "yes" : "no"],
      ["balance", c.balance],
      ["nonce", c.nonce],
      ["capabilities", c.capability_count],
      ["has program", c.has_program ? "yes" : "no"]
    ];
    if (c.program_vk) rows.push(["program vk", shortId(c.program_vk)]);
    if (c.created_by_factory) rows.push(["minted by factory", shortId(c.created_by_factory)]);
    var body = '<div class="deos-vstack"><span class="deos-text" style="font-weight:700">Cell</span>' +
      '<div class="portal-card-fields">' +
      rows.map(function (r) {
        return '<div class="deos-row" style="justify-content:space-between">' +
          '<span class="deos-text">' + esc(r[0]) + '</span>' +
          '<span class="deos-bind">' + esc(r[1]) + '</span></div>';
      }).join("") +
      '</div>' +
      '<p class="portal-note">The fields above are <b>read live</b> from the edge node&rsquo;s API (the server&rsquo;s ' +
      'claim). The trust banner above runs a <b>recursive-STARK light client in this tab</b> that verifies a real ' +
      'finalized history end-to-end, re-witnessing nothing &mdash; the proof that the verification machinery is genuine ' +
      'and runs in your browser. Binding <i>this specific cell&rsquo;s</i> committed history (a server-supplied proof ' +
      'envelope + per-field heap openings) into that banner is the next rung.</p>' +
      '</div>';
    content.innerHTML = body;
  }
})();
