/* DreggNet portal — the live network view + the in-tab proof engine.
   The hero: a recursive-STARK light client (the dregg_wasm verifier) loads and
   verifies a real finalized history in YOUR browser, then the verification
   sweeps the living network. Read-only; ?api= override; same-origin proxy. */
(function () {
  "use strict";
  var params = new URLSearchParams(location.search);
  var API = (params.get("api") || "").replace(/\/$/, "");
  function api(path) { return API + path; }
  function esc(s) {
    return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }
  function shortId(id) { return id && id.length > 18 ? id.slice(0, 8) + "…" + id.slice(-6) : id; }
  var SVGNS = "http://www.w3.org/2000/svg";
  function svg(tag, attrs) { var e = document.createElementNS(SVGNS, tag); for (var k in attrs) if (attrs[k] != null) e.setAttribute(k, attrs[k]); return e; }
  var reduceMotion = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  var cellsEl = document.getElementById("portal-cells");
  if (cellsEl) initNetworkView();

  function initNetworkView() {
    var svgEl = document.getElementById("net-svg");
    var counterEl = document.getElementById("net-counter");
    var meterEl = document.getElementById("net-meter-fill");
    var netLive = document.getElementById("net-live");
    var netLiveText = document.getElementById("net-live-text");
    var trustchip = document.getElementById("trustchip");
    var trustText = document.getElementById("trustchip-text");

    var lastCells = [];
    var nodeById = {};        // cellId -> { group, lit }  (`lit` is DECORATION; nothing here verifies a cell)
    var enginePromise = null; // memoized wasm load+verify
    var verdict = null;

    // ---- engine (the live proof) -------------------------------------------
    var eng = {
      box: document.getElementById("engine"),
      shield: document.getElementById("engine-shield"),
      state: document.getElementById("engine-state"),
      sub: document.getElementById("engine-sub"),
      detail: document.getElementById("engine-detail"),
      runBtn: document.getElementById("engine-run")
    };
    function engReset() { if (eng.box) eng.box.className = "engine"; }
    function setTrust(cls, text) {
      if (trustchip) trustchip.className = "trustchip " + cls;
      if (trustText) trustText.textContent = text;
    }

    function runEngine() {
      if (enginePromise) return enginePromise;
      if (eng.box) eng.box.classList.add("scanning");
      if (eng.runBtn) { eng.runBtn.disabled = true; eng.runBtn.textContent = "verifying…"; }
      eng.shield.innerHTML = "&#9676;";
      eng.state.textContent = "Loading the verifier…";
      eng.sub.textContent = "instantiating the recursive-STARK light client (wasm)";
      eng.detail.innerHTML = '<div class="engine-prog"><i></i></div>';
      setTrust("live", "light client · loading wasm…");

      // The aggregate is PRE-FOLDED off the verifier (the producer's heavy step,
      // done once — ./history.json ships the wire envelope + the config VK
      // anchor). The tab does the light-client step only: the real recursion
      // verify. (Folding IN the tab is out of reach post-v12 — the fold's
      // working set exceeds wasm32's 4 GiB — and was never the story anyway:
      // the light client verifies, re-executing nothing.)
      enginePromise = Promise.all([
        import("./pkg/dregg_wasm.js").then(function (m) { return m.default().then(function () { return m; }); }),
        fetch("./history.json", { cache: "no-store" }).then(function (r) {
          if (!r.ok) throw new Error("history.json " + r.status);
          return r.json();
        })
      ]).then(function (loaded) {
        var m = loaded[0], baked = loaded[1];
        eng.state.textContent = "Checking a pre-folded history…";
        eng.sub.textContent = "one recursive proof over the whole committed chain — run here";
        // ⚑ WHICH ANCHOR. `?anchor=<64 hex>` comes out of the visitor's own URL — a value
        // this host did not put there. Absent one we fall back to `baked.anchor_hex`, which
        // arrives in the SAME `history.json` fetch as the proof, and every verdict says so.
        anchorUsed = urlAnchor() || String(baked.anchor_hex || "").trim().toLowerCase();
        anchorIsYours = !!urlAnchor();
        return new Promise(function (res) { setTimeout(res, reduceMotion ? 0 : 420); }).then(function () {
          return m.verify_devnet_history(JSON.stringify(baked.envelope), anchorUsed);
        });
      }).then(function (v) {
        verdict = v;
        if (eng.box) eng.box.classList.remove("scanning");
        if (v && v.aggregate_attested) {
          onVerified(v);
        } else {
          onRefused(v);
        }
        return v;
      }).catch(function (e) {
        if (eng.box) eng.box.classList.remove("scanning");
        eng.box && eng.box.classList.add("bad");
        eng.shield.innerHTML = "&#10007;";
        eng.state.textContent = "Engine failed to run";
        eng.sub.textContent = "the verifier could not start in this browser";
        eng.detail.innerHTML = '<div class="engine-floor">' + esc(String(e && e.message || e)) + "</div>";
        setTrust("", "light client · error");
        if (eng.runBtn) { eng.runBtn.disabled = false; eng.runBtn.textContent = "Retry →"; }
        enginePromise = null; // allow retry
        console.error("proof engine failed", e);
      });
      return enginePromise;
    }

    // ⚑ THE ANCHOR THE PRODUCER DOES NOT CONTROL — the sibling light-client page's repair
    // (`site/light-client/index.html`), applied to the portal, which was its unfixed twin.
    // MEASURED 2026-07-30: this page ran a genuine recursion verify and then printed
    // "Verified in your browser" and (index.html) "trusting no server", while the proof and
    // the VK anchor it was checked against arrived in ONE `history.json` fetch from ONE
    // origin. A hostile host swaps both halves and the ✓ still paints. The verify is real;
    // the trust claim over it was not.
    function urlAnchor() {
      var q;
      try { q = new URLSearchParams(location.search); } catch (e) { return ""; }
      var a = String(q.get("anchor") || "").trim().toLowerCase().replace(/^0x/, "");
      return /^[0-9a-f]{64}$/.test(a) ? a : "";
    }
    var anchorUsed = "", anchorIsYours = false;
    function anchorNote() {
      return anchorIsYours
        ? '<div class="engine-floor"><b>anchor:</b> YOUR <code>?anchor=</code> URL parameter \u2014 ' +
          'a value this host did not put here. This is a trust decision. <code>' + esc(anchorUsed) + '</code></div>'
        : '<div class="engine-floor"><b>anchor:</b> SERVED BY THIS HOST, in the same ' +
          '<code>history.json</code> as the proof. The verifier really did enforce it \u2014 but we handed ' +
          'you both halves, so this is a <b>consistency check, not a trust decision</b>. Append ' +
          '<code>?anchor=&lt;64 hex&gt;</code> to this URL to bring your own. <code>' + esc(anchorUsed) + '</code></div>';
    }

    function onVerified(v) {
      eng.box && eng.box.classList.add(anchorIsYours ? "ok" : "warn");
      eng.shield.innerHTML = anchorIsYours ? "&#10003;" : "&#8801;";
      eng.state.textContent = anchorIsYours
        ? "Verified in your browser, against your anchor"
        : "Consistent \u2014 checked against this host's own anchor";
      eng.sub.textContent = anchorIsYours
        ? "recursion checked · re-executing nothing"
        : "recursion checked · re-executing nothing · the anchor came from this host";
      var root = (v.final_root || []).join(", ");
      eng.detail.innerHTML =
        '<div class="engine-stats">' +
          '<div class="engine-stat"><div class="k">turns folded</div><div class="v">' + esc(v.num_turns) + "</div></div>" +
          '<div class="engine-stat"><div class="k">engine</div><div class="v" style="font-size:.74rem">' + esc(v.engine) + "</div></div>" +
          '<div class="engine-stat span2"><div class="k">commitment · final_root</div><div class="v root">[' + esc(root) + "]</div></div>" +
        "</div>" +
        anchorNote() +
        '<div class="engine-floor"><b>rests on:</b> ' + esc(v.named_floor || "FRI soundness + Poseidon2 collision-resistance") + "</div>";
      if (eng.runBtn) eng.runBtn.parentNode.style.display = "none";
      setTrust(anchorIsYours ? "ok" : "warn",
        anchorIsYours ? "light client · verified ✓" : "light client · consistent (host anchor) ≡");
      runSweep();
    }

    function onRefused(v) {
      eng.box && eng.box.classList.add("bad");
      eng.shield.innerHTML = "&#10007;";
      eng.state.textContent = "Attestation refused";
      eng.sub.textContent = "treat the served content as an unproven claim";
      eng.detail.innerHTML = '<div class="engine-floor">' + esc((v && v.named_floor) || "no verdict returned") + "</div>" + anchorNote();
      setTrust("", "light client · refused");
      if (eng.runBtn) { eng.runBtn.disabled = false; eng.runBtn.textContent = "Run again →"; }
    }

    // ---- the network animation ----------------------------------------------
    // ⚑ MEASURED 2026-07-30. This was called `runSweep` and it counted
    // "<b>N / N</b> cells whose aggregate verified under the live light client".
    // NOTHING WAS VERIFIED. `lightNode` is a `setTimeout` that adds a CSS class and
    // sets `n.verified = true` unconditionally; the counter is incremented by that
    // timer, over `lastCells` — a list fetched from `/api/cells`, i.e. supplied by
    // the very host under test. Adding a hundred fabricated cells to that endpoint
    // made this page report "100 / 100 cells verified" without a single proof.
    // ONE proof of ONE pre-folded history.json is verified in this file, at
    // `verify_devnet_history` above, and that is all.
    //
    // The animation is kept — it is a nice depiction of the topology and the page
    // is allowed to be pretty — and every word claiming it was a verification is
    // GONE. The class it adds is `lit`, not `verified`, so no stylesheet or
    // consumer can read a verdict out of the DOM either.
    function runSweep() {
      var spokes = lastCells.slice(1);
      var total = lastCells.length;
      var done = 0;
      function bump() {
        done++;
        if (counterEl) counterEl.innerHTML = "drawing · <b>" + done + "</b> / " + total + " cells";
        if (meterEl) meterEl.style.width = Math.round((done / Math.max(1, total)) * 100) + "%";
        if (done >= total && counterEl) counterEl.innerHTML =
          "<b>" + total + "</b> cells this node reports it hosts \u2014 <b>drawn, not verified</b>. " +
          "One proof was checked in this tab: the pre-folded history above. Nothing here checked " +
          "these cells, and this list came from the node.";
      }
      if (counterEl) counterEl.innerHTML = "drawing · <b>0</b> / " + total + " cells";
      var dur = reduceMotion ? 0 : Math.min(2600, 700 + total * 180);
      addRadar(dur);
      // hub verifies first (it is the anchor), then spokes by angle
      lightNode(lastCells[0] && lastCells[0].id, reduceMotion ? 0 : 120, bump);
      spokes.forEach(function (c, i) {
        var ang = (2 * Math.PI * i) / Math.max(1, spokes.length); // 0 at top going clockwise
        var t = reduceMotion ? 0 : 200 + (ang / (2 * Math.PI)) * dur;
        lightNode(c.id, t, bump);
      });
    }
    // ⚑ `lit`, never `verified`. This function checks NOTHING — it is a timer — and
    // both the flag and the CSS class it used to set said otherwise, which is how a
    // decorative animation came to drive a verification counter.
    function lightNode(id, delay, cb) {
      var n = nodeById[id];
      setTimeout(function () {
        if (n && n.group && !n.lit) { n.group.classList.add("lit"); n.lit = true; }
        var card = id && document.querySelector('.cell[data-id="' + cssesc(id) + '"]');
        if (card) card.classList.add("lit");
        cb && cb();
      }, delay);
    }
    function cssesc(s) { return String(s).replace(/["\\]/g, "\\$&"); }
    function addRadar(dur) {
      if (!svgEl || reduceMotion || dur <= 0) return;
      var cx = 380, cy = 220, R = 200;
      var g = svg("g", { class: "sweep" });
      var line = svg("line", { x1: cx, y1: cy, x2: cx, y2: cy - R, class: "sweep-line", opacity: "0.85" });
      var anim = svg("animateTransform", {
        attributeName: "transform", type: "rotate", from: "0 " + cx + " " + cy, to: "360 " + cx + " " + cy,
        dur: (dur / 1000) + "s", repeatCount: "1", fill: "freeze"
      });
      line.appendChild(anim);
      g.appendChild(line);
      svgEl.appendChild(g);
      setTimeout(function () { if (g.parentNode) g.parentNode.removeChild(g); }, dur + 200);
    }

    // ---- data load ----------------------------------------------------------
    function loadCells() {
      fetch(api("/api/cells"), { headers: { accept: "application/json" } })
        .then(function (r) { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
        .then(function (cells) {
          lastCells = cells || [];
          renderCells(lastCells);
          renderGraph(lastCells);
          if (verdict && verdict.aggregate_attested) { // already verified: re-light immediately
            lastCells.forEach(function (c) { lightNode(c.id, 0, function () {}); });
            if (counterEl) counterEl.innerHTML =
              "<b>" + lastCells.length + "</b> cells this node reports it hosts \u2014 <b>drawn, not verified</b>. " +
              "The one proof checked in this tab is the pre-folded history above.";
            if (meterEl) meterEl.style.width = "100%";
          }
        })
        .catch(function (e) {
          cellsEl.innerHTML = '<div class="err">could not reach <code>/api/cells</code> — ' + esc(e.message) +
            '<br>if you are testing from another origin, append <code>?api=https://portal.dregg.studio</code> to the URL.</div>';
          if (counterEl) counterEl.textContent = "network unreachable";
        });
    }

    function renderCells(cells) {
      if (!cells || !cells.length) {
        cellsEl.innerHTML = '<div class="empty" style="grid-column:1/-1"><div class="big">◯</div>no cells reported yet — the network is quiet. The light client is still live; open it again when cells appear.</div>';
        return;
      }
      cellsEl.innerHTML = cells.map(function (c, i) {
        var hub = i === 0;
        var tags = "";
        if (hub) tags += '<span class="tag hub">custodial hub</span>';
        if (c.has_program) tags += '<span class="tag prog">service cell</span>';
        if (c.nullifier_known) tags += '<span class="tag violet">spent-seen</span>';
        var href = "./cell.html?id=" + encodeURIComponent(c.id) + (API ? "&api=" + encodeURIComponent(API) : "");
        return '<a class="cell" data-id="' + esc(c.id) + '" href="' + href + '">' +
          '<div class="cell-top"><span class="cell-id">' + esc(shortId(c.id)) + '</span>' +
          '<span class="cell-vchip">verify →</span></div>' +
          '<div class="cell-rows">' +
          '<span class="cell-row">balance <b>' + esc(c.balance) + "</b></span>" +
          '<span class="cell-row">nonce <b>' + esc(c.nonce) + "</b></span>" +
          '<span class="cell-row">capabilities <b>' + esc(c.capability_count) + "</b></span></div>" +
          (tags ? '<div class="cell-tags">' + tags + "</div>" : "") +
          "</a>";
      }).join("");
    }

    function renderGraph(cells) {
      if (!svgEl) return;
      svgEl.innerHTML = "";
      nodeById = {};
      var defs = svg("defs", {});
      defs.innerHTML =
        '<radialGradient id="hubgrad" cx="50%" cy="40%" r="70%">' +
        '<stop offset="0%" stop-color="#6d86ff" stop-opacity="0.85"/>' +
        '<stop offset="100%" stop-color="#11151f" stop-opacity="1"/></radialGradient>';
      svgEl.appendChild(defs);
      if (!cells || !cells.length) return;

      var cx = 380, cy = 220;
      var hub = cells[0], spokes = cells.slice(1);
      var R = Math.min(330, Math.max(150, 110 + spokes.length * 8));
      R = Math.min(R, 200);

      // edges first (animated data-flow)
      spokes.forEach(function (c, i) {
        var a = (2 * Math.PI * i) / Math.max(1, spokes.length) - Math.PI / 2;
        var x = cx + R * Math.cos(a), y = cy + R * Math.sin(a);
        svgEl.appendChild(svg("line", { class: "edge flow", x1: cx, y1: cy, x2: x, y2: y }));
      });

      function nodeGroup(c, x, y, r, isHub) {
        var g = svg("g", { class: "node" + (isHub ? " node-hub" : "") + (reduceMotion ? "" : " breathe") });
        var href = "./cell.html?id=" + encodeURIComponent(c.id) + (API ? "&api=" + encodeURIComponent(API) : "");
        var a = svg("a", {}); a.setAttributeNS("http://www.w3.org/1999/xlink", "href", href); a.setAttribute("href", href);
        a.appendChild(svg("circle", { class: "node-ring", cx: x, cy: y, r: r + 6 }));
        a.appendChild(svg("circle", { class: "node-core", cx: x, cy: y, r: r }));
        // ⚑ NOT a checkmark. Nothing in this file checks a per-cell anything; a ✓ here was
        // the graphical half of the counter defect. A dot says "drawn" and claims nothing.
        var tick = svg("text", { class: "node-tick", x: x, y: y + 4, "text-anchor": "middle" }); tick.textContent = "·";
        a.appendChild(tick);
        var label = svg("text", { class: "node-label", x: x, y: y + r + 14, "text-anchor": "middle" });
        label.textContent = isHub ? "hub" : shortId(c.id);
        a.appendChild(label);
        var title = svg("title", {}); title.textContent = c.id + (isHub ? " (custodial hub)" : "");
        a.appendChild(title);
        g.appendChild(a);
        svgEl.appendChild(g);
        nodeById[c.id] = { group: g, lit: false };
      }

      spokes.forEach(function (c, i) {
        var a = (2 * Math.PI * i) / Math.max(1, spokes.length) - Math.PI / 2;
        var x = cx + R * Math.cos(a), y = cy + R * Math.sin(a);
        var r = 9 + Math.min(11, Math.log10(1 + Number(c.balance || 0)) * 3.4);
        nodeGroup(c, x, y, r, false);
      });
      if (hub) nodeGroup(hub, cx, cy, 22, true);
    }

    // ---- liveness (SSE) -----------------------------------------------------
    function connectStream() {
      try {
        var es = new EventSource(api("/observability/stream"));
        es.addEventListener("hello", function (ev) {
          setNetLive("live · " + safeField(ev.data, "apps", "?") + " apps · " + safeField(ev.data, "nullifiers", "0") + " nullifiers");
          loadCells();
        });
        es.addEventListener("ping", function (ev) {
          setNetLive("live · seq " + safeField(ev.data, "seq", "?") + " · " + safeField(ev.data, "nullifiers", "0") + " nullifiers");
        });
        es.onerror = function () { if (netLive) netLive.classList.remove("ok"); };
      } catch (e) { /* poll still drives it */ }
    }
    function safeField(json, k, dflt) { try { var o = JSON.parse(json); return o[k] != null ? o[k] : dflt; } catch (e) { return dflt; } }
    function setNetLive(text) { if (netLive) { netLive.classList.add("live"); } if (netLiveText) netLiveText.textContent = text; }

    // ---- wire up ------------------------------------------------------------
    var heroBtn = document.getElementById("hero-verify");
    if (heroBtn) heroBtn.addEventListener("click", function () { runEngine(); document.getElementById("network").scrollIntoView({ behavior: "smooth" }); });
    if (eng.runBtn) eng.runBtn.addEventListener("click", runEngine);

    loadCells();
    connectStream();
    setInterval(loadCells, 20000);
    // auto-run the proof engine shortly after load so the wow happens on its own
    setTimeout(function () { if (!enginePromise) runEngine(); }, 1400);
  }
})();
