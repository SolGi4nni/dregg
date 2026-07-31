/* ============================================================================
 * dregg.works — the served-bytes-vs-commitment badge.
 *
 * Drop this one self-contained script onto any page served by
 * `<name>.dregg.works` and a visitor's own browser re-hashes the bytes it
 * received and compares them against a slot-0 commitment read from a node API.
 * The blake3 is real and runs locally; the host cannot forge a preimage.
 *
 * ⚑ WHAT THE HOST STILL CHOOSES — READ THIS BEFORE BELIEVING A ✓.
 * ---------------------------------------------------------------------------
 * MEASURED 2026-07-30. The check has an ORACLE with two halves — WHICH CELL is
 * authoritative, and WHICH NODE answers for it — and through the version before
 * this one BOTH halves were read from the page under verification (`data-cell` /
 * `data-node` / `meta dregg:*` / `window.__DREGG__`). A hostile host serves
 * arbitrary bytes, then points `data-cell` at a cell IT published holding
 * `blake3(those bytes)`, or points `data-node` at a server it runs — and the
 * badge painted a green "✓ verified on-chain" over the sentence
 * "You did not trust the host." You did. The host picked what it was checked
 * against. (`docs/VISITOR-VERIFY-WELD.md` already named this: "page-supplied
 * cell ids are not merely strippable — they are swappable ... verify-badge.js is
 * defeated this way *even when present*.")
 *
 * So this script now grades its own verdict by WHERE THE ORACLE CAME FROM:
 *
 *   TRUST DECISION   both halves came from the VISITOR'S OWN URL —
 *                    `?dregg-cell=<64 hex>&dregg-node=<https://…>` — values the
 *                    serving host did not put there and cannot edit. Only this
 *                    path is ever labelled "verified", and it is the only path
 *                    that sets `window.__DREGG_VERIFY__.verdict = "verified"`.
 *   CONSISTENCY CHECK either half came from the page. The bytes really do hash
 *                    to the commitment that oracle published — a genuine fact
 *                    about the two, and NOT evidence that you avoided trusting
 *                    the host, because the host chose the oracle. Painted amber,
 *                    labelled, never green, and `verdict` is left ABSENT so a
 *                    consumer testing `=== "verified"` gets `undefined` rather
 *                    than a weaker string that skims as a pass.
 *   REFUSED          served bytes ≠ the commitment, or the page declares a cell
 *                    other than the one the visitor asked for.
 *
 * WHAT IT DOES (entirely client-side), in order:
 *   1. re-fetches THIS page's own bytes  -> blake3(bytes)  (the served body)
 *   2. fetches the cell's slot-0 commitment from the node API
 *        GET <node>/api/cell/<cell>  ->  json.fields[0]   (the committed hash)
 *   3. compares, and labels the verdict with the oracle's provenance.
 *
 * THE SELF-CERTIFYING LOOP (why blake3(served) == commitment):
 *   The publisher includes THIS snippet in the page, then commits
 *   `blake3(the whole file, badge tag and all)` to slot 0 of their cell in one
 *   cap-gated receipted turn (the `WebOfCells::publish` / portal `publishMinisite`
 *   convention — see portal/src/drive-actions.mjs). The host serves that exact
 *   file. The badge re-hashes that exact file. The loop closes on itself.
 *
 * HOW IT HOOKS
 *   The VISITOR'S half (the only half that makes a ✓ a trust decision) is the
 *   URL query string, which the serving host does not author:
 *     https://mysite.dregg.works/?dregg-cell=<64-hex>&dregg-node=https://<a-node>
 *   The PAGE'S half is the publisher's convenience default, and is what makes a
 *   verdict a consistency check:
 *     <script src="/verify-badge.js"
 *             data-cell="<64-hex cell id>"
 *             data-node="https://<a-node>"        (optional; the cell-lookup API base)
 *             data-name="mysite"></script>        (optional, for the label)
 *   Or meta tags (`<meta name="dregg:cell|node|name" content="…">`), or a global
 *   the host injects before this script (`window.__DREGG__ = {cell,node,name}`).
 *
 *   There is deliberately NO built-in node endpoint: no public devnet is
 *   currently anchored, so when no node is supplied the badge still re-hashes
 *   the served bytes locally but states plainly that verification against a
 *   live chain is unavailable — it never invents an endpoint and never
 *   upgrades an uncheckable page to a pass.
 *
 *   The cell id being content-addressed makes it UNFORGEABLE, not TRUSTWORTHY:
 *   it binds bytes to a cell, never a cell to a hostname. Binding `mysite` to
 *   ONE cell needs an out-of-band name→cell registry the visitor holds (the
 *   extension leg of `docs/VISITOR-VERIFY-WELD.md`, plan item 3), which does not
 *   exist yet. Until it does, `?dregg-cell=` IS the out-of-band channel: a link
 *   you got from somewhere other than the host you are checking.
 *
 * No build step, no dependencies, no external resources. The blake3 below is a
 * standalone implementation verified byte-for-byte against @noble/hashes across
 * all input lengths (multi-chunk included) and the empty-string test vector.
 * ============================================================================ */
(function () {
  "use strict";

  /* ---------- standalone BLAKE3 (one-shot, 32-byte output) ---------- */
  var IV = new Uint32Array([
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
  ]);
  var MSG = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
  var CHUNK_START = 1, CHUNK_END = 2, PARENT = 4, ROOT = 8;
  function rotr(x, n) { return ((x >>> n) | (x << (32 - n))) >>> 0; }

  function compress(cv, block, ctrLo, ctrHi, blockLen, flags) {
    var s = new Uint32Array(16);
    for (var i = 0; i < 8; i++) s[i] = cv[i];
    s[8] = IV[0]; s[9] = IV[1]; s[10] = IV[2]; s[11] = IV[3];
    s[12] = ctrLo >>> 0; s[13] = ctrHi >>> 0; s[14] = blockLen >>> 0; s[15] = flags >>> 0;
    var m = block;
    function g(a, b, c, d, mx, my) {
      s[a] = (s[a] + s[b] + mx) >>> 0; s[d] = rotr(s[d] ^ s[a], 16);
      s[c] = (s[c] + s[d]) >>> 0;       s[b] = rotr(s[b] ^ s[c], 12);
      s[a] = (s[a] + s[b] + my) >>> 0; s[d] = rotr(s[d] ^ s[a], 8);
      s[c] = (s[c] + s[d]) >>> 0;       s[b] = rotr(s[b] ^ s[c], 7);
    }
    for (var r = 0; r < 7; r++) {
      g(0, 4, 8, 12, m[0], m[1]);  g(1, 5, 9, 13, m[2], m[3]);
      g(2, 6, 10, 14, m[4], m[5]); g(3, 7, 11, 15, m[6], m[7]);
      g(0, 5, 10, 15, m[8], m[9]); g(1, 6, 11, 12, m[10], m[11]);
      g(2, 7, 8, 13, m[12], m[13]); g(3, 4, 9, 14, m[14], m[15]);
      if (r < 6) { var p = new Uint32Array(16); for (var k = 0; k < 16; k++) p[k] = m[MSG[k]]; m = p; }
    }
    for (var j = 0; j < 8; j++) { s[j] = (s[j] ^ s[j + 8]) >>> 0; s[j + 8] = (s[j + 8] ^ cv[j]) >>> 0; }
    return s;
  }
  function wordsOf(bytes, off, len) {
    var w = new Uint32Array(16);
    for (var i = 0; i < len; i++) w[i >> 2] |= bytes[off + i] << ((i & 3) * 8);
    return w;
  }
  function outputBytes(state) {
    var o = new Uint8Array(32);
    for (var i = 0; i < 8; i++) {
      o[i * 4] = state[i] & 255; o[i * 4 + 1] = (state[i] >>> 8) & 255;
      o[i * 4 + 2] = (state[i] >>> 16) & 255; o[i * 4 + 3] = (state[i] >>> 24) & 255;
    }
    return o;
  }
  function hashChunk(input, off, len, ctr, root) {
    var cv = IV.slice(0, 8);
    var nBlocks = Math.max(1, Math.ceil(len / 64));
    for (var b = 0; b < nBlocks; b++) {
      var bOff = off + b * 64, bLen = Math.min(64, len - b * 64), flags = 0;
      if (b === 0) flags |= CHUNK_START;
      if (b === nBlocks - 1) { flags |= CHUNK_END; if (root) flags |= ROOT; }
      var out = compress(cv, wordsOf(input, bOff, Math.max(0, bLen)),
        ctr & 0xffffffff, Math.floor(ctr / 0x100000000), bLen, flags);
      if (b === nBlocks - 1 && root) return outputBytes(out);
      cv = out.slice(0, 8);
    }
    return cv;
  }
  function parentOut(left, right, root) {
    var block = new Uint32Array(16);
    for (var i = 0; i < 8; i++) { block[i] = left[i]; block[i + 8] = right[i]; }
    var out = compress(IV.slice(0, 8), block, 0, 0, 64, PARENT | (root ? ROOT : 0));
    return root ? outputBytes(out) : out.slice(0, 8);
  }
  function pow2Below(n) { var p = 1; while (p * 2 < n) p *= 2; return p; }
  function hashTree(input, off, len, ctr, root) {
    if (len <= 1024) return hashChunk(input, off, len, ctr, root);
    var nChunks = Math.ceil(len / 1024);
    var leftChunks = pow2Below(nChunks), leftLen = leftChunks * 1024;
    var left = hashTree(input, off, leftLen, ctr, false);
    var right = hashTree(input, off + leftLen, len - leftLen, ctr + leftChunks, false);
    return parentOut(left, right, root);
  }
  function blake3hex(bytes) {
    var out = hashTree(bytes, 0, bytes.length, 0, true), s = "";
    for (var i = 0; i < 32; i++) s += (out[i] < 16 ? "0" : "") + out[i].toString(16);
    return s;
  }

  /* ---------- config: where the cell id + node API come from ---------- */
  // ⚑ TWO SOURCES, GRADED, NEVER MERGED SILENTLY.
  //   * the VISITOR'S URL (`?dregg-cell=` / `?dregg-node=`) — the serving host
  //     does not author the query string of the link you followed, so an oracle
  //     from here is one the party under test does not control;
  //   * the PAGE (data-* / meta dregg:* / window.__DREGG__) — authored by the
  //     very host whose bytes are being checked.
  // No endpoint is hardcoded — no public devnet is currently anchored — so an
  // unconfigured badge reports that honestly instead of querying a dead host.
  function normCell(s) { return String(s || "").trim().toLowerCase().replace(/^0x/, ""); }
  function normNode(s) { return String(s || "").trim().replace(/\/+$/, ""); }

  function readConfig() {
    var cfg = (window.__DREGG__ && typeof window.__DREGG__ === "object") ? window.__DREGG__ : {};
    var self = document.currentScript || (function () {
      var ss = document.getElementsByTagName("script");
      for (var i = ss.length - 1; i >= 0; i--) if (/verify-badge\.js/.test(ss[i].src)) return ss[i];
      return null;
    })();
    function meta(n) { var m = document.querySelector('meta[name="dregg:' + n + '"]'); return m && m.content; }
    function data(n) { return self && self.dataset ? self.dataset[n] : null; }

    var q;
    try { q = new URLSearchParams(location.search); } catch (e) { q = null; }
    var urlCell = normCell(q && q.get("dregg-cell"));
    var urlNode = normNode(q && q.get("dregg-node"));
    if (!/^[0-9a-f]{64}$/.test(urlCell)) urlCell = "";   // a malformed override is IGNORED, never coerced

    var pageCell = normCell(data("cell") || meta("cell") || cfg.cell);
    var pageNode = normNode(data("node") || meta("node") || cfg.node);

    return {
      cell: urlCell || pageCell,
      node: urlNode || pageNode,
      name: String(data("name") || meta("name") || cfg.name || "").trim(),
      // Kept SEPARATELY so a verdict can say which half came from where, and so
      // the two can be COMPARED: a page declaring a cell other than the one the
      // visitor asked for is a refusal, not a silent override.
      urlCell: urlCell,
      urlNode: urlNode,
      pageCell: pageCell,
      pageNode: pageNode,
    };
  }

  /* ---------- the oracle's provenance — printed on EVERY verdict ---------- */
  // `own` is true only when BOTH halves of the oracle came from the visitor's
  // own URL. That is the sole condition under which a match is a statement about
  // the HOST rather than a statement about the host's own bookkeeping.
  function provenanceOf(cfg) {
    var cellFromYou = !!cfg.urlCell, nodeFromYou = !!cfg.urlNode;
    if (cellFromYou && nodeFromYou) {
      return {
        own: true,
        short: "oracle: YOUR URL (both halves)",
        label: "oracle provenance: BOTH halves came from your own <code>?dregg-cell=</code> and " +
          "<code>?dregg-node=</code> — values this host did not put here and cannot edit. " +
          "This is a trust decision.",
      };
    }
    var chose = !cellFromYou && !nodeFromYou
      ? "the cell id AND the node"
      : (!cellFromYou ? "the cell id" : "the node");
    return {
      own: false,
      short: "oracle: this page chose " + (!cellFromYou && !nodeFromYou ? "both halves" : chose),
      label: "oracle provenance: THIS PAGE supplied " + chose + ". The bytes really do hash to the " +
        "commitment that oracle published — but the party under test picked the oracle, so this is a " +
        "<strong>consistency check, not a trust decision</strong>. A host serving arbitrary bytes can " +
        "publish a cell holding their hash, or name a node it runs, and reach this same state. " +
        "Append <code>?dregg-cell=&lt;64 hex&gt;&amp;dregg-node=&lt;https://a-node&gt;</code> — from a link " +
        "you did not get from this host — to make it one.",
    };
  }

  /* ---------- the badge UI (self-contained styles) ---------- */
  function injectStyle() {
    if (document.getElementById("dw-badge-style")) return;
    var css =
      '.dw-vbadge{position:fixed;right:14px;bottom:14px;z-index:2147483000;' +
      'font:600 12.5px/1.4 "SF Mono","Cascadia Code","JetBrains Mono",ui-monospace,Menlo,monospace;' +
      'display:flex;align-items:center;gap:8px;padding:9px 13px;border-radius:999px;cursor:pointer;' +
      'border:1px solid rgba(228,221,208,.18);background:rgba(8,12,10,.92);color:#a89e8e;' +
      'box-shadow:0 6px 24px rgba(0,0,0,.45);backdrop-filter:blur(8px);-webkit-backdrop-filter:blur(8px);' +
      'transition:border-color .18s,color .18s;user-select:none;max-width:min(92vw,440px)}' +
      '.dw-vbadge:hover{border-color:#5b8a5a}' +
      '.dw-vbadge .mk{font-weight:800}' +
      '.dw-vbadge.checking{color:#c49245}' +
      '.dw-vbadge.ok{color:#7aab6f;border-color:rgba(122,171,111,.55)}' +
      // A consistency check gets its OWN colour. It is not a pass and it is not a
      // failure, and painting it with either one is the whole defect.
      '.dw-vbadge.consistent{color:#c49245;border-color:rgba(196,146,69,.6)}' +
      '.dw-vbadge.bad{color:#d9663f;border-color:rgba(217,102,63,.65)}' +
      '.dw-vbadge .spin{width:8px;height:8px;border-radius:50%;background:#c49245;animation:dwspin 1s ease-in-out infinite}' +
      '@keyframes dwspin{0%,100%{opacity:.3}50%{opacity:1}}' +
      '.dw-panel{position:fixed;right:14px;bottom:60px;z-index:2147483000;display:none;' +
      'width:min(92vw,420px);padding:16px 18px;border-radius:12px;' +
      'border:1px solid rgba(228,221,208,.16);background:rgba(8,12,10,.97);color:#a89e8e;' +
      'box-shadow:0 12px 40px rgba(0,0,0,.5);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);' +
      'font:13px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",system-ui,sans-serif}' +
      '.dw-panel.show{display:block}' +
      '.dw-panel h4{margin:0 0 8px;font:700 14px/1.3 "Iowan Old Style",Palatino,Georgia,serif;color:#f5f0e8}' +
      '.dw-panel .row{font-family:"SF Mono",ui-monospace,Menlo,monospace;font-size:11px;word-break:break-all;margin:6px 0;color:#a89e8e}' +
      '.dw-panel .row b{color:#7a7265;font-weight:600;display:block;text-transform:uppercase;letter-spacing:.05em;font-size:9.5px;margin-bottom:1px}' +
      '.dw-panel .ok{color:#7aab6f}.dw-panel .bad{color:#d9663f}.dw-panel .warn{color:#c49245}' +
      '.dw-panel .prov{margin-top:9px;padding:8px 10px;border-radius:7px;font-size:11.5px;line-height:1.5;' +
      'border:1px solid rgba(228,221,208,.12);background:rgba(228,221,208,.035);color:#9a9184}' +
      '.dw-panel .prov code{font-family:"SF Mono",ui-monospace,Menlo,monospace;font-size:10.5px;color:#c49245}' +
      '.dw-panel a{color:#7aab6f;text-decoration:none}.dw-panel a:hover{color:#c49245}' +
      '.dw-panel .note{margin-top:10px;padding-top:10px;border-top:1px solid rgba(228,221,208,.1);font-size:11.5px;color:#7a7265;line-height:1.55}';
    var st = document.createElement("style");
    st.id = "dw-badge-style"; st.textContent = css;
    document.head.appendChild(st);
  }

  function el(tag, cls, html) { var e = document.createElement(tag); if (cls) e.className = cls; if (html != null) e.innerHTML = html; return e; }

  function run() {
    var cfg = readConfig();
    var prov = provenanceOf(cfg);
    injectStyle();
    var badge = el("div", "dw-vbadge checking", '<span class="spin"></span> checking served bytes…');
    var panel = el("div", "dw-panel");
    document.body.appendChild(badge);
    document.body.appendChild(panel);
    badge.addEventListener("click", function () { panel.classList.toggle("show"); });

    // ⚑ THE MACHINE-READABLE VERDICT. `verdict` is written in EXACTLY ONE place
    // (`set("ok", …)`, reachable only from the visitor-supplied-oracle branch) and
    // is ABSENT otherwise, so a consumer testing `=== "verified"` gets `undefined`
    // for a consistency check rather than a weaker string that reads as partial
    // success. `oracle_from_visitor` is the branchable bit underneath it.
    window.__DREGG_VERIFY__ = {
      state: "checking",
      oracle_from_visitor: prov.own,
      cell: cfg.cell || null,
      node: cfg.node || null,
      cell_source: cfg.urlCell ? "visitor-url" : (cfg.pageCell ? "page" : null),
      node_source: cfg.urlNode ? "visitor-url" : (cfg.pageNode ? "page" : null),
    };

    function set(state, label, panelHtml) {
      badge.className = "dw-vbadge " + state;
      var mark = state === "ok" ? "✓" : (state === "consistent" ? "≡" : "✕");
      badge.innerHTML = (state === "checking" ? '<span class="spin"></span> ' : '<span class="mk">' + mark + '</span> ') + label;
      panel.innerHTML = panelHtml;
      window.__DREGG_VERIFY__.state = state;
      // THE ONE PLACE THE SUCCESS WORD IS WRITTEN.
      if (state === "ok") window.__DREGG_VERIFY__.verdict = "verified";
      else delete window.__DREGG_VERIFY__.verdict;
    }

    // The visitor named a cell and the page claims a different one. That is not an
    // override to resolve silently — it is the page disagreeing with the link you
    // followed about which cell speaks for it, and it is refused on the spot.
    if (cfg.urlCell && cfg.pageCell && cfg.urlCell !== cfg.pageCell) {
      set("bad", "cell mismatch — refused",
        '<h4 class="bad">✕ this page declares a different cell than you asked for</h4>' +
        '<div class="row"><b>the cell you named (?dregg-cell)</b>' + cfg.urlCell + '</div>' +
        '<div class="row"><b>the cell this page declares</b>' + cfg.pageCell + '</div>' +
        '<div class="note">Nothing was checked. A page that answers to a cell other than the one your ' +
        'link names is not the page your link named — no hash comparison can repair that, so none was run.</div>');
      return;
    }

    if (!cfg.cell || cfg.cell.length !== 64) {
      set("bad", "unchecked — no cell",
        '<h4>no cell to check against</h4>' +
        '<div class="note">Neither your URL nor this page named an on-chain cell, so nothing was compared. ' +
        'A visitor supplies one with <span class="row">?dregg-cell=&lt;64 hex&gt;</span>; a publisher supplies ' +
        'the convenience default with <span class="row">data-cell / meta dregg:cell</span>. Naming the node ' +
        'API base is the other half (<span class="row">?dregg-node= / data-node / meta dregg:node</span>) — ' +
        'there is no default node, and no public devnet is currently anchored.</div>');
      return;
    }

    var title = cfg.name ? (cfg.name + ".dregg.works") : "this page";
    var pageUrl = location.href.split("#")[0];

    var pageFetch = fetch(pageUrl, { cache: "no-store" }).then(function (r) {
      if (!r.ok) throw new Error("re-fetch " + r.status);
      return r.arrayBuffer();
    });

    if (!cfg.node) {
      // No node named and no public devnet is currently anchored. The local half
      // (re-hashing the served bytes) still runs; the chain half is honestly
      // reported unavailable — never routed at an invented endpoint.
      pageFetch.then(function (buf) {
        var served = blake3hex(new Uint8Array(buf));
        set("bad", "unverified — no node",
          '<h4>no node configured — on-chain check unavailable</h4>' +
          '<div class="row"><b>served bytes — blake3 (computed locally)</b>' + served + '</div>' +
          '<div class="row"><b>cell named (' + (cfg.urlCell ? "your URL" : "this page") + ')</b>' + cfg.cell + '</div>' +
          '<div class="note">No public devnet is currently anchored and neither your URL nor this page names a ' +
          'node API (<span class="row">?dregg-node= / data-node / meta dregg:node / window.__DREGG__.node</span>), ' +
          'so the served bytes were compared against nothing. A missing check is never a pass — ' +
          'treat this page as unverified.</div>');
      }).catch(function (err) {
        set("bad", "verify failed",
          '<h4 class="bad">could not complete the check</h4>' +
          '<div class="row"><b>error</b>' + String(err && err.message || err) + '</div>' +
          '<div class="note">The badge could not re-read this page. A failed check is never a pass.</div>');
      });
      return;
    }

    Promise.all([
      pageFetch,
      fetch(cfg.node + "/api/cell/" + cfg.cell, { cache: "no-store" }).then(function (r) {
        if (!r.ok) throw new Error("node " + r.status);
        return r.json();
      }),
    ]).then(function (res) {
      var served = blake3hex(new Uint8Array(res[0]));
      var detail = res[1] || {};
      if (!detail.found) throw new Error("cell not found on node");
      var committed = ((detail.fields && detail.fields[0]) || "").toLowerCase();
      var match = committed && served === committed;
      var rows =
        '<div class="row"><b>served bytes — blake3</b>' + served + '</div>' +
        '<div class="row"><b>committed (cell slot 0, per the node below)</b>' + (committed || "(empty)") + '</div>' +
        '<div class="row"><b>cell — from ' + (cfg.urlCell ? "YOUR ?dregg-cell=" : "THIS PAGE") + '</b>' +
        '<a href="' + (cfg.node || "") + '/api/cell/' + cfg.cell + '" target="_blank" rel="noopener">' + cfg.cell + '</a></div>' +
        '<div class="row"><b>node — from ' + (cfg.urlNode ? "YOUR ?dregg-node=" : "THIS PAGE") + '</b>' + cfg.node + '</div>';
      // ⚑ THE PROVENANCE RIDES ON EVERY VERDICT, including the refusals: a reader
      // must never have to go looking for which oracle produced the answer.
      var provBox = '<div class="prov">' + prov.label + '</div>';
      if (match && prov.own) {
        // The ONLY green. Both halves of the oracle came from the visitor.
        set("ok", "verified — your oracle",
          '<h4 class="ok">✓ these exact bytes are the ones committed at the cell YOU named</h4>' + rows +
          provBox +
          '<div class="note">Your browser re-hashed the bytes it received and matched them against slot&nbsp;0 ' +
          'of a cell you named, read from a node you named. This host was not asked to be believed about ' +
          'anything. <a href="/light-client/" target="_blank" rel="noopener">how this works →</a></div>');
      } else if (match) {
        set("consistent", "consistent — host-supplied oracle",
          '<h4 class="warn">≡ the served bytes match the commitment THIS PAGE pointed at</h4>' + rows +
          provBox +
          '<div class="note">This is a real comparison and it held — but it is not the trustless claim. ' +
          'The host chose which cell and/or which node is authoritative, so a host serving forged bytes ' +
          'reaches this same state by pointing the check at an oracle that commits them. ' +
          '<a href="/light-client/" target="_blank" rel="noopener">how this works →</a></div>');
      } else {
        set("bad", "bytes do not match",
          '<h4 class="bad">✕ served bytes do not match the commitment</h4>' + rows +
          provBox +
          '<div class="note">The bytes you received are not the bytes committed at this cell. Do not trust ' +
          'this page.</div>');
      }
    }).catch(function (err) {
      set("bad", "verify failed",
        '<h4 class="bad">could not complete the check</h4>' +
        '<div class="row"><b>title</b>' + title + '</div>' +
        '<div class="row"><b>error</b>' + String(err && err.message || err) + '</div>' +
        '<div class="note">The badge could not reach the node API or re-read this page. ' +
        'A failed check is never a pass — treat it as unverified.</div>');
    });
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run);
  else run();
})();
