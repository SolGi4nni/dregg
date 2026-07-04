/* ============================================================================
 * dregg.works — the trustless-host verify badge.
 *
 * Drop this one self-contained script onto any page served by
 * `<name>.dregg.works` and every visitor can prove, in their own browser, that
 * the bytes they received are exactly the bytes committed on-chain to the
 * publisher's cell. The host cannot tamper: it does not hold the commitment, and
 * it cannot forge a blake3 preimage.
 *
 * WHAT IT DOES (entirely client-side, no trust in the serving host):
 *   1. re-fetches THIS page's own bytes  -> blake3(bytes)  (the served body)
 *   2. fetches the cell's slot-0 commitment from the node API
 *        GET <node>/api/cell/<cell>  ->  json.fields[0]   (the committed hash)
 *   3. compares.  ✓ match = these exact bytes are the published, on-chain bytes.
 *                 ✗ mismatch = the host served something the publisher never
 *                   committed — refuse to trust it.
 *
 * THE SELF-CERTIFYING LOOP (why blake3(served) == commitment):
 *   The publisher includes THIS snippet in the page, then commits
 *   `blake3(the whole file, badge tag and all)` to slot 0 of their cell in one
 *   cap-gated receipted turn (the `WebOfCells::publish` / portal `publishMinisite`
 *   convention — see portal/src/drive-actions.mjs). The host serves that exact
 *   file. The badge re-hashes that exact file. The loop closes on itself.
 *
 * HOW IT HOOKS (the serving host / publisher supplies the cell; the node is
 * defaulted but overridable):
 *   Cheapest: data-attributes on the script tag —
 *     <script src="/verify-badge.js"
 *             data-cell="<64-hex cell id>"
 *             data-node="https://<a-node>"        (optional; the cell-lookup API base)
 *             data-name="mysite"></script>        (optional, for the label)
 *   Or meta tags:
 *     <meta name="dregg:cell" content="<64-hex cell id>">
 *     <meta name="dregg:node" content="https://<a-node>">
 *     <meta name="dregg:name" content="mysite">
 *   Or a global the host injects before this script:
 *     <script>window.__DREGG__ = { cell:"...", node:"https://...", name:"..." }</script>
 *
 *   When no node is supplied, the badge falls back to DEFAULT_NODE below — the
 *   public devnet node from the central endpoints config (sdk/src/endpoints.rs
 *   `defaults::DEVNET`; this literal is that config's JS projection — if the
 *   devnet domain moves, move both). Every hook above overrides it.
 *
 *   Because the serving host for *.dregg.works is untrusted infrastructure that
 *   lives OUTSIDE this repo, the badge takes nothing on faith from it: the cell
 *   id is content-addressed (unforgeable), and the commitment is fetched from a
 *   node the visitor can point anywhere (data-node) and cross-check — the default
 *   only picks WHICH node answers when the visitor/publisher expresses no
 *   preference. The host merely ships bytes; it is never asked to be believed.
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
  // The default cell-lookup node: the public devnet API host from the central
  // endpoints config (sdk/src/endpoints.rs `defaults::DEVNET`). Overridable via
  // data-node / meta dregg:node / window.__DREGG__.node — the default only
  // applies when none of those are set.
  var DEFAULT_NODE = "https://devnet.dregg.fg-goose.online";
  function readConfig() {
    var cfg = (window.__DREGG__ && typeof window.__DREGG__ === "object") ? window.__DREGG__ : {};
    var self = document.currentScript || (function () {
      var ss = document.getElementsByTagName("script");
      for (var i = ss.length - 1; i >= 0; i--) if (/verify-badge\.js/.test(ss[i].src)) return ss[i];
      return null;
    })();
    function meta(n) { var m = document.querySelector('meta[name="dregg:' + n + '"]'); return m && m.content; }
    function data(n) { return self && self.dataset ? self.dataset[n] : null; }
    return {
      cell: (data("cell") || meta("cell") || cfg.cell || "").trim().toLowerCase().replace(/^0x/, ""),
      node: (data("node") || meta("node") || cfg.node || DEFAULT_NODE).trim().replace(/\/+$/, ""),
      name: (data("name") || meta("name") || cfg.name || "").trim(),
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
      '.dw-panel .ok{color:#7aab6f}.dw-panel .bad{color:#d9663f}' +
      '.dw-panel a{color:#7aab6f;text-decoration:none}.dw-panel a:hover{color:#c49245}' +
      '.dw-panel .note{margin-top:10px;padding-top:10px;border-top:1px solid rgba(228,221,208,.1);font-size:11.5px;color:#7a7265;line-height:1.55}';
    var st = document.createElement("style");
    st.id = "dw-badge-style"; st.textContent = css;
    document.head.appendChild(st);
  }

  function el(tag, cls, html) { var e = document.createElement(tag); if (cls) e.className = cls; if (html != null) e.innerHTML = html; return e; }

  function run() {
    var cfg = readConfig();
    injectStyle();
    var badge = el("div", "dw-vbadge checking", '<span class="spin"></span> verifying on-chain…');
    var panel = el("div", "dw-panel");
    document.body.appendChild(badge);
    document.body.appendChild(panel);
    badge.addEventListener("click", function () { panel.classList.toggle("show"); });

    function set(state, label, panelHtml) {
      badge.className = "dw-vbadge " + state;
      badge.innerHTML = (state === "checking" ? '<span class="spin"></span> ' : '<span class="mk">' + (state === "ok" ? "✓" : "✕") + '</span> ') + label;
      panel.innerHTML = panelHtml;
    }

    if (!cfg.cell || cfg.cell.length !== 64) {
      set("bad", "verify unconfigured",
        '<h4>verify badge not configured</h4>' +
        '<div class="note">This page did not declare its on-chain cell. The publisher must add ' +
        '<span class="row">data-cell / meta dregg:cell</span> (the 64-hex cell id) so visitors can verify ' +
        'the served bytes. Optionally <span class="row">data-node / meta dregg:node</span> picks the node API ' +
        'base (default: the public devnet node).</div>');
      return;
    }

    var title = cfg.name ? (cfg.name + ".dregg.works") : "this page";
    var pageUrl = location.href.split("#")[0];

    Promise.all([
      fetch(pageUrl, { cache: "no-store" }).then(function (r) {
        if (!r.ok) throw new Error("re-fetch " + r.status);
        return r.arrayBuffer();
      }),
      cfg.node
        ? fetch(cfg.node + "/api/cell/" + cfg.cell, { cache: "no-store" }).then(function (r) {
            if (!r.ok) throw new Error("node " + r.status);
            return r.json();
          })
        : Promise.reject(new Error("no node configured (data-node / meta dregg:node)")),
    ]).then(function (res) {
      var served = blake3hex(new Uint8Array(res[0]));
      var detail = res[1] || {};
      if (!detail.found) throw new Error("cell not found on node");
      var committed = ((detail.fields && detail.fields[0]) || "").toLowerCase();
      var match = committed && served === committed;
      var rows =
        '<div class="row"><b>served bytes — blake3</b>' + served + '</div>' +
        '<div class="row"><b>committed on-chain (cell slot 0)</b>' + (committed || "(empty)") + '</div>' +
        '<div class="row"><b>cell</b><a href="' + (cfg.node || "") + '/api/cell/' + cfg.cell + '" target="_blank" rel="noopener">' + cfg.cell + '</a></div>';
      if (match) {
        set("ok", "verified on-chain",
          '<h4 class="ok">✓ these exact bytes are committed on-chain</h4>' + rows +
          '<div class="note">You did not trust the host. Your browser re-hashed the bytes it received and ' +
          'matched them against the commitment in cell slot&nbsp;0, fetched from the node. ' +
          '<a href="https://dregg.fg-goose.online/light-client/" target="_blank" rel="noopener">how this works →</a></div>');
      } else {
        set("bad", "bytes do not match",
          '<h4 class="bad">✕ served bytes do not match the on-chain commitment</h4>' + rows +
          '<div class="note">The host served bytes the publisher never committed. Do not trust this page — ' +
          'the commitment is on-chain and this is not it.</div>');
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
