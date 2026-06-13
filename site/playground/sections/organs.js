/**
 * Organs — the v0.3.0 SDK nouns (docs/ORGANS.md) as a live try-it surface.
 *
 * The four organs (trustline · channels · mailbox · attested-query) are the
 * ergonomic faces of node-side services, NOT pure in-browser primitives: a
 * trustline's per-line factory descriptor and a channel's seal fan-out are
 * computed by the Rust SDK / node, and the enforcement tooth is the
 * executor-installed cell program. So this section drives them through the
 * REAL `@dregg/sdk` clients against a configured devnet node — the same
 * client a production integrator imports:
 *
 *   import { NodeClient } from "@dregg/sdk";
 *   const node = new NodeClient(url, { devnetKey });
 *   const line = await node.trustline().open(holderHex, 1000);
 *
 * HONEST DEGRADATION: with no node configured (or unreachable), nothing is
 * faked. The panels show the organ's story, the exact SDK call shape, and the
 * node verdict slot stays empty with a clear "point me at a devnet node"
 * prompt. The node URL + devnet key are shared with the Turn Workbench
 * (localStorage `dregg_node_url` / `dregg_node_token`).
 *
 * The two organs THIS section drives end-to-end against a node:
 *   - TRUSTLINE  open → draw → repay → status  (the quantitative capability)
 *   - CHANNELS   create → join → remove → status  (the epoch-unification
 *                keystone: remove(m) darkens ciphertext AND capabilities in
 *                ONE turn — `epochs_unified` surfaced).
 * MAILBOX (relay, separate port) + ATTESTED-QUERY (light-client read) are
 * surfaced as their SDK shape + ORGANS.md story; driving them needs the relay
 * service URL / a federation node, noted per panel rather than stubbed.
 */

const NODE_URL_KEY = 'dregg_node_url';
const NODE_TOKEN_KEY = 'dregg_node_token';
// The browser-safe, fetch-only SDK entry (BrowserNodeClient + organ clients).
// The full /index.mjs entry statically imports node:crypto / fs and cannot
// parse in a browser; /browser.mjs is the part that is pure fetch.
const SDK_URL = '/pkg/@dregg/sdk/browser.mjs';

function esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function defaultNodeUrl() {
  try {
    const { protocol, hostname, origin } = window.location;
    const isLocal = hostname === 'localhost' || hostname === '127.0.0.1' || hostname === '[::1]';
    if ((protocol === 'http:' || protocol === 'https:') && !isLocal) return origin;
  } catch {}
  return 'http://localhost:8420';
}

function nodeUrl() {
  return (localStorage.getItem(NODE_URL_KEY) || defaultNodeUrl()).replace(/\/+$/, '');
}
function nodeToken() {
  return localStorage.getItem(NODE_TOKEN_KEY) || '';
}

// ---------------------------------------------------------------------------
// Section state
// ---------------------------------------------------------------------------
let sdk = null;            // the @dregg/sdk module (lazy import)
let sdkError = null;       // import error, if the bundle isn't served
let node = null;           // NodeClient bound to the configured url/token
let nodeOnline = null;     // null=unknown, true/false after probe
let nodeOperator = null;   // operator pubkey hex (becomes a useful holder id)

let tl = { line: null, status: null, log: [] };       // trustline organ state
let ch = { group: null, status: null, members: [], log: [] }; // channels organ state

function organLog(o, kind, text) {
  o.log.unshift({ kind, text, at: new Date().toLocaleTimeString() });
  o.log = o.log.slice(0, 12);
}

// ---------------------------------------------------------------------------
// SDK + node wiring
// ---------------------------------------------------------------------------

async function ensureSdk() {
  if (sdk || sdkError) return sdk;
  try {
    sdk = await import(SDK_URL);
  } catch (e) {
    sdkError = String(e?.message || e);
  }
  return sdk;
}

function makeNode() {
  if (!sdk) return null;
  const token = nodeToken();
  node = new sdk.BrowserNodeClient(nodeUrl(), token ? { devnetKey: token } : {});
  return node;
}

async function probeNode(section) {
  await ensureSdk();
  if (!sdk) { render(section); return; }
  makeNode();
  nodeOnline = null;
  render(section);
  try {
    // operatorPublicKeyHex() falls back /api/node/identity → /status — a good liveness probe.
    nodeOperator = await node.operatorPublicKeyHex();
    nodeOnline = true;
  } catch (e) {
    nodeOnline = false;
    nodeOperator = null;
  }
  render(section);
}

function saveSettings(section) {
  const url = section.querySelector('#org-url')?.value?.trim();
  const tok = section.querySelector('#org-token')?.value?.trim();
  if (url != null) localStorage.setItem(NODE_URL_KEY, url);
  if (tok != null) localStorage.setItem(NODE_TOKEN_KEY, tok);
  probeNode(section);
}

// ---------------------------------------------------------------------------
// Trustline organ actions (real node calls via the SDK)
// ---------------------------------------------------------------------------

function randHex(bytes) {
  const a = new Uint8Array(bytes);
  (self.crypto || window.crypto).getRandomValues(a);
  return Array.from(a, (b) => b.toString(16).padStart(2, '0')).join('');
}

async function tlOpen(section) {
  if (!node) return;
  const holderInput = section.querySelector('#tl-holder')?.value?.trim();
  const holder = holderInput || randHex(32); // a fresh counterparty cell id
  const line = Number(section.querySelector('#tl-line')?.value || 1000);
  organLog(tl, 'run', `trustline().open(holder=${holder.slice(0, 10)}…, line=${line})`);
  render(section);
  try {
    const res = await node.trustline().open(holder, line, randHex(4));
    tl.line = res;
    tl.status = null;
    organLog(tl, 'ok', `opened ${res.trustline.slice(0, 12)}… · line=${res.line} · ${res.turn_hashes?.length || 0} lifecycle turns`);
  } catch (e) {
    organLog(tl, 'err', `open failed: ${e?.message || e}`);
  }
  render(section);
}

async function tlAction(section, kind) {
  if (!node || !tl.line) return;
  const cell = tl.line.trustline;
  const amount = Number(section.querySelector('#tl-amount')?.value || 100);
  organLog(tl, 'run', `trustline().${kind}(${cell.slice(0, 10)}…${kind === 'status' ? '' : `, ${amount}`})`);
  render(section);
  try {
    const c = node.trustline();
    let res;
    if (kind === 'draw') { res = await c.draw(cell, amount); organLog(tl, 'ok', `drew ${amount} · drawn=${res.drawn} · remaining=${res.remaining}`); }
    else if (kind === 'repay') { res = await c.repay(cell, amount); organLog(tl, 'ok', `repaid ${amount} · drawn=${res.drawn} · remaining=${res.remaining}`); }
    else if (kind === 'status') { res = await c.status(cell); tl.status = res; organLog(tl, 'ok', `status · drawn=${res.drawn}/${res.line} · open=${res.open}`); }
    else if (kind === 'close') { res = await c.close(cell); organLog(tl, 'ok', `closed · settled→holder=${res.settled_to_holder} · residual→issuer=${res.residual_to_issuer}`); tl.line = null; tl.status = null; }
  } catch (e) {
    organLog(tl, 'err', `${kind} failed: ${e?.message || e}`);
  }
  render(section);
}

// ---------------------------------------------------------------------------
// Channels organ actions (real node calls via the SDK)
// ---------------------------------------------------------------------------

function newMember(label) {
  // A founding/joining member needs a cell id + an X25519 seal public key. The
  // playground mints synthetic identities (random 32-byte cell + seal pk) so a
  // stranger can see the membership/epoch machinery move; the node seals the
  // real fan-out to these keys.
  return { label, cell: randHex(32), sealPk: randHex(32) };
}

async function chCreate(section) {
  if (!node) return;
  const alice = newMember('alice');
  const tag = Math.floor(Math.random() * 1e6);
  ch.members = [alice];
  organLog(ch, 'run', `channels().create(tag=${tag}, [alice])`);
  render(section);
  try {
    const res = await node.channels().create(tag, [{ cell: alice.cell, sealPk: alice.sealPk }]);
    ch.group = res;
    ch.status = null;
    organLog(ch, 'ok', `group ${res.channel.slice(0, 12)}… · epoch=${res.epoch} · members=${res.members} · fan_out=${res.fan_out?.length || 0} sealed keys`);
  } catch (e) {
    organLog(ch, 'err', `create failed: ${e?.message || e}`);
  }
  render(section);
}

async function chJoin(section) {
  if (!node || !ch.group) return;
  const m = newMember(`m${ch.members.length}`);
  organLog(ch, 'run', `channels().join(${ch.group.channel.slice(0, 10)}…, ${m.label})`);
  render(section);
  try {
    const res = await node.channels().join(ch.group.channel, { cell: m.cell, sealPk: m.sealPk });
    ch.members.push(m);
    ch.group = res;
    organLog(ch, 'ok', `${m.label} joined · epoch bumped → ${res.epoch} · delegation_epoch=${res.delegation_epoch} · members=${res.members}`);
  } catch (e) {
    organLog(ch, 'err', `join failed: ${e?.message || e}`);
  }
  render(section);
}

async function chRemove(section) {
  if (!node || !ch.group || ch.members.length < 2) return;
  const m = ch.members[ch.members.length - 1];
  organLog(ch, 'run', `channels().remove(${ch.group.channel.slice(0, 10)}…, ${m.label}) — THE keystone: one turn darkens ciphertext AND caps`);
  render(section);
  try {
    const res = await node.channels().remove(ch.group.channel, m.cell);
    ch.members = ch.members.filter((x) => x !== m);
    ch.group = res;
    const inFanout = (res.fan_out || []).some((k) => k.member === m.cell);
    organLog(ch, 'ok', `${m.label} removed · epoch=${res.epoch} == delegation_epoch=${res.delegation_epoch} (unified) · ${m.label} ${inFanout ? 'STILL in fan_out (bug!)' : 'absent from fan_out → never gets the e+1 key'}`);
  } catch (e) {
    organLog(ch, 'err', `remove failed: ${e?.message || e}`);
  }
  render(section);
}

async function chStatus(section) {
  if (!node || !ch.group) return;
  organLog(ch, 'run', `channels().status(${ch.group.channel.slice(0, 10)}…)`);
  render(section);
  try {
    const res = await node.channels().status(ch.group.channel);
    ch.status = res;
    organLog(ch, res.epochs_unified ? 'ok' : 'err', `status · epoch=${res.epoch} delegation_epoch=${res.delegation_epoch} · epochs_unified=${res.epochs_unified}${res.epochs_unified ? '' : ' ← INVARIANT BROKEN'}`);
  } catch (e) {
    organLog(ch, 'err', `status failed: ${e?.message || e}`);
  }
  render(section);
}

// ---------------------------------------------------------------------------
// Render
// ---------------------------------------------------------------------------

function nodeBadge() {
  if (!sdk) return `<span class="org-badge org-badge--off">SDK bundle not served</span>`;
  if (nodeOnline === true) return `<span class="org-badge org-badge--on">node online${nodeOperator ? ` · operator ${esc(nodeOperator.slice(0, 8))}…` : ''}</span>`;
  if (nodeOnline === false) return `<span class="org-badge org-badge--off">node unreachable</span>`;
  return `<span class="org-badge org-badge--unknown">not connected</span>`;
}

function logBlock(o) {
  if (!o.log.length) return '<div class="org-dim">no calls yet</div>';
  return o.log.map((l) =>
    `<div class="org-log__row org-log__row--${l.kind}"><span class="org-dim">${esc(l.at)}</span> ${esc(l.text)}</div>`).join('');
}

function render(section) {
  const ready = nodeOnline === true;
  const disabled = ready ? '' : ' disabled';

  // ---- trustline panel ----
  const tlStatus = tl.status ? `
    <div class="org-status">
      <div><strong>line</strong> ${esc(tl.status.line)} · <strong>drawn</strong> ${esc(tl.status.drawn)} · <strong>remaining</strong> ${esc(tl.status.remaining)} · <strong>open</strong> ${tl.status.open ? 'yes' : 'no'}</div>
      <div class="org-dim">collateral=${esc(tl.status.collateral)} · escrow=${esc(tl.status.escrow)} · coordinator_remaining=${esc(String(tl.status.coordinator_remaining))}</div>
    </div>` : '';

  const trustlinePanel = `
    <div class="org-card">
      <div class="org-card__head">
        <h3>Trustline <span class="org-tag">§1 · quantitative capability</span></h3>
        <a class="org-link" href="/learn/" title="ORGANS.md §1">what is a trustline? →</a>
      </div>
      <p class="org-lede">"Issuer extends holder a line of N" is an attenuated capability whose every
        draw debits a shared counter — <em>granted ⊆ held</em> made quantitative. The node births the
        per-line cell from a content-addressed factory; the executor re-evaluates <code>drawn ≤ line</code>
        on every touch. This is the real <code>node.trustline()</code> SDK client.</p>
      <div class="org-controls">
        <label class="org-f"><span>holder cell (blank = mint one)</span><input id="tl-holder" placeholder="64-hex or blank"></label>
        <label class="org-f"><span>line</span><input id="tl-line" value="1000" placeholder="N"></label>
        <button class="pg-btn pg-btn--primary pg-btn--sm" data-org="tl-open"${disabled}>open</button>
      </div>
      <div class="org-controls">
        <label class="org-f"><span>amount</span><input id="tl-amount" value="100"></label>
        <button class="pg-btn pg-btn--accent pg-btn--sm" data-org="tl-draw"${tl.line && ready ? '' : ' disabled'}>draw</button>
        <button class="pg-btn pg-btn--ghost pg-btn--sm" data-org="tl-repay"${tl.line && ready ? '' : ' disabled'}>repay</button>
        <button class="pg-btn pg-btn--ghost pg-btn--sm" data-org="tl-status"${tl.line && ready ? '' : ' disabled'}>status</button>
        <button class="pg-btn pg-btn--ghost pg-btn--sm" data-org="tl-close"${tl.line && ready ? '' : ' disabled'}>close</button>
      </div>
      ${tl.line ? `<div class="org-handle">line cell <code>${esc(tl.line.trustline)}</code></div>` : ''}
      ${tlStatus}
      <div class="org-log">${logBlock(tl)}</div>
    </div>`;

  // ---- channels panel ----
  const chStat = ch.status ? `
    <div class="org-status ${ch.status.epochs_unified ? 'is-ok' : 'is-fail'}">
      <div><strong>epoch</strong> ${esc(ch.status.epoch)} · <strong>delegation_epoch</strong> ${esc(ch.status.delegation_epoch)} ·
        <strong>epochs_unified</strong> ${ch.status.epochs_unified ? '✓ (the keystone holds)' : '✗ INVARIANT BROKEN'}</div>
      <div class="org-dim">members=${esc(String(ch.status.members))} · messages_held=${esc(String(ch.status.messages_held))} · open=${ch.status.open ? 'yes' : 'no'}</div>
    </div>` : '';

  const memberPills = ch.members.length
    ? `<div class="org-members">members: ${ch.members.map((m) => `<code class="org-member">${esc(m.label)} ${esc(m.cell.slice(0, 6))}…</code>`).join(' ')}</div>`
    : '';

  const channelsPanel = `
    <div class="org-card">
      <div class="org-card__head">
        <h3>Channels <span class="org-tag">§4 · the epoch-unification keystone</span></h3>
        <a class="org-link" href="/learn/" title="ORGANS.md §4">what is a channel? →</a>
      </div>
      <p class="org-lede">A group is a CELL. The group's key epoch and the capability freshness epoch are
        <strong>the same counter</strong>: every join / remove / rekey is ONE atomic turn that bumps the
        membership root, the epoch-key commitment, AND the cell's <code>delegation_epoch</code>. So
        <code>remove(m)</code> ends, in a single step, BOTH m's forward-read ability (no e+1 key) and m's
        group-held capabilities (staled by the freshness check). Watch <code>epochs_unified</code>.</p>
      <div class="org-controls">
        <button class="pg-btn pg-btn--primary pg-btn--sm" data-org="ch-create"${disabled}>create group</button>
        <button class="pg-btn pg-btn--accent pg-btn--sm" data-org="ch-join"${ch.group && ready ? '' : ' disabled'}>join member</button>
        <button class="pg-btn pg-btn--ghost pg-btn--sm" data-org="ch-remove"${ch.group && ch.members.length > 1 && ready ? '' : ' disabled'}>remove last</button>
        <button class="pg-btn pg-btn--ghost pg-btn--sm" data-org="ch-status"${ch.group && ready ? '' : ' disabled'}>status</button>
      </div>
      ${ch.group ? `<div class="org-handle">group cell <code>${esc(ch.group.channel)}</code> · epoch ${esc(ch.group.epoch)} · fan_out ${esc(String(ch.group.fan_out?.length ?? '?'))} sealed key(s)</div>` : ''}
      ${memberPills}
      ${chStat}
      <div class="org-log">${logBlock(ch)}</div>
    </div>`;

  // ---- read-only organs (surfaced, not stubbed) ----
  const readonlyPanel = `
    <div class="org-card org-card--muted">
      <div class="org-card__head"><h3>Mailbox <span class="org-tag">§2 · hosted inbox over the relay</span></h3></div>
      <p class="org-lede">A store-and-forward relay (separate service, default <code>:3100</code>) moves opaque
        sealed bodies; the relay sees only ciphertext. Membership ops are signed by the inbox owner; every
        drained message carries a <code>DequeueProof</code> (custody). Driving it needs the relay URL — bring
        one and use <code>new MailboxClient(relayUrl, identity)</code>.</p>
      <pre class="org-snip">const mb = new MailboxClient("http://relay:3100", identity);
await mb.subscribe();                  // create your hosted inbox
const { messages } = await mb.drain(); // custody-proofed batch</pre>
    </div>
    <div class="org-card org-card--muted">
      <div class="org-card__head"><h3>Attested query <span class="org-tag">§ · the light-client read</span></h3></div>
      <p class="org-lede">The read-only twin: a light client trusts a verdict from verifying ONE succinct
        whole-history aggregate, re-witnessing nothing. This client FETCHES the federation-signed roots,
        finalized checkpoints, and a turn's full-turn STARK bytes for a verifier (<code>@dregg/sdk/wasm</code>
        or Rust) — it does not yet verify threshold sigs in pure TS (a named follow-up).</p>
      <pre class="org-snip">const aq = new AttestedQuery(nodeUrl);
const roots = await aq.attestedRoots();  // federation-signed roots
const cp    = await aq.checkpoint();      // latest finalized checkpoint</pre>
    </div>`;

  const connectHint = ready ? '' : `
    <div class="org-connect">
      <strong>These organs are node-backed.</strong> A trustline's factory descriptor and a channel's seal
      fan-out are computed by the node (the enforcement tooth is the executor-installed cell program either
      way), so this section talks to a real devnet node via the <code>@dregg/sdk</code> <code>NodeClient</code>.
      Point it at one (operator-gated routes need the devnet key) — settings are shared with the Turn Workbench.
      ${sdkError ? `<div class="org-err">SDK bundle failed to load: ${esc(sdkError)}</div>` : ''}
    </div>`;

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Organs <span class="org-version">@dregg/sdk v0.3.0</span></h2>
      <p>The four <strong>organs</strong> (docs/ORGANS.md) are the v0.3.0 SDK nouns — bilateral credit, a
        hosted inbox, a light-client read, and a group key-epoch lift. They aren't browser-local primitives:
        each is the ergonomic face of a node-side service whose enforcement tooth is the executor-installed
        cell program. This section drives the two stateful organs (<strong>trustline</strong>,
        <strong>channels</strong>) against a real node through the actual SDK client a production integrator
        imports — nothing is faked when no node is connected.</p>
    </div>

    <div class="org-bar">
      ${nodeBadge()}
      <label class="org-f org-f--wide"><span>node URL</span><input id="org-url" value="${esc(nodeUrl())}" placeholder="http://localhost:8420"></label>
      <label class="org-f"><span>devnet key (operator-gated)</span><input id="org-token" type="password" value="${esc(nodeToken())}" placeholder="optional"></label>
      <button class="pg-btn pg-btn--primary pg-btn--sm" id="org-connect">connect</button>
    </div>
    ${connectHint}

    <div class="org-grid">
      ${trustlinePanel}
      ${channelsPanel}
    </div>
    <div class="org-grid">
      ${readonlyPanel}
    </div>
  `;

  wire(section);
}

function wire(section) {
  section.querySelector('#org-connect')?.addEventListener('click', () => saveSettings(section));
  const handlers = {
    'tl-open': () => tlOpen(section),
    'tl-draw': () => tlAction(section, 'draw'),
    'tl-repay': () => tlAction(section, 'repay'),
    'tl-status': () => tlAction(section, 'status'),
    'tl-close': () => tlAction(section, 'close'),
    'ch-create': () => chCreate(section),
    'ch-join': () => chJoin(section),
    'ch-remove': () => chRemove(section),
    'ch-status': () => chStatus(section),
  };
  section.querySelectorAll('[data-org]').forEach((b) =>
    b.addEventListener('click', () => handlers[b.getAttribute('data-org')]?.()));
}

export function initOrgans() {
  const section = document.getElementById('section-organs');
  if (!section) return;
  render(section);
  // Probe lazily on first paint so the badge reflects reality without blocking boot.
  probeNode(section);
}

// --- styles ------------------------------------------------------------------
(function injectStyles() {
  if (document.getElementById('org-styles')) return;
  const s = document.createElement('style');
  s.id = 'org-styles';
  s.textContent = `
.org-version { font-size:0.66rem; font-weight:700; text-transform:uppercase; letter-spacing:0.05em; color:var(--accent-bright,#7db87b); border:1px solid var(--line,#2a3530); border-radius:999px; padding:2px 9px; vertical-align:middle; }
.org-bar { display:flex; flex-wrap:wrap; align-items:flex-end; gap:10px; margin:8px 0 12px; padding:10px; border:1px solid var(--line,#2a3530); border-radius:8px; background:var(--bg-raised,#141a17); }
.org-badge { font-size:0.66rem; font-weight:700; text-transform:uppercase; letter-spacing:0.04em; border-radius:999px; padding:3px 10px; align-self:center; }
.org-badge--on { background:rgba(98,196,122,0.15); color:#8ee6a2; border:1px solid #3f7a4f; }
.org-badge--off { background:rgba(212,104,92,0.12); color:#f18b7d; border:1px solid #7a3f3a; }
.org-badge--unknown { background:rgba(201,168,76,0.12); color:#f2d06b; border:1px solid #7a6a3a; }
.org-connect { font-size:0.8rem; line-height:1.55; color:var(--text-dim,#8a958f); border:1px solid var(--line,#2a3530); border-left:3px solid #c9a84c; border-radius:6px; background:var(--bg-raised,#141a17); padding:10px 12px; margin-bottom:12px; }
.org-connect strong { color:var(--text,#e8f0e8); }
.org-grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(340px,1fr)); gap:14px; margin-bottom:14px; }
.org-card { border:1px solid var(--line,#2a3530); border-radius:8px; background:var(--bg-raised,#141a17); padding:12px 14px; }
.org-card--muted { opacity:0.92; border-style:dashed; }
.org-card__head { display:flex; align-items:baseline; justify-content:space-between; gap:8px; flex-wrap:wrap; }
.org-card__head h3 { margin:0 0 4px; font-size:0.96rem; }
.org-tag { font-size:0.62rem; font-weight:600; text-transform:uppercase; letter-spacing:0.04em; color:var(--text-dim,#8a958f); }
.org-link { color:var(--accent-bright,#8fddff); text-decoration:none; border-bottom:1px dotted currentColor; font-size:0.72rem; white-space:nowrap; }
.org-lede { font-size:0.76rem; color:var(--text-dim,#8a958f); line-height:1.5; margin:4px 0 10px; }
.org-lede code, .org-lede em { color:var(--text,#e8f0e8); font-style:normal; }
.org-controls { display:flex; flex-wrap:wrap; align-items:flex-end; gap:8px; margin:6px 0; }
.org-f { display:flex; flex-direction:column; gap:2px; font-size:0.66rem; color:var(--text-dim,#8a958f); }
.org-f--wide { flex:1 1 220px; }
.org-f input { padding:5px 7px; font:inherit; font-size:0.74rem; background:var(--bg,#0a0f0d); color:var(--text,#e8f0e8); border:1px solid var(--line,#2a3530); border-radius:4px; min-width:130px; }
.org-f--wide input { width:100%; }
.org-handle { font-size:0.7rem; color:var(--text-dim,#8a958f); margin:7px 0 3px; }
.org-handle code { color:var(--text,#e8f0e8); word-break:break-all; }
.org-members { font-size:0.7rem; color:var(--text-dim,#8a958f); margin:4px 0; }
.org-member { border:1px solid var(--line,#2a3530); border-radius:4px; padding:1px 6px; margin-right:4px; }
.org-status { font-size:0.74rem; line-height:1.5; border:1px solid var(--line,#2a3530); border-left:3px solid #64a8c8; border-radius:6px; background:var(--bg,#0a0f0d); padding:7px 10px; margin:7px 0; }
.org-status.is-ok { border-left-color:#62c47a; }
.org-status.is-fail { border-left-color:#d4685c; }
.org-status strong { color:var(--text,#e8f0e8); }
.org-snip { font-size:0.7rem; background:var(--bg,#0a0f0d); border:1px solid var(--line,#2a3530); border-radius:6px; padding:8px 10px; overflow-x:auto; color:#9fd3ad; margin:4px 0 0; }
.org-log { border:1px solid var(--line,#2a3530); border-radius:6px; background:var(--bg,#0a0f0d); padding:7px 10px; font-size:0.68rem; max-height:170px; overflow-y:auto; display:flex; flex-direction:column; gap:3px; margin-top:9px; }
.org-log__row--err { color:#f18b7d; }
.org-log__row--ok { color:#8ee6a2; }
.org-log__row--run { color:var(--text-dim,#8a958f); }
.org-dim { color:var(--text-dim,#8a958f); }
.org-err { color:#f18b7d; margin-top:6px; }
`;
  document.head.appendChild(s);
})();
