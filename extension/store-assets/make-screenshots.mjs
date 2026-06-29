// Store-listing screenshot baker for Dragon's Egg Cipherclerk.
//
// Renders the extension's REAL HTML surfaces (popup.html, confirm-intent.html,
// disclosure-picker.html) in headless Chromium with seeded display state, then
// frames each capture on a 1280x800 canvas (Chrome Web Store / AMO size).
//
// These are honestly RENDERED-not-live shots: the actual shipped markup + CSS
// are loaded from disk and populated with representative example data (no live
// node, no real keys). The chrome.* APIs are stubbed so the page scripts do not
// throw; the final DOM state is set explicitly before capture.
//
// Usage: node store-assets/make-screenshots.mjs
// Output: store-assets/*.png  (+ copies in /tmp)

import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const require = createRequire(import.meta.url);
const EXT_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const { chromium } = require(path.join(EXT_DIR, 'tests', 'node_modules', '@playwright', 'test'));

const OUT = path.join(EXT_DIR, 'store-assets');
const TMP = '/tmp';
const ICON_B64 = readFileSync(path.join(EXT_DIR, 'icons', 'icon-128.png')).toString('base64');

// A representative 24-word recovery phrase from the BIP39 list (EXAMPLE ONLY).
const DEMO_WORDS = (
  'ribbon lava cabbage tornado fabric kingdom velvet humble ' +
  'orchard signal puzzle meadow citizen render falcon mosaic ' +
  'harbor twilight ginger summit lantern voyage acorn dragon'
).split(' ');

// A faithful turn reading, in the same human terms src/explain.ts renders,
// bound to the canonical [turn <hash>] the node verifies.
const DEMO_EXPLANATION =
  `This turn does the following, signed by profile "ember":\n` +
  `\n` +
  `  1. transfer 25 computrons\n` +
  `       from cell 9f23c8a1…e4b07d52\n` +
  `       to   cell 6ad1f0bb…12c9aa80\n` +
  `\n` +
  `  2. attenuate capability cap:read /vault/ledger\n` +
  `       grant to 6ad1f0bb…12c9aa80\n` +
  `       expires in 24h, read-only\n` +
  `\n` +
  `  3. emit receipt note "settlement for invoice #4417"\n` +
  `\n` +
  `Bound to [turn b71e09c4…5fd3a128].\n` +
  `Your signature authorizes exactly the above and nothing else.`;

async function rawCapture(browser, { file, width, seed }) {
  const ctx = await browser.newContext({
    viewport: { width, height: 1400 },
    deviceScaleFactor: 2,
  });
  // Stub the extension messaging surfaces so page scripts run without throwing.
  await ctx.addInitScript(() => {
    const noop = async () => ({});
    window.chrome = {
      runtime: {
        sendMessage: noop,
        onMessage: { addListener() {} },
        getURL: (p) => p,
        connect: () => ({ postMessage() {}, onMessage: { addListener() {} }, onDisconnect: { addListener() {} } }),
        lastError: null,
      },
      storage: {
        local: { get: async () => ({}), set: async () => {}, remove: async () => {} },
        session: { get: async () => ({}), set: async () => {}, remove: async () => {} },
      },
      tabs: { query: async () => [] },
      permissions: { contains: async () => true, request: async () => true },
    };
  });
  const page = await ctx.newPage();
  await page.goto('file://' + path.join(EXT_DIR, file));
  await page.waitForLoadState('domcontentloaded');
  // Let any on-load refresh() settle (it sees empty stubbed data), then seed.
  await page.waitForTimeout(400);
  await page.evaluate(seed);
  await page.waitForTimeout(150);
  const body = page.locator('body');
  const box = await body.boundingBox();
  const buf = await page.screenshot({
    clip: { x: 0, y: 0, width, height: Math.ceil(box.height) },
  });
  await ctx.close();
  return buf;
}

async function frame(browser, { rawPng, title, caption }) {
  const ctx = await browser.newContext({
    viewport: { width: 1280, height: 800 },
    deviceScaleFactor: 1,
  });
  const page = await ctx.newPage();
  const rawB64 = rawPng.toString('base64');
  const html = `<!DOCTYPE html><html><head><meta charset="utf-8"><style>
    * { margin:0; padding:0; box-sizing:border-box; }
    html,body { width:1280px; height:800px; overflow:hidden;
      font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif; }
    body { display:flex; align-items:center; gap:56px; padding:0 80px;
      background: radial-gradient(120% 120% at 18% 8%, #2a2150 0%, #16162a 45%, #0c0c18 100%);
      color:#e8e6f5; }
    .left { width:520px; flex-shrink:0; }
    .brand { display:flex; align-items:center; gap:16px; margin-bottom:34px; }
    .brand img { width:64px; height:64px; border-radius:14px;
      box-shadow:0 10px 30px rgba(124,58,237,0.35); }
    .brand .name { font-size:24px; font-weight:700; letter-spacing:-0.01em; }
    .brand .name b { color:#c4b5fd; }
    h2 { font-size:40px; line-height:1.12; font-weight:750; letter-spacing:-0.02em;
      margin-bottom:22px; }
    h2 .accent { color:#c4b5fd; }
    p.cap { font-size:18px; line-height:1.55; color:#b9b6cf; max-width:480px; }
    .badge { display:inline-block; margin-top:30px; font-size:13px; font-weight:600;
      color:#a7f3d0; background:rgba(6,95,70,0.4); border:1px solid rgba(16,185,129,0.4);
      padding:6px 14px; border-radius:999px; letter-spacing:0.02em; }
    .right { flex:1; display:flex; justify-content:center; align-items:center; }
    .device { border-radius:20px; overflow:hidden; background:#1a1a2e;
      box-shadow:0 26px 70px rgba(0,0,0,0.55), 0 0 0 1px rgba(167,139,250,0.18);
      max-height:712px; }
    .device img { display:block; max-height:712px; width:auto; }
  </style></head><body>
    <div class="left">
      <div class="brand">
        <img src="data:image/png;base64,${ICON_B64}">
        <div class="name">Dragon's Egg <b>Cipherclerk</b></div>
      </div>
      <h2>${title}</h2>
      <p class="cap">${caption}</p>
      <div class="badge">Authorization-first · keys never leave your device</div>
    </div>
    <div class="right">
      <div class="device"><img src="data:image/png;base64,${rawB64}"></div>
    </div>
  </body></html>`;
  await page.setContent(html, { waitUntil: 'networkidle' });
  await page.waitForTimeout(200);
  const buf = await page.screenshot({ clip: { x: 0, y: 0, width: 1280, height: 800 } });
  await ctx.close();
  return buf;
}

// ---- seed functions (run inside the page) -------------------------------

function seedOnboarding(words) {
  const hide = (id) => { const e = document.getElementById(id); if (e) e.style.display = 'none'; };
  document.querySelectorAll('.tab-content').forEach((e) => (e.style.display = 'none'));
  hide('tabsNav');
  const onb = document.getElementById('onboardingSection');
  if (onb) onb.classList.remove('hidden');
  const s1 = document.getElementById('onbStep1');
  if (s1) s1.style.display = 'none';
  const s2 = document.getElementById('onbStep2');
  if (s2) { s2.classList.remove('hidden'); s2.style.display = 'block'; }
  const m = document.getElementById('onbMnemonic');
  if (m) {
    m.style.display = 'block';
    m.textContent = words.map((w, i) => String(i + 1).padStart(2, '0') + '. ' + w).join('   ');
  }
  const conf = document.getElementById('onbConfirm');
  if (conf) conf.value = '';
  const st = document.getElementById('statusText'); if (st) st.textContent = 'Setting up wallet';
  const dot = document.getElementById('statusDot'); if (dot) dot.classList.add('locked');
}

function seedCipherclerk(words) {
  const onb = document.getElementById('onboardingSection');
  if (onb) onb.classList.add('hidden');
  const st = document.getElementById('statusText'); if (st) st.textContent = 'Connected · unlocked';
  // Profile switcher
  const sel = document.getElementById('profileSelect');
  if (sel) {
    sel.innerHTML = '<option>ember</option><option>treasury</option><option>devnet-test</option>';
    sel.value = 'ember';
  }
  const pk = document.getElementById('profilePubkey');
  if (pk) pk.textContent = 'ed25519:335840a9c1f7e2b48d06ba91c3e57f4a2d8c0916b7e34af1c2d59e0a77b18b9a';
  // Receipts
  const rc = document.getElementById('receiptsContainer');
  if (rc) {
    const rows = [
      ['b71e09c4…5fd3a128', 'transfer · note', 'final · h.40912', true],
      ['2cf8a013…9ad41e60', 'attenuate', 'final · h.40908', true],
      ['e4d7710b…0c93fa22', 'mint · receipt', 'pending · h.40901', false],
    ];
    rc.innerHTML = rows.map(([h, k, f, p]) =>
      `<div class="ref-item"><div class="ref-cell">${h}</div>` +
      `<div class="ref-meta">${k} — ${f} — proof ${p ? '✓' : '…'}</div></div>`).join('');
  }
  const tc = document.getElementById('tokenCount'); if (tc) tc.textContent = '3';
  const cl = document.getElementById('chainLength'); if (cl) cl.textContent = '128';
  // Recent authorizations
  const lc = document.getElementById('logContainer');
  if (lc) {
    const auths = [
      ['read /vault/ledger', 'private · ZK proof', '2m ago'],
      ['transfer 25 computrons', 'signed turn', '14m ago'],
    ];
    lc.innerHTML = auths.map(([a, m, t]) =>
      `<div class="log-entry">${a}<div class="time">${m} · ${t}</div></div>`).join('');
  }
  // Keep the unlocked action buttons; hide passphrase / mnemonic surfaces.
  ['passphraseSection', 'passphraseSetupSection', 'mnemonicDisplay', 'mnemonicWarning']
    .forEach((id) => { const e = document.getElementById(id); if (e) { e.classList.add('hidden'); e.style.display = 'none'; } });
  const backup = document.getElementById('backupBtn'); if (backup) backup.style.display = 'block';
}

function seedCaps() {
  const onb = document.getElementById('onboardingSection');
  if (onb) onb.classList.add('hidden');
  document.querySelectorAll('.tab-content').forEach((e) => e.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach((b) => b.classList.remove('active'));
  const tab = document.getElementById('tab-capabilities');
  if (tab) tab.classList.add('active');
  document.querySelectorAll('.tab-btn').forEach((b) => {
    if (b.getAttribute('data-tab') === 'capabilities') b.classList.add('active');
  });
  const refs = document.getElementById('liveRefsContainer');
  if (refs) {
    const items = [
      ['cap:read /vault/ledger', 'from treasury · read-only · 23h left'],
      ['cap:invoke /service/oracle', 'from market-cell · 1 use left'],
    ];
    refs.innerHTML = items.map(([c, m]) =>
      `<div class="ref-item"><div class="ref-cell">${c}</div><div class="ref-meta">${m}</div></div>`).join('');
  }
  const st = document.getElementById('statusText'); if (st) st.textContent = 'Connected · unlocked';
}

function seedSigning(explanation) {
  document.body.style.minHeight = 'auto';
  const title = document.getElementById('title');
  if (title) title.textContent = 'Sign Turn';
  const sub = document.getElementById('subtitle');
  if (sub) sub.textContent = 'A page asks your cipherclerk to sign this turn. This is exactly what it does:';
  const action = document.getElementById('action'); if (action) action.textContent = 'signTurn';
  const origin = document.getElementById('origin'); if (origin) origin.textContent = 'https://app.dregg.net';
  const specRow = document.getElementById('specRow'); if (specRow) specRow.style.display = 'none';
  const optRow = document.getElementById('optionsRow'); if (optRow) optRow.style.display = 'none';
  const details = document.getElementById('details');
  if (details) { details.style.flex = '0 0 auto'; details.style.marginBottom = '16px'; }
  const exp = document.getElementById('explanation');
  if (exp) {
    exp.textContent = explanation;
    exp.style.display = 'block';
    exp.style.maxHeight = 'none';
    exp.style.fontSize = '12.5px';
    exp.style.lineHeight = '1.55';
  }
}

// ---- drive ---------------------------------------------------------------

const SHOTS = [
  {
    out: '01-signing-authorization',
    file: 'confirm-intent.html', width: 440,
    seed: `(${seedSigning.toString()})(${JSON.stringify(DEMO_EXPLANATION)})`,
    title: 'See exactly <span class="accent">what you sign</span>.',
    caption: 'Every turn is decoded into a faithful, effect-by-effect reading — bound to the canonical turn hash the node verifies. No blind signing. Your key releases a signature only on explicit approval.',
  },
  {
    out: '02-onboarding',
    file: 'popup.html', width: 360,
    seed: `(${seedOnboarding.toString()})(${JSON.stringify(DEMO_WORDS)})`,
    title: 'Your keys, <span class="accent">on your device</span>.',
    caption: 'Guided first-run setup forces a passphrase and a recovery-phrase backup before any key is created. Keys are encrypted at rest with AES-256-GCM. A wallet is never left under a key a browser restart could orphan.',
  },
  {
    out: '03-identity-receipts',
    file: 'popup.html', width: 360,
    seed: `(${seedCipherclerk.toString()})(${JSON.stringify(DEMO_WORDS)})`,
    title: 'Named identities, <span class="accent">live receipts</span>.',
    caption: 'An identity is a name you chose, not a hex key you pasted. Switch profiles, watch the node receipt stream commit your turns in real time, and review every recent authorization.',
  },
  {
    out: '04-capabilities',
    file: 'popup.html', width: 360,
    seed: `(${seedCaps.toString()})()`,
    title: 'Hold and share <span class="accent">capabilities</span>.',
    caption: 'Capability tokens are attenuable, expiring grants. Accept a dregg:// reference, share a scoped capability to another cell, and authorize against held tokens — all confirmed by you.',
  },
  {
    out: '05-zk-disclosure',
    file: 'disclosure-picker.html', width: 440,
    seed: `(() => { document.body.style.minHeight='auto'; const o = document.getElementById('originName'); if (o) o.textContent='app.dregg.net'; const a=document.getElementById('actionName'); if(a)a.textContent='read'; const r=document.getElementById('resourceName'); if(r)r.textContent='/vault/ledger'; const p=document.getElementById('preview'); if(p){p.textContent='Preview: the verifier will learn only allow / deny.'; p.style.cssText='display:block;background:#0f172a;border:1px solid #374151;border-radius:8px;padding:12px;margin-bottom:16px;font-size:12px;color:#9ca3af;';} })()`,
    title: 'Prove it <span class="accent">without revealing it</span>.',
    caption: 'Selective disclosure lets you share a full token, reveal only chosen facts, or prove authorization in zero knowledge with range predicate proofs — the verifier learns only allow or deny.',
  },
];

const { writeFileSync } = require('node:fs');

const browser = await chromium.launch();
for (const s of SHOTS) {
  process.stdout.write(`capturing ${s.out} … `);
  const raw = await rawCapture(browser, { file: s.file, width: s.width, seed: s.seed });
  const framed = await frame(browser, { rawPng: raw, title: s.title, caption: s.caption });
  const dest = path.join(OUT, s.out + '.png');
  writeFileSync(dest, framed);
  writeFileSync(path.join(TMP, s.out + '.png'), framed);
  // Also keep the bare UI capture (useful as small tiles / debugging).
  writeFileSync(path.join(OUT, s.out + '-raw.png'), raw);
  console.log('ok ->', dest);
}
await browser.close();
console.log('done');
