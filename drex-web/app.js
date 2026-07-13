// app.js — DrEX web app. Drives the sealed order end-to-end:
//   confirm-intent approve → REAL sign + REAL prove (wallet wasm) →
//   sealed commit/reveal → clear-side mirror → fill + graded fairness panel.
import {
  initWallet, traderKey, signOrderTurn, proveSolvency, tamperCheck,
  proveEligibility, sealedCommit, sealedReveal, randHex, hex,
} from './drex-wallet.mjs';
import {
  demoBook, aggregate, findRings, settleRing, clearingReport, rejectPolarity, fairnessLedger,
} from './drex-clearside.js';

const $ = (id) => document.getElementById(id);
const book = demoBook();
let walletReady = false;

// ── render the sealed order book (left rail) ──
function renderBook(reveal = false) {
  $('book').innerHTML = book.map((o, i) => {
    const mine = o.trader === 'Ada';
    const body = reveal
      ? `<span class="m">offers ${o.offerAmount} ${o.offerAsset} · wants ≥ ${o.wantMin} ${o.wantAsset}</span>`
      : `<span class="m">committed · <span class="mono fade">H(order‖salt)</span></span>`;
    return `<div class="card ord ${mine ? 'mine' : ''}">
      <span class="t">${o.trader}${mine ? ' · you' : ''}</span>
      <span class="sealed">${reveal ? 'revealed' : 'sealed'}</span>
      ${body}
      <span class="m">priority ${o.priority}</span>
    </div>`;
  }).join('');
}

// ── flow log (center) ──
const steps = [];
function step(id, h, opts = {}) {
  let s = steps.find(x => x.id === id);
  if (!s) { s = { id }; steps.push(s); }
  Object.assign(s, { h, ...opts });
  drawFlow();
  return s;
}
function drawFlow() {
  $('flow').innerHTML = steps.map(s => {
    const badge = s.real ? '<span class="real">REAL wasm</span>'
      : s.mirror ? '<span class="mirror">clear-side mirror</span>' : '';
    return `<div class="step ${s.state || ''}">
      <div class="h">${s.h}${badge}</div>
      ${s.d ? `<div class="d">${s.d}</div>` : ''}
    </div>`;
  }).join('');
}

// ── the reused confirm-intent modal ──
function currentOrder() {
  return {
    v: 1,
    sell: { asset: $('sellAsset').value, amount: +$('sellAmt').value },
    want: { asset: $('wantAsset').value, min: +$('wantMin').value },
    limitRate: $('limit').value,
    sealedUntilBatch: 'T+1',
    priority: 3,
  };
}
function openIntent(order) {
  const nonce = randHex().slice(0, 16);
  $('mSell').querySelector('.v').textContent = `${order.sell.amount} ${order.sell.asset}`;
  $('mWant').querySelector('.v').textContent = `≥ ${order.want.min} ${order.want.asset}`;
  $('mLimit').querySelector('.v').textContent = order.limitRate;
  $('mExpl').textContent =
    `[order drex_place_order]\n  place a SEALED bid on DrEX:\n  sell ${order.sell.amount} ${order.sell.asset}\n  want ≥ ${order.want.min} ${order.want.asset}  (limit ${order.limitRate})\n  hidden until batch T+1, then matched in the multilateral clearing.\n  the cipherclerk signs this exact order (nonce-bound) — nothing else.`;
  $('mNonce').textContent = 'nonce ' + nonce + ' · this approval is bound to exactly what is shown above';
  $('modal').classList.add('show');
  return new Promise((resolve) => {
    const done = (ok) => { $('modal').classList.remove('show'); $('acceptBtn').onclick = null; $('rejectBtn').onclick = null; resolve({ ok, nonce }); };
    $('acceptBtn').onclick = () => done(true);
    $('rejectBtn').onclick = () => done(false);
  });
}

// ── the full flow ──
async function place() {
  steps.length = 0; drawFlow();
  $('placeBtn').disabled = true;
  const order = currentOrder();
  const holdings = +$('holdings').value;

  // confirm-intent approve (anti-blind-sign)
  step('confirm', 'Confirm intent — nonce-bound order card', { state: 'active', d: 'awaiting your approval in the cipherclerk popup…' });
  const { ok, nonce } = await openIntent(order);
  if (!ok) { step('confirm', 'Confirm intent — rejected', { state: 'fail', d: 'you declined; nothing signed.' }); $('placeBtn').disabled = false; return; }
  step('confirm', 'Confirm intent — approved', { state: 'done', d: 'nonce ' + nonce + ' bound to the displayed order' });

  const key = traderKey(1);

  // STEP 1 — sealed commit
  const salt = randHex();
  const commit = await sealedCommit(order, salt);
  step('commit', 'Sealed-bid commit', { state: 'done', d: 'H(order‖salt) = ' + commit.slice(0, 40) + '…  (order hidden until batch T)' });

  // STEP 2 — REAL sign order-turn
  step('sign', 'Sign the order-turn', { real: true, state: 'active', d: 'cipherclerk_make_action_turn …' });
  await tick();
  const signed = signOrderTurn(order, key);
  step('sign', 'Sign the order-turn', { real: true, state: 'done',
    d: `Ed25519-signed dregg Turn\n  turn_id: ${signed.turnId}\n  agent cell: ${signed.agentCell.slice(0,24)}…\n  hybrid PQ envelope: ${signed.envelopeLen} bytes (ed25519 + ML-DSA-65 / FIPS-204)` });

  // STEP 3 — REAL solvency proof
  step('solv', 'Prove solvency (offer covered, non-inflating)', { real: true, state: 'active', d: 'prove_conservation → Bulletproofs + Schnorr …' });
  await tick();
  const sol = proveSolvency(holdings, order.sell.amount, signed.turnId);
  if (!sol.ok) {
    step('solv', 'Prove solvency — FAIL-CLOSED', { real: true, state: 'fail', d: sol.reason || 'proof did not verify' });
    $('placeBtn').disabled = false; return;
  }
  step('solv', 'Prove solvency', { real: true, state: 'done',
    d: `holdings ${sol.holdings} = offer ${sol.offer} + change ${sol.change}  ⇒  offer covered, change ≥ 0\n  verify_conservation_proof → valid=${sol.valid}, range_proofs_checked=${sol.rangeProofsChecked}\n  ${sol.rangeProofs} Bulletproof range proofs · bound to order via message_hex=turn_id` });

  // STEP 3b — tamper check
  const forgedTurn = signOrderTurn({ ...order, want: { asset: 'ART', min: 1 } }, key).turnId;
  const tamper = tamperCheck(sol, forgedTurn);
  step('tamper', 'Tamper check — substituted order rejected', { real: true, state: tamper.valid ? 'fail' : 'done',
    d: `re-verify the SAME proof against a forged order id → valid=${tamper.valid}\n  ${tamper.error || ''}` });

  // STEP 4 — REAL eligibility
  step('elig', 'Prove trading eligibility (anonymous)', { real: true, state: 'active', d: 'prove_anonymous_membership …' });
  await tick();
  const ring = book.map((_, i) => hex(traderKey(i + 1)));
  const elig = proveEligibility(hex(key), ring);
  step('elig', 'Prove trading eligibility', { real: true, state: 'done',
    d: `blinded ring membership over ${elig.ringSize} eligible traders (identity hidden)\n  presentation tag (nullifier): ${elig.presentationTag.slice(0,40)}…` });

  // hold onto the order for reveal/clear
  window.__drexPending = { order, salt, commit, signed, sol, elig };
  $('clock').innerHTML = `<span class="ok">order sealed + proven.</span> advance the batch to reveal &amp; clear.`;
  $('batchPill').className = 'pill warn'; $('batchPill').textContent = 'batch T+1 · ready to clear';
  // add an advance button
  if (!$('advanceBtn')) {
    const b = document.createElement('button'); b.className = 'primary'; b.id = 'advanceBtn';
    b.textContent = 'Advance batch → reveal & clear'; b.onclick = clearBatch;
    $('placeBtn').after(b);
  }
  $('placeBtn').disabled = false;
}

// ── reveal + clear the batch ──
async function clearBatch() {
  $('advanceBtn').disabled = true;
  const p = window.__drexPending;

  // reveal
  const rev = await sealedReveal(p.commit, p.order, p.salt);
  step('reveal', 'Sealed-bid reveal at batch T', { state: rev.ok ? 'done' : 'fail',
    d: 'reveal (order, salt) → commitment binds: ' + rev.ok });
  renderBook(true);
  $('batchPill').className = 'pill live'; $('batchPill').textContent = 'batch T+1 · cleared';

  // clear-side mirror
  const { agg, ok: aggOk } = aggregate(book);
  const { twoCycles, ring: ringIdx } = findRings(book);
  const legs = settleRing(book, ringIdx);
  step('match', 'Match — multilateral ring found', { mirror: true, state: 'done',
    d: `bilateral (2-party) matches: ${twoCycles} → genuinely multilateral\n  ring: ${ringIdx.map(i=>book[i].trader).join(' → ')} → ${book[ringIdx[0]].trader}\n  ` + legs.map(l=>`${l.fromTrader}→${l.toTrader} ${l.amount} ${l.asset}`).join('  ·  ') });
  const rep = clearingReport(book, ringIdx, legs);
  const rj = rejectPolarity(book, legs);
  step('settle', 'Settle — conserving, all-or-nothing', { mirror: true, state: 'done',
    d: `over-debit reject polarity: drained ${rj.victim} one short → leg ${rj.refusedAt} refused, whole ring aborts (${rj.settledLegs} legs settled)` });

  renderCleared(rep, legs);
  renderFairness();
}

function renderCleared(rep, legs) {
  const maxAmt = Math.max(...legs.map(l => l.amount));
  const color = { GOLD: '#f0c14b', ART: '#bc8cff', WINE: '#f85149', SILVER: '#8b949e', PEARL: '#58a6ff' };
  let html = '<div class="card">';
  html += rep.alloc.map(a => {
    const mine = a.trader === 'Ada';
    return `<div class="alloc ${mine ? 'mine' : ''}">
      <span class="who">${a.trader}${mine ? ' · you' : ''}</span>
      <span class="leg">sent ${a.sent} ${a.sentAsset} · got ${a.received} ${a.recvAsset} (≥${a.wantMin})</span>
      <span class="${a.ir && a.budget ? 'ok' : 'no'}">${a.ir && a.budget ? '✔' : '✗'}</span>
    </div>`;
  }).join('');
  html += rep.rested.map(t => `<div class="alloc"><span class="who fade">${t}</span><span class="leg fade">rests — no match this batch</span><span class="fade">·</span></div>`).join('');
  html += '</div>';
  // conservation bars
  html += '<div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">per-asset conservation (in = out)</div>';
  html += rep.conservation.map(c =>
    `<div class="leg">${c.asset}: ${c.in} in = ${c.out} out <span class="ok">✔</span></div>
     <div class="bar"><span style="width:100%;background:${color[c.asset]||'#58a6ff'}"></span></div>`).join('');
  html += '</div>';
  $('cleared').innerHTML = html;
}

function renderFairness() {
  $('fair').innerHTML = fairnessLedger().map(f => {
    const chips = f.grades.map(g => `<span class="chip ${g === 'NOT-IN-THIS-BATCH' ? 'NOTBATCH' : g}">${g}</span>`).join('');
    return `<div class="fair">
      <div>${chips}</div>
      <div class="lab" style="margin-top:6px">${f.label}</div>
      <div class="det">${f.detail}</div>
      <div class="cite">${f.lean}</div>
    </div>`;
  }).join('');
}

const tick = () => new Promise(r => setTimeout(r, 30));

// ── boot ──
(async function boot() {
  renderBook(false);
  renderFairness();
  $('placeBtn').onclick = place;
  try {
    await initWallet();
    walletReady = true;
    $('walletPill').className = 'pill live';
    $('walletPill').textContent = 'wallet: Dragon\'s Egg Cipherclerk · ready';
    $('placeBtn').disabled = false;
  } catch (e) {
    $('walletPill').className = 'pill warn';
    $('walletPill').textContent = 'wallet: wasm load failed — run via serve.mjs';
    console.error(e);
  }
})();
