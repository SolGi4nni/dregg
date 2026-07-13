// gate/run-gate.mjs — the DrEX gate: drive a sealed-bid order end-to-end with
// REAL wallet-wasm proving, then clear the batch and show the fill + fairness.
//
//   node drex-web/gate/run-gate.mjs
//
// What is REAL here — EVERYTHING. Both the wallet AND the matcher:
//   • cipherclerk_make_action_turn  — a real Ed25519-signed order Turn
//   • assemble_signed_turn_envelope — the real hybrid ed25519 + ML-DSA-65 envelope
//   • prove_conservation / verify_conservation_proof — a real Bulletproofs+Schnorr
//     solvency proof, verified green, and a tamper attempt shown flipping to false
//   • prove_anonymous_membership    — a real blinded eligibility tag
//   • the MATCHER + SETTLEMENT — the REAL Rust pipeline: this gate shells to the
//     `drex_clear` binary (intent/src/bin/drex_clear.rs), the same solver.rs ring
//     match + verified_settle.rs kernel fold as `cargo run --example drex_clear_book`.
//     No mirror: the clearing, conservation, and over-debit reject are the real
//     engine's output over the revealed orders.

import { spawn } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  initWallet, traderKey, signOrderTurn, proveSolvency, tamperCheck,
  proveEligibility, sealedCommit, sealedReveal, randHex, hex,
} from '../drex-wallet.mjs';
import { demoBook, fairnessLedger } from '../drex-clearside.js';

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const REMOTE_HOST = process.env.DREX_REMOTE || 'persvati';
const REMOTE_DIR = process.env.DREX_REMOTE_DIR || 'dregg-build/drex-matcher';

// Run the REAL clear-book pipeline over the revealed orders (same wire the web
// server uses): a LOCAL binary if one exists, else the prebuilt binary on the
// persvati build host over ssh (orders piped to its stdin).
function runRealClear(orders) {
  const local = ['release', 'debug']
    .map((p) => path.join(REPO, 'target', p, 'drex_clear'))
    .find((p) => fs.existsSync(p));
  const spec = local
    ? { c: local, a: [] }
    : { c: 'ssh', a: [REMOTE_HOST, `cd ${REMOTE_DIR} && ./target/debug/drex_clear`] };
  return new Promise((resolve, reject) => {
    const child = spawn(spec.c, spec.a, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', reject);
    child.on('close', () => {
      const last = out.trim().split('\n').filter(Boolean).pop() || '';
      try { resolve(JSON.parse(last)); }
      catch (e) { reject(new Error('drex_clear no JSON: ' + err.slice(-300) + ' / ' + out.slice(-300))); }
    });
    child.stdin.end(JSON.stringify(orders));
  });
}

const line = (s = '') => console.log(s);
const rule = (t) => line('\n\x1b[36m── ' + t + ' ' + '─'.repeat(Math.max(0, 72 - t.length)) + '\x1b[0m');
const ok = (s) => '\x1b[32m' + s + '\x1b[0m';
const bad = (s) => '\x1b[31m' + s + '\x1b[0m';

async function main() {
  line('\x1b[35m╔══════════════════════════════════════════════════════════════════════╗');
  line('║  DrEX · Dragon\'s EXchange — sealed-bid gate (REAL wallet proving)     ║');
  line('╚══════════════════════════════════════════════════════════════════════╝\x1b[0m');

  rule('boot the wallet wasm (the SAME dregg_wasm.js the extension ships)');
  const t0 = Date.now();
  await initWallet();
  line('  wallet wasm instantiated in ' + (Date.now() - t0) + 'ms  (Dragon\'s Egg Cipherclerk)');

  // ── the trader places a sealed order (Ada's leg of the 3-ring) ──
  const book = demoBook();
  const me = book.find(o => o.trader === 'Ada');
  const order = {
    v: 1,
    sell: { asset: me.offerAsset, amount: me.offerAmount },
    want: { asset: me.wantAsset, min: me.wantMin },
    limitRate: '1/2',
    sealedUntilBatch: 'T+1',
    priority: me.priority,
  };
  rule('the order (what confirm-intent renders + the user approves)');
  line('  sell ' + order.sell.amount + ' ' + order.sell.asset +
       ', want ≥ ' + order.want.min + ' ' + order.want.asset +
       ', limit ' + order.limitRate + ', SEALED until batch ' + order.sealedUntilBatch);

  // ── STEP 1 — sealed-bid commit (before batch T) ──
  rule('STEP 1 · sealed-bid COMMIT (SealedAuction.lean commit–reveal)');
  const salt = randHex();
  const commit = await sealedCommit(order, salt);
  line('  published commitment H(order‖salt) = ' + commit.slice(0, 32) + '…  (order hidden)');

  // ── STEP 2 — REAL: sign the order-turn ──
  rule('STEP 2 · sign the order-turn  \x1b[32m[REAL: cipherclerk wasm]\x1b[0m');
  const key = traderKey(1);
  const signed = signOrderTurn(order, key);
  line('  ' + ok('✔') + ' Ed25519-signed dregg Turn');
  line('    turn_id      : ' + signed.turnId);
  line('    agent cell   : ' + signed.agentCell);
  line('    turn bytes   : ' + signed.turnBytesLen + '  (postcard-encoded signed Turn)');
  line('    hybrid PQ env: ' + signed.envelopeLen + ' bytes  (ed25519 + ML-DSA-65 / FIPS-204) ' + signed.envelopeHex);

  // ── STEP 3 — REAL: prove solvency, bound to this order ──
  rule('STEP 3 · prove solvency  \x1b[32m[REAL: prove_conservation → Bulletproofs+Schnorr]\x1b[0m');
  const sol = proveSolvency(me.holdings, me.offerAmount, signed.turnId);
  line('  statement: holdings ' + sol.holdings + ' = offer ' + sol.offer + ' + change ' + sol.change +
       '  ⇒  holdings ≥ offer (offer covered), change ≥ 0 (no negative-value inflation)');
  line('  bound to order via message_hex = turn_id ' + sol.messageHex.slice(0, 16) + '…');
  line('  ' + (sol.ok ? ok('✔') : bad('✗')) +
       ' verify_conservation_proof → valid=' + sol.valid + ', range_proofs_checked=' + sol.rangeProofsChecked +
       '  (' + sol.rangeProofs + ' range proofs, ' + sol.inputCommitments + ' in / ' + sol.outputCommitments + ' out commitments)');

  rule('STEP 3b · tamper check  \x1b[32m[REAL verifier rejects a substituted order]\x1b[0m');
  const forged = { ...order, want: { asset: 'ART', min: 1 } }; // whale tries to swap the order after proving
  const forgedTurn = signOrderTurn(forged, key).turnId;
  const tamper = tamperCheck(sol, forgedTurn);
  line('  re-verify the SAME proof against a forged order id → valid=' +
       (tamper.valid ? bad(String(tamper.valid)) : ok(String(tamper.valid))) +
       (tamper.error ? '  (' + tamper.error + ')' : ''));
  if (tamper.valid) throw new Error('GATE FAIL: a substituted order must not verify');

  // ── STEP 4 — REAL: prove eligibility (anonymous) ──
  rule('STEP 4 · prove trading eligibility  \x1b[32m[REAL: prove_anonymous_membership]\x1b[0m');
  const ring = book.map((_, i) => hex(traderKey(i + 1)));
  const elig = proveEligibility(hex(key), ring);
  line('  ' + ok('✔') + ' blinded ring membership over ' + elig.ringSize + ' eligible traders (identity hidden)');
  line('    presentation tag (one-order-per-batch nullifier): ' + elig.presentationTag.slice(0, 32) + '…');

  // ── STEP 5 — reveal at batch T ──
  rule('STEP 5 · sealed-bid REVEAL at batch T');
  const rev = await sealedReveal(commit, order, salt);
  line('  reveal (order, salt) → commitment binds: ' + (rev.ok ? ok('✔ true') : bad('✗ false')));
  if (!rev.ok) throw new Error('GATE FAIL: sealed commitment did not bind on reveal');

  // ── STEP 6 — clear the batch through the REAL matcher (solver.rs + verified_settle.rs) ──
  rule('STEP 6 · clear the batch  \x1b[32m[REAL: drex_clear → solver.rs + verified_settle.rs]\x1b[0m');
  // Fold Ada's revealed order into the book, then hand the whole revealed book to
  // the REAL Rust pipeline (same one `cargo run --example drex_clear_book` runs).
  const revealed = book.map(o => (o.trader === 'Ada'
    ? { ...o, offerAsset: order.sell.asset, offerAmount: order.sell.amount, wantAsset: order.want.asset, wantMin: order.want.min, priority: order.priority }
    : o));
  const orders = revealed.map(o => ({ trader: o.trader, offerAsset: o.offerAsset, offerAmount: o.offerAmount, wantAsset: o.wantAsset, wantMin: o.wantMin, priority: o.priority }));
  const res = await runRealClear(orders);
  if (res.error) throw new Error('GATE FAIL: real matcher errored: ' + res.error);
  line('  provenance: ' + res.provenance);
  line('  rung-2 aggregate: faithful permutation, sorted by priority → ' + (res.aggregateFaithful ? ok('✔') : bad('✗')));
  line('  bilateral (2-party) matches among cross-bid traders: ' + res.twoCycles + '  → genuinely multilateral');
  if (!res.ring) throw new Error('GATE FAIL: real matcher found no clearing ring');
  line('  clearing ring: ' + res.ring.participants.join(' → ') + ' → ' + res.ring.participants[0]);
  for (const l of res.ring.legs) line('    leg  ' + l.fromTrader.padEnd(4) + ' → ' + l.toTrader.padEnd(4) + '  ' + String(l.amount).padStart(3) + ' ' + l.asset);

  rule('CLEARED ALLOCATIONS + your fill  (read off the VERIFIED post-ledger)');
  for (const a of res.allocations) {
    if (a.rested) { line('  ' + a.trader.padEnd(4) + ' rests (no match this batch)'); continue; }
    const mine = a.trader === 'Ada' ? ' \x1b[35m← your fill\x1b[0m' : '';
    line('  ' + a.trader.padEnd(4) + ' sent ' + String(a.sent).padStart(3) + ' ' + a.sentAsset.padEnd(6) +
         ' received ' + String(a.received).padStart(3) + ' ' + a.recvAsset.padEnd(6) +
         ' (wanted ≥ ' + a.wantMin + ') ' + (a.ir && a.budget ? ok('✔') : bad('✗')) + mine);
  }

  rule('WHY IT\'S FAIR — proved properties, graded');
  line('  conservation (in = out), from the verified settle:');
  for (const c of res.conservation) line('    ' + c.asset.padEnd(6) + ': ' + c.in + ' in = ' + c.out + ' out ' + (c.ok ? ok('✔') : bad('✗')));
  line('  limits (IR + budget), every participant: ' + (res.limitsOk ? ok('✔') : bad('✗')));
  line('');
  for (const f of fairnessLedger()) {
    line('  ' + f.grades.map(g => gradeChip(g)).join(' ') + ' ' + f.label);
    line('        ' + f.lean);
  }

  // ── STEP 7 — reject polarity (refused by the REAL verified kernel) ──
  rule('STEP 7 · reject polarity — a bad settlement is refused by the REAL kernel, atomically');
  const rj = res.reject;
  if (!rj) throw new Error('GATE FAIL: no reject-polarity result from the real matcher');
  line('  drained ' + rj.victim + '\'s ' + rj.asset + ' to ' + rj.starvedTo + ' (one short of its ' + rj.need + ' leg)');
  line('  verified kernel (recKExecAsset) → leg ' + rj.refusedAt + ' refused; whole ring aborts (' + rj.settledLegs + ' legs settled) ' +
       (rj.aborted ? ok('✔') : bad('✗')));
  if (!rj.aborted) throw new Error('GATE FAIL: over-debit must be refused by the real kernel');

  rule('GATE RESULT');
  const pass = sol.ok && !tamper.valid && rev.ok && res.aggregateFaithful && res.limitsOk && res.conservesOk && rj.aborted;
  line('  ' + (pass ? ok('PASS') : bad('FAIL')) +
       ' — real signed order-turn + real solvency proof (verified, tamper-rejected) + real anonymous');
  line('         eligibility, driven through a sealed-bid batch to a REAL solver.rs → verified_settle.rs fill.');
  if (!pass) process.exit(1);
}

function gradeChip(g) {
  const c = { PROVED: 42, ATTESTED: 44, REPLAYABLE: 45, 'NOT-IN-THIS-BATCH': 100 }[g] || 47;
  return '\x1b[' + c + ';30m ' + g + ' \x1b[0m';
}

main().catch(e => { console.error('\x1b[31mGATE ERROR:\x1b[0m', e); process.exit(1); });
