// gate/run-gate.mjs — the DrEX gate: drive a sealed-bid order end-to-end with
// REAL wallet-wasm proving, then clear the batch and show the fill + fairness.
//
//   node drex-web/gate/run-gate.mjs
//
// What is REAL here (the extension wasm actually runs):
//   • cipherclerk_make_action_turn  — a real Ed25519-signed order Turn
//   • assemble_signed_turn_envelope — the real hybrid ed25519 + ML-DSA-65 envelope
//   • prove_conservation / verify_conservation_proof — a real Bulletproofs+Schnorr
//     solvency proof, verified green, and a tamper attempt shown flipping to false
//   • prove_anonymous_membership    — a real blinded eligibility tag
// What is a LABELED stand-in: the matcher/settlement (clear-side mirror of
//   solver.rs + verified_settle.rs — see drex-clearside.js banner).

import {
  initWallet, traderKey, signOrderTurn, proveSolvency, tamperCheck,
  proveEligibility, sealedCommit, sealedReveal, randHex, hex,
} from '../drex-wallet.mjs';
import {
  demoBook, aggregate, findRings, settleRing, clearingReport, rejectPolarity, fairnessLedger,
} from '../drex-clearside.js';

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

  // ── STEP 6 — clear the batch (LABELED mirror of solver.rs/verified_settle.rs) ──
  rule('STEP 6 · clear the batch  \x1b[33m[clear-side MIRROR; real matcher = solver.rs/verified_settle.rs]\x1b[0m');
  const { agg, ok: aggOk } = aggregate(book);
  line('  rung-2 aggregate: faithful permutation, sorted by priority → ' + (aggOk ? ok('✔') : bad('✗')));
  const { twoCycles, ring: ringIdx } = findRings(book);
  line('  bilateral (2-party) matches among cross-bid traders: ' + twoCycles + '  → genuinely multilateral');
  if (!ringIdx) throw new Error('GATE FAIL: matcher found no clearing ring');
  const legs = settleRing(book, ringIdx);
  line('  clearing ring: ' + ringIdx.map(i => book[i].trader).join(' → ') + ' → ' + book[ringIdx[0]].trader);
  for (const l of legs) line('    leg  ' + l.fromTrader.padEnd(4) + ' → ' + l.toTrader.padEnd(4) + '  ' + String(l.amount).padStart(3) + ' ' + l.asset);

  const rep = clearingReport(book, ringIdx, legs);
  rule('CLEARED ALLOCATIONS + your fill');
  for (const a of rep.alloc) {
    const mine = a.trader === 'Ada' ? ' \x1b[35m← your fill\x1b[0m' : '';
    line('  ' + a.trader.padEnd(4) + ' sent ' + String(a.sent).padStart(3) + ' ' + a.sentAsset.padEnd(6) +
         ' received ' + String(a.received).padStart(3) + ' ' + a.recvAsset.padEnd(6) +
         ' (wanted ≥ ' + a.wantMin + ') ' + (a.ir && a.budget ? ok('✔') : bad('✗')) + mine);
  }
  for (const t of rep.rested) line('  ' + t.padEnd(4) + ' rests (no match this batch)');

  rule('WHY IT\'S FAIR — proved properties, graded');
  line('  conservation (in = out):');
  for (const c of rep.conservation) line('    ' + c.asset.padEnd(6) + ': ' + c.in + ' in = ' + c.out + ' out ' + (c.ok ? ok('✔') : bad('✗')));
  line('  limits (IR + budget), every participant: ' + (rep.limitsOk ? ok('✔') : bad('✗')));
  line('');
  for (const f of fairnessLedger()) {
    line('  ' + f.grades.map(g => gradeChip(g)).join(' ') + ' ' + f.label);
    line('        ' + f.lean);
  }

  // ── STEP 7 — reject polarity ──
  rule('STEP 7 · reject polarity — a bad settlement is refused, atomically');
  const rj = rejectPolarity(book, legs);
  line('  drained ' + rj.victim + '\'s ' + rj.asset + ' to ' + rj.starvedTo + ' (one short of its ' + rj.need + ' leg)');
  line('  verified kernel → leg ' + rj.refusedAt + ' refused; whole ring aborts (' + rj.settledLegs + ' legs settled) ' +
       (rj.aborted ? ok('✔') : bad('✗')));
  if (!rj.aborted) throw new Error('GATE FAIL: over-debit must be refused');

  rule('GATE RESULT');
  const pass = sol.ok && !tamper.valid && rev.ok && aggOk && rep.limitsOk && rep.conservesOk && rj.aborted;
  line('  ' + (pass ? ok('PASS') : bad('FAIL')) +
       ' — real signed order-turn + real solvency proof (verified, tamper-rejected) +');
  line('         real anonymous eligibility, driven through a sealed-bid batch to a fair, conserving fill.');
  if (!pass) process.exit(1);
}

function gradeChip(g) {
  const c = { PROVED: 42, ATTESTED: 44, REPLAYABLE: 45, 'NOT-IN-THIS-BATCH': 100 }[g] || 47;
  return '\x1b[' + c + ';30m ' + g + ' \x1b[0m';
}

main().catch(e => { console.error('\x1b[31mGATE ERROR:\x1b[0m', e); process.exit(1); });
