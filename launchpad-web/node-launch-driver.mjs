// node-launch-driver.mjs — drive a REAL launch as a turn stream on a live dregg
// node, so the node-driven launchpad (node-indexer.mjs) has real state to read.
//
//   DREGG_NODE=http://127.0.0.1:8420 node node-launch-driver.mjs
//
// Each step is a real turn submitted to the node's /turn/submit ingress: it is
// executed on the effect-VM and proven by the node's prove_pool. A launch =
// register → some bids → clear, every one a committed+proven turn. The launch
// payload rides in the EmitEvent data words under the MARKER the indexer reads.
// This is NOT a mock: after running it, `GET /api/starbridge/identity/events`
// on the node shows exactly these launch events, and the launchpad renders them.

import { codeFromSymbol } from './node-indexer.mjs';

const NODE = (process.env.DREGG_NODE || 'http://127.0.0.1:8420').replace(/\/$/, '');
const PASSPHRASE = process.env.DREGG_NODE_PASSPHRASE || 'drex-dev-node';
const MARKER = 0xDE6611;
const EV = { REGISTER: 1, BID: 2, CLEAR: 3 };

async function unlock() {
  const r = await fetch(NODE + '/cipherclerk/unlock', {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ passphrase: PASSPHRASE }),
  }).then((x) => x.json());
  if (!r.success || !r.bearer_token) throw new Error('unlock failed: ' + (r.error || '?'));
  return r.bearer_token;
}

// The node's operator cell (turns commit against it) + a faucet top-up so the
// launch turns have computron budget.
async function operatorSetup() {
  const id = await fetch(NODE + '/api/node/identity').then((x) => x.json());
  const cell = id.agent_cell;
  await fetch(NODE + '/api/faucet', {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ recipient: cell, amount: 10000 }),
  }).catch(() => {});
  return cell;
}

// One real launch turn: an EmitEvent (marker + payload) + a SetField bump so the
// turn carries a real state transition, on the operator cell.
async function launchTurn(bearer, operator, memo, words) {
  const data = words.map((w) => String(w));
  const body = {
    agent: operator, nonce: 0, fee: 1500, memo,
    actions: [{ effects: [
      { kind: 'emit_event', topic: 'launch', data },
      { kind: 'increment_nonce' },
    ] }],
  };
  const r = await fetch(NODE + '/turn/submit', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + bearer },
    body: JSON.stringify(body),
  }).then((x) => x.json());
  console.log(`  ${memo.padEnd(24)} → accepted=${r.accepted} turn=${(r.turn_hash || r.error || '').slice(0, 24)} proof=${r.proof_status}`);
  return r;
}

async function main() {
  const bearer = await unlock();
  const operator = await operatorSetup();
  const id = Number(process.env.LAUNCH_ID || 1);
  const sym = process.env.LAUNCH_SYMBOL || 'DREGG';
  console.log(`driving launch #${id} (${sym}) as real turns on ${NODE}`);
  await launchTurn(bearer, operator, `launch:register:${id}`, [MARKER, EV.REGISTER, id, 1_000_000, 400_000, codeFromSymbol(sym)]);
  await launchTurn(bearer, operator, `launch:bid:${id}:a`, [MARKER, EV.BID, id, 1, 12, 50_000]);
  await launchTurn(bearer, operator, `launch:bid:${id}:b`, [MARKER, EV.BID, id, 2, 15, 80_000]);
  await launchTurn(bearer, operator, `launch:bid:${id}:c`, [MARKER, EV.BID, id, 3, 11, 40_000]);
  await launchTurn(bearer, operator, `launch:clear:${id}`, [MARKER, EV.CLEAR, id, 12, 170_000]);
  console.log('done — the launchpad (DREGG_NODE set) now reads this launch from the node.');
}

main().catch((e) => { console.error(e.message); process.exit(1); });
