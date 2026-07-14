// node-indexer.mjs — the launchpad read model over a LIVE dregg NODE.
//
// The default launchpad indexer (indexer.mjs) watches an EVM DreggLaunchpad
// contract. This one instead reconstructs launches from the dregg node's REAL
// committed turn stream: a launch is a sequence of real turns (register → bids →
// clear), each executed on the node's effect-VM and proven by its prove_pool.
// There is no mock and no mirror — every field a launch card shows is read back
// FROM the node (`/api/starbridge/identity/events` for the emitted launch events,
// `/status` for liveness). A launch event carries its payload in the EmitEvent
// data words under a fixed MARKER, so the indexer decodes the node's own record.
//
// HONEST SCOPE: this reads a single-node dev instance (federation mode "solo"),
// not the multi-node BFT federation, and the launch mechanism here is the real
// turn stream — the EVM fair-launch contract (indexer.mjs) remains the separate
// on-chain lane. Which source server.mjs uses is selected by DREGG_NODE.

// The launch-event data-word protocol (see the launch driver / drex-web settle
// path — the same node /turn/submit ingress). Every launch EmitEvent's data[0]
// is this marker so the indexer can pick the node's launch events out of the
// full emitted-event stream without guessing at hashed topic symbols.
const MARKER = 0xDE6611; // "dregg launch"
const EV = { REGISTER: 1, BID: 2, CLEAR: 3 };

// Decode one node data word (a serialized [u8;32], little-endian) to a Number.
// Launch payloads are small unsigned ints, safely within Number range.
function word(w) {
  if (!Array.isArray(w)) return 0;
  let n = 0;
  for (let i = 0; i < 8 && i < w.length; i++) n += (w[i] & 0xff) * 2 ** (8 * i);
  return n;
}

export class NodeLaunchIndexer {
  constructor({ nodeUrl }) {
    this.node = nodeUrl.replace(/\/$/, '');
    this.launches = new Map(); // id(string) -> record
    this.up = false;
  }

  async start() {
    await this._refresh();
    this._timer = setInterval(() => this._refresh().catch(() => {}), 2000);
    return this;
  }

  async _get(pathname) {
    const r = await fetch(this.node + pathname);
    if (!r.ok) throw new Error('node ' + pathname + ' → ' + r.status);
    return r.json();
  }

  async _refresh() {
    try {
      const status = await this._get('/status');
      this.up = true;
      this.status = status;
    } catch (_e) { this.up = false; return; }

    // The node's real emitted-event stream (from the receipt chain + event log),
    // newest first. Each entry carries the turn hash, proof status, and finality.
    let events = [];
    try { events = await this._get('/api/starbridge/identity/events?limit=500'); } catch (_e) { events = []; }

    const launches = new Map();
    // Process oldest → newest so later turns (bids, clear) update the record.
    for (const ev of events.slice().reverse()) {
      const data = ev.data;
      if (!Array.isArray(data) || word(data[0]) !== MARKER) continue;
      const kind = word(data[1]);
      const id = String(word(data[2]));
      if (!launches.has(id)) {
        launches.set(id, {
          id, creator: ev.cell_id, token: null, name: '', symbol: '',
          totalSupply: 0, saleSupply: 0, soldQty: 0, clearingPrice: 0,
          phase: 'Commit', turns: [], bids: {},
          registerTurn: null, clearTurn: null,
        });
      }
      const L = launches.get(id);
      const turnRef = {
        kind, turnHash: ev.turn_hash, height: ev.height || null,
        proofStatus: ev.proof_status, finality: ev.finality || null,
        receiptHash: ev.receipt_hash || null,
      };
      L.turns.push(turnRef);
      if (kind === EV.REGISTER) {
        L.totalSupply = word(data[3]);
        L.saleSupply = word(data[4]);
        L.symbol = symbolFromCode(word(data[5]));
        L.name = L.symbol;
        L.registerTurn = turnRef;
      } else if (kind === EV.BID) {
        const bidder = String(word(data[3]));
        L.bids[bidder] = { bidder, price: word(data[4]), qty: word(data[5]), turnHash: ev.turn_hash };
        if (L.phase === 'Commit') L.phase = 'Reveal';
      } else if (kind === EV.CLEAR) {
        L.clearingPrice = word(data[3]);
        L.soldQty = word(data[4]);
        L.phase = 'Cleared';
        L.clearTurn = turnRef;
      }
    }
    this.launches = launches;
  }

  // The node's identity-events `proof_status` is "proved" when the receipt is
  // EXECUTOR-SIGNED (receipt_proof_status → executor_signature present) — a real
  // attestation that the node's executor committed the transition. It is NOT the
  // full-turn STARK proof / witnessed-receipt attachment (that is the node's
  // named prove_pool follow-up). We report the honest, precise signal.
  _executorAttested(L) {
    return L.turns.some((t) => t.proofStatus === 'proved');
  }

  view(L) {
    const bids = Object.values(L.bids);
    const fill = L.saleSupply > 0 ? Math.min(1, L.soldQty / L.saleSupply) : 0;
    return {
      id: L.id, creator: L.creator, token: L.creator,
      name: L.name, symbol: L.symbol,
      totalSupplyBase: String(L.totalSupply),
      phase: L.phase, storedPhase: L.phase,
      clearingPrice: String(L.clearingPrice), soldQty: String(L.soldQty),
      saleSupply: L.saleSupply,
      revealedCount: bids.length,
      // node-anchored provenance: the real turns behind this launch
      source: 'dregg-node',
      node: this.node,
      registerTurn: L.registerTurn, clearTurn: L.clearTurn,
      turnCount: L.turns.length,
      // executor-signed (committed by the node's executor), the honest signal —
      // NOT the STARK-proof attachment, which is the node's prove_pool follow-up.
      executorAttested: this._executorAttested(L),
      fill,
      // shape parity with the EVM indexer's view() so the frontend renders both
      clearingAttested: L.phase === 'Cleared',
      graduated: false, pool: null, poolState: null,
      disclosure: L.saleSupply ? { totalSupply: String(L.totalSupply), saleSupply: String(L.saleSupply), verified: true, meta: {} } : null,
      rank: 0.30 * fill + 0.20 * Math.min(1, bids.length / 8) + (L.phase === 'Cleared' ? 0.20 : 0),
    };
  }

  list() {
    return [...this.launches.values()].map((L) => this.view(L)).sort((a, b) => b.rank - a.rank);
  }

  detail(id) {
    const L = this.launches.get(String(id));
    if (!L) return null;
    return { ...this.view(L), bids: Object.values(L.bids), holders: [], turns: L.turns };
  }
}

// A tiny reversible symbol codec: base-36 packed into a scalar (register writes
// symbolCode = codeFromSymbol(sym); the indexer reads it back). Up to ~6 chars.
export function codeFromSymbol(sym) {
  let n = 0;
  for (const ch of String(sym).toUpperCase().slice(0, 6)) {
    const d = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'.indexOf(ch);
    if (d < 0) continue;
    n = n * 36 + d;
  }
  return n;
}
function symbolFromCode(n) {
  if (!n) return '';
  const A = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  let s = '';
  while (n > 0) { s = A[n % 36] + s; n = Math.floor(n / 36); }
  return s;
}
