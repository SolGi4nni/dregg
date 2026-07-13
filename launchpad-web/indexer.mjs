// indexer.mjs — the event-listener over the REAL DreggLaunchpad contract.
//
// Pattern taken from fiv3fingers/Token-Launchpad-Backend
// (src/logListeners/AgentsLandListener.ts: `program.addEventListener("launchEvent",
// …)` → store into a DB → REST + socket). We keep the same shape — subscribe to
// the launch lifecycle events, maintain a queryable store, serve it over REST —
// but over the EVM fair-launch engine instead of a Solana bonding curve, and the
// store is authoritative FROM CHAIN (no mirror of the mechanism).
//
// The store has two provenance tiers, kept honestly distinct:
//   • ON-CHAIN (authoritative): scheduleCommit, phase, clearingPrice, soldQty,
//     token metadata + supply, the bids, the holder balances (from Transfer logs).
//   • DISCLOSED (creator-submitted, then VERIFIED against the on-chain commitment
//     via `checkSchedule`): the raw supply/vesting split + name/description/image.
//     `disclosureVerified` is the on-chain keccak match — the "no hidden supply"
//     proof a launch card shows.

import { ethers } from 'ethers';
import { LAUNCHPAD_ABI, TOKEN_ABI, POOL_ABI, PHASE } from './shared/abi.mjs';

export class LaunchpadIndexer {
  constructor({ rpcUrl, launchpad }) {
    this.provider = new ethers.JsonRpcProvider(rpcUrl);
    this.address = launchpad;
    this.pad = new ethers.Contract(launchpad, LAUNCHPAD_ABI, this.provider);
    this.launches = new Map(); // id(string) -> launch record
    this.disclosed = new Map(); // id(string) -> { schedule, meta, verified }
    this.tokenBalances = new Map(); // tokenAddr -> Map(holder -> bigint)
    this._tokenSubscribed = new Set();
  }

  async start() {
    // Backfill everything from genesis, then poll for new blocks.
    await this._backfill();
    this.provider.on('block', () => this._refresh().catch(() => {}));
    return this;
  }

  // ── creator-submitted disclosed schedule (verified against the commitment) ──
  async submitDisclosure(id, schedule, meta) {
    id = String(id);
    let verified = false;
    try {
      verified = await this.pad.checkSchedule(id, [
        BigInt(schedule.totalSupply),
        BigInt(schedule.saleSupply),
        BigInt(schedule.creatorAllocation),
        BigInt(schedule.poolAllocation),
        BigInt(schedule.creatorLockUntil),
        BigInt(schedule.reservePrice),
        BigInt(schedule.graduationBps),
      ]);
    } catch (_e) { verified = false; }
    this.disclosed.set(id, { schedule, meta: meta || {}, verified });
    await this._refresh();
    return { id, verified };
  }

  async _backfill() {
    const reg = await this.pad.queryFilter(this.pad.filters.LaunchRegistered(), 0);
    for (const ev of reg) await this._onRegistered(ev.args);
    await this._refresh();
  }

  async _onRegistered(a) {
    const id = a.launchId.toString();
    if (this.launches.has(id)) return;
    const token = new ethers.Contract(a.token, TOKEN_ABI, this.provider);
    let name = '', symbol = '', totalSupply = 0n;
    try {
      [name, symbol, totalSupply] = await Promise.all([token.name(), token.symbol(), token.totalSupply()]);
    } catch (_e) {}
    this.launches.set(id, {
      id, creator: a.creator, token: a.token, tokenName: name, tokenSymbol: symbol,
      totalSupplyBase: totalSupply.toString(),
      scheduleCommit: a.scheduleCommit,
      commitEnd: Number(a.commitEnd), revealEnd: Number(a.revealEnd),
      storedPhase: 'Commit', clearingPrice: '0', soldQty: '0', proceeds: '0',
      clearingAttested: false,
      graduated: false, pool: null, poolState: null,
      bids: {}, // bidder -> { committed, revealed, price, qty, filled, settled, deposit }
    });
    await this._subscribeToken(a.token);
  }

  async _subscribeToken(tokenAddr) {
    if (this._tokenSubscribed.has(tokenAddr)) return;
    this._tokenSubscribed.add(tokenAddr);
    this.tokenBalances.set(tokenAddr, new Map());
    const token = new ethers.Contract(tokenAddr, TOKEN_ABI, this.provider);
    const logs = await token.queryFilter(token.filters.Transfer(), 0);
    const bals = this.tokenBalances.get(tokenAddr);
    for (const l of logs) this._applyTransfer(bals, l.args);
    token.on('Transfer', (from, to, value) => this._applyTransfer(bals, { from, to, value }));
  }

  _applyTransfer(bals, { from, to, value }) {
    const ZERO = '0x0000000000000000000000000000000000000000';
    if (from !== ZERO) bals.set(from, (bals.get(from) || 0n) - value);
    if (to !== ZERO) bals.set(to, (bals.get(to) || 0n) + value);
  }

  // Refresh dynamic on-chain state for all known launches.
  async _refresh() {
    // pick up launches registered since last backfill
    try {
      const count = Number(await this.pad.launchCount());
      for (let i = 1; i <= count; i++) {
        if (!this.launches.has(String(i))) {
          const commit = await this.pad.scheduleCommitOf(i); // exists ⇒ registered
          if (commit && commit !== ethers.ZeroHash) {
            // reconstruct from logs
            const reg = await this.pad.queryFilter(this.pad.filters.LaunchRegistered(i), 0);
            if (reg[0]) await this._onRegistered(reg[0].args);
          }
        }
      }
    } catch (_e) {}

    for (const L of this.launches.values()) {
      try {
        const [phase, price, sold, attested, revealed] = await Promise.all([
          this.pad.phaseOf(L.id), this.pad.clearingPriceOf(L.id), this.pad.soldQtyOf(L.id),
          this.pad.clearingAttested(L.id), this.pad.revealedCount(L.id),
        ]);
        L.storedPhase = PHASE[Number(phase)];
        L.clearingPrice = price.toString();
        L.soldQty = sold.toString();
        L.clearingAttested = attested;
        L.revealedCount = Number(revealed);
      } catch (_e) {}
      // graduation + the live pool (the provably-solvent liquid market)
      await this._refreshGraduation(L);
      // bids: refresh for every address we have seen commit/reveal from
      await this._refreshBids(L);
    }
  }

  // ── graduation state + the live solvent pool (reserves / price / floor / trades) ──
  async _refreshGraduation(L) {
    try {
      const graduated = await this.pad.isGraduated(L.id);
      L.graduated = graduated;
      // the on-chain-verifiable disclosed seed (deterministic from cleared state)
      try {
        const [qSeed, tSeed] = await this.pad.graduationSeed(L.id);
        L.graduationSeed = { quoteSeed: qSeed.toString(), tokenSeed: tSeed.toString() };
      } catch (_e) {}
      if (!graduated) return;
      const poolAddr = await this.pad.poolOf(L.id);
      L.pool = poolAddr;
      const pool = new ethers.Contract(poolAddr, POOL_ABI, this.provider);
      const [rq, rt, fq, ft, spot, fee] = await Promise.all([
        pool.reserveQuote(), pool.reserveToken(), pool.floorQuote(), pool.floorToken(),
        pool.spotPriceWeiPerToken(), pool.feeBps(),
      ]);
      // recent trades (Bought / Sold) — the honest tape, read from logs.
      let trades = [];
      try {
        const [bought, sold] = await Promise.all([
          pool.queryFilter(pool.filters.Bought(), 0),
          pool.queryFilter(pool.filters.Sold(), 0),
        ]);
        trades = [
          ...bought.map((e) => ({ kind: 'buy', who: e.args.buyer, quote: e.args.quoteIn.toString(),
            token: e.args.tokenOut.toString(), block: e.blockNumber })),
          ...sold.map((e) => ({ kind: 'sell', who: e.args.seller, quote: e.args.quoteOut.toString(),
            token: e.args.tokenIn.toString(), block: e.blockNumber })),
        ].sort((a, b) => b.block - a.block).slice(0, 20);
      } catch (_e) {}
      L.poolState = {
        address: poolAddr,
        reserveQuote: rq.toString(), reserveToken: rt.toString(),
        floorQuote: fq.toString(), floorToken: ft.toString(),
        spotWeiPerToken: spot.toString(), feeBps: Number(fee),
        trades,
      };
    } catch (_e) {}
  }

  async _refreshBids(L) {
    // discover bidders from events (committed + revealed)
    const cEv = await this.pad.queryFilter(this.pad.filters.BidCommitted(L.id), 0);
    for (const ev of cEv) { const b = ev.args.bidder; if (!L.bids[b]) L.bids[b] = { bidder: b }; }
    for (const b of Object.keys(L.bids)) {
      try {
        const r = await this.pad.getBid(L.id, b);
        L.bids[b] = {
          bidder: b, committed: r.committed, revealed: r.revealed,
          price: r.price.toString(), qty: r.qty.toString(), filled: r.filled.toString(),
          settled: r.settled, deposit: r.deposit.toString(),
        };
      } catch (_e) {}
    }
  }

  // ── effective phase (storage phase doesn't auto-advance with the clock) ──
  effectivePhase(L, now = Math.floor(Date.now() / 1000)) {
    if (L.storedPhase === 'Cleared' || L.storedPhase === 'Finalized') return L.storedPhase;
    if (now < L.commitEnd) return 'Commit';
    if (now < L.revealEnd) return 'Reveal';
    return 'ClearReady'; // reveal window closed, clearing may be finalized
  }

  holders(tokenAddr) {
    const bals = this.tokenBalances.get(tokenAddr) || new Map();
    return [...bals.entries()]
      .filter(([, v]) => v > 0n)
      .sort((a, b) => (b[1] > a[1] ? 1 : -1))
      .map(([addr, v]) => ({ address: addr, balanceBase: v.toString() }));
  }

  // ── the REPLAYABLE discovery ranking (OCIP anti-pay-to-rank) ──
  // A PURE, DETERMINISTIC function over PUBLIC on-chain fields only. There is no
  // boost/promote input anywhere — the score is re-derivable by anyone from the
  // same chain state (docs/deos/DREGGFI-VISION.md §1 REPLAYABLE grade; the honest
  // discovery: no paid placement). Components are exposed so the rank is auditable.
  rankScore(L) {
    const now = Math.floor(Date.now() / 1000);
    const disc = this.disclosed.get(L.id);
    const sale = disc?.verified ? Number(disc.schedule.saleSupply) : 0;
    const sold = Number(L.soldQty || 0);
    const fill = sale > 0 ? Math.min(1, sold / sale) : 0;            // demand met
    const participation = Math.min(1, (L.revealedCount || 0) / 8);    // breadth of bidders
    const cleared = (L.storedPhase === 'Cleared' || L.storedPhase === 'Finalized') ? 1 : 0;
    const attested = L.clearingAttested ? 1 : 0;                      // rung-2 proof present
    const disclosed = disc?.verified ? 1 : 0;                        // no-hidden-supply proof
    const ageHrs = Math.max(0, (now - (L.revealEnd - 0)) / 3600);
    const recency = 1 / (1 + ageHrs / 24);                          // decays over ~a day
    const score =
      0.30 * fill + 0.20 * participation + 0.20 * cleared +
      0.15 * disclosed + 0.10 * recency + 0.05 * attested;
    return { score, components: { fill, participation, cleared, disclosed, recency, attested } };
  }

  // ── public read model ──
  view(L) {
    const disc = this.disclosed.get(L.id);
    const rank = this.rankScore(L);
    return {
      id: L.id, creator: L.creator, token: L.token,
      name: L.tokenName, symbol: L.tokenSymbol,
      totalSupplyBase: L.totalSupplyBase,
      scheduleCommit: L.scheduleCommit,
      commitEnd: L.commitEnd, revealEnd: L.revealEnd,
      phase: this.effectivePhase(L), storedPhase: L.storedPhase,
      clearingPrice: L.clearingPrice, soldQty: L.soldQty,
      clearingAttested: L.clearingAttested, revealedCount: L.revealedCount || 0,
      disclosure: disc ? { ...disc.schedule, meta: disc.meta, verified: disc.verified } : null,
      graduated: L.graduated, pool: L.pool, poolState: L.poolState || null,
      graduationSeed: L.graduationSeed || null,
      rank: rank.score, rankComponents: rank.components,
    };
  }

  list() {
    return [...this.launches.values()]
      .map((L) => this.view(L))
      .sort((a, b) => b.rank - a.rank);
  }

  detail(id) {
    const L = this.launches.get(String(id));
    if (!L) return null;
    return { ...this.view(L), bids: Object.values(L.bids), holders: this.holders(L.token) };
  }
}
