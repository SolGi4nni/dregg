// launchpad.js — the launch flow, driving the REAL DreggLaunchpad contract.
// Every function here is a real on-chain call (or a real read); there is no mirror
// of the clearing mechanism — the contract computes and verifies it.

/* global ethers */
import { state } from './app.js';

// ── (a) register a launch with a DISCLOSED schedule (no hidden supply) ──
// The schedule MUST close: saleSupply + creatorAllocation == totalSupply, or the
// contract reverts (SupplyDoesNotClose). Returns { launchId, token }.
export async function register({ name, symbol, totalSupply, saleSupply, creatorAllocation,
  poolAllocation, graduationBps, creatorLockUntil, reservePriceWei, commitDuration, revealDuration }) {
  const s = [BigInt(totalSupply), BigInt(saleSupply), BigInt(creatorAllocation),
    BigInt(poolAllocation), BigInt(creatorLockUntil), BigInt(reservePriceWei), BigInt(graduationBps)];
  const tx = await state.pad.registerLaunch(name, symbol, s, commitDuration, revealDuration,
    ethers.ZeroAddress, ethers.ZeroAddress);
  const rc = await tx.wait();
  // pull the LaunchRegistered event for the id + token
  let launchId = null, token = null;
  for (const log of rc.logs) {
    try { const p = state.pad.interface.parseLog(log);
      if (p && p.name === 'LaunchRegistered') { launchId = p.args.launchId.toString(); token = p.args.token; } }
    catch (_e) {}
  }
  return { launchId, token, txHash: rc.hash, schedule: {
    totalSupply: String(totalSupply), saleSupply: String(saleSupply),
    creatorAllocation: String(creatorAllocation), poolAllocation: String(poolAllocation),
    graduationBps: String(graduationBps), creatorLockUntil: String(creatorLockUntil),
    reservePrice: String(reservePriceWei) } };
}

// ── (b) sealed commit ──
// The seal is computed by the ON-CHAIN `sealOf` view — the exact preimage encoding
// the contract will re-check in revealBid (no JS re-derivation, no drift). The salt
// is generated + kept locally; losing it means you cannot reveal (fail-closed UX).
export function freshSalt() { return ethers.hexlify(ethers.randomBytes(32)); }

export async function seal(priceWei, qty, salt, bidder) {
  return state.pad.sealOf(BigInt(priceWei), BigInt(qty), salt, bidder);
}

export async function commit({ launchId, priceWei, qty, salt }) {
  const sealedHash = await seal(priceWei, qty, salt, state.account);
  const deposit = BigInt(priceWei) * BigInt(qty); // escrow the max payment
  const tx = await state.pad.commitBid(launchId, sealedHash, '0x', { value: deposit });
  const rc = await tx.wait();
  return { sealedHash, deposit: deposit.toString(), txHash: rc.hash };
}

// ── (b) reveal ──
export async function reveal({ launchId, priceWei, qty, salt }) {
  const tx = await state.pad.revealBid(launchId, BigInt(priceWei), BigInt(qty), salt);
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── (c) build the clearing order (untrusted search the contract VERIFIES) ──
// Sort the revealed bidders descending by price; the contract re-checks this is a
// permutation (no-drop/no-insert) and non-increasing before it walks the fill.
// `bids` = the /api/launches/:id detail's bids array (revealed subset).
export function clearingOrder(bids) {
  const revealed = bids.filter((b) => b.revealed);
  // the on-chain _revealedBidders order is push-order of reveals; we return the
  // permutation of THAT array's indices, sorted by descending price.
  const idx = revealed.map((_, i) => i);
  idx.sort((a, b) => {
    const pa = BigInt(revealed[a].price), pb = BigInt(revealed[b].price);
    return pb > pa ? 1 : pb < pa ? -1 : 0;
  });
  return { order: idx, revealed };
}

export async function finalize({ launchId, order }) {
  const tx = await state.pad.finalizeClearing(launchId, order.map((i) => BigInt(i)), '0x');
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── (d) settle a bidder (permissionless; every winner pays the uniform price) ──
export async function settle({ launchId, bidder }) {
  const tx = await state.pad.settleBid(launchId, bidder);
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── (e) graduation — seed the provably-solvent pool from the cleared raise ──
// The seed is the DISCLOSED fraction the contract itself computes (graduationSeed);
// we pass those exact amounts, and the contract reverts a mismatch. No JS-derived
// seeding — the numbers come from the chain.
export async function graduate({ launchId }) {
  const [quoteSeed, tokenSeed] = await state.pad.graduationSeed(launchId);
  const tx = await state.pad.graduate(launchId, quoteSeed, tokenSeed);
  const rc = await tx.wait();
  let pool = null;
  for (const log of rc.logs) {
    try { const p = state.pad.interface.parseLog(log);
      if (p && p.name === 'Graduated') pool = p.args.pool; } catch (_e) {}
  }
  return { pool, quoteSeed: quoteSeed.toString(), tokenSeed: tokenSeed.toString(), txHash: rc.hash };
}

// A read/write handle to the graduated DreggSolventPool (the liquid market).
export function poolContract(poolAddr) {
  return new ethers.Contract(poolAddr, state.cfg.poolAbi, state.signer || state.provider);
}

// Buy tokens with ETH against the never-insolvent pool. `slippageBps` sets a
// min-out floor off the on-chain quote (a trade that would drain the pool below
// its reserve floor reverts on-chain — PoolFloorBreached).
export async function poolBuy({ poolAddr, quoteWei, slippageBps = 100 }) {
  const pool = poolContract(poolAddr);
  const quoted = await pool.quoteBuy(BigInt(quoteWei));
  const minOut = (quoted * BigInt(10000 - slippageBps)) / 10000n;
  const tx = await pool.buy(minOut, { value: BigInt(quoteWei) });
  const rc = await tx.wait();
  return { txHash: rc.hash, quotedOut: quoted.toString() };
}

// Sell tokens for ETH (approves the pool first).
export async function poolSell({ poolAddr, tokenBase, tokenAddr, minQuoteWei = 0 }) {
  const pool = poolContract(poolAddr);
  const tokenAbi = ['function approve(address spender, uint256 value) returns (bool)'];
  const token = new ethers.Contract(tokenAddr, tokenAbi, state.signer);
  await (await token.approve(poolAddr, BigInt(tokenBase))).wait();
  const tx = await pool.sell(BigInt(tokenBase), BigInt(minQuoteWei));
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── read helpers over the backend API ──
export async function fetchLaunches() { return (await (await fetch('/api/launches')).json()).launches; }
export async function fetchLaunch(id) { const r = await fetch('/api/launches/' + id); return r.ok ? r.json() : null; }
export async function submitDisclosure(id, schedule, meta) {
  const r = await fetch(`/api/launches/${id}/disclose`, { method: 'POST',
    headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ schedule, meta }) });
  return r.json();
}
