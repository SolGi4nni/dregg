// e2e.mjs — the GATE driver. Drives the REAL DreggLaunchpad on a local anvil
// through the full fair-launch lifecycle (register → sealed commit → reveal →
// uniform-price clear → settle), asserts the on-chain outcome, and confirms the
// BACKEND indexed it (disclosure verified, clearing, holders, bids) over REST.
//
//   RPC=http://127.0.0.1:8545 ADDRESS=0x… SERVER=http://localhost:8785 node gate/e2e.mjs
//
// No faked launch: every number is produced by the deployed contract. Time is
// advanced deterministically with anvil's evm_increaseTime/evm_mine.

import { ethers } from 'ethers';
import { LAUNCHPAD_ABI, TOKEN_ABI, POOL_ABI } from '../shared/abi.mjs';

const RPC = process.env.RPC || 'http://127.0.0.1:8545';
const ADDRESS = process.env.ADDRESS;
const SERVER = process.env.SERVER || 'http://localhost:8785';
const G = 10n ** 9n; // gwei

const KEYS = [
  '0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80', // creator
  '0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d', // alice
  '0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a', // bob
  '0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6', // carol
  '0x47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a', // dave
];

const provider = new ethers.JsonRpcProvider(RPC);
// NonceManager serializes nonce assignment locally (avoids a getTransactionCount
// race when one account sends several txs back-to-back).
const wallets = KEYS.map((k) => new ethers.NonceManager(new ethers.Wallet(k, provider)));
const [creator, alice, bob, carol, dave] = wallets;
const [creatorA, aliceA, bobA, carolA, daveA] = await Promise.all(wallets.map((w) => w.getAddress()));
const pad = (w) => new ethers.Contract(ADDRESS, LAUNCHPAD_ABI, w);

let pass = 0, fail = 0;
const ok = (c, m) => { if (c) { pass++; console.log('  \x1b[32mPASS\x1b[0m', m); } else { fail++; console.log('  \x1b[31mFAIL\x1b[0m', m); } };
const warp = async (s) => { await provider.send('evm_increaseTime', [s]); await provider.send('evm_mine', []); };
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const spotFmt = (w) => (Number(BigInt(w || 0)) / 1e9).toFixed(3) + ' gwei/token';

async function post(path, body) {
  const r = await fetch(SERVER + path, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) });
  return { status: r.status, body: await r.json() };
}
async function get(path) { const r = await fetch(SERVER + path); return { status: r.status, body: r.ok ? await r.json() : null }; }

async function main() {
  if (!ADDRESS) { console.error('ADDRESS env required'); process.exit(2); }
  console.log(`\n=== dregg launchpad GATE — real contract @ ${ADDRESS} on ${RPC} ===\n`);

  // ── (a) register a disclosed launch ──
  const now = (await provider.getBlock('latest')).timestamp;
  const schedule = { totalSupply: 1200, saleSupply: 1000, creatorAllocation: 100,
    poolAllocation: 100, graduationBps: 5000,
    creatorLockUntil: now + 30 * 86400, reservePrice: (1n * G).toString() };
  const s = [1200n, 1000n, 100n, 100n, BigInt(schedule.creatorLockUntil), 1n * G, 5000n];
  console.log('(a) registerLaunch — disclosed schedule (1000 sale + 100 creator + 100 pool = 1200)');
  const txR = await pad(creator).registerLaunch('AuroraGate', 'AURG', s, 100, 100, ethers.ZeroAddress, ethers.ZeroAddress);
  const rcR = await txR.wait();
  let launchId, token;
  for (const log of rcR.logs) { try { const p = pad(creator).interface.parseLog(log);
    if (p?.name === 'LaunchRegistered') { launchId = p.args.launchId.toString(); token = p.args.token; } } catch (_e) {} }
  ok(!!launchId, `launch registered — id ${launchId}, token ${token?.slice(0,10)}…`);

  // supply must close on-chain
  ok(await pad(creator).checkSchedule(launchId, s), 'checkSchedule verifies the disclosed schedule (no hidden supply)');

  // reject a hidden-supply schedule (sale+creator != total)
  let reverted = false;
  try { await pad(creator).registerLaunch.staticCall('Bad', 'BAD', [1000n, 900n, 200n, 100n, 0n, 1n * G, 5000n], 10, 10, ethers.ZeroAddress, ethers.ZeroAddress); }
  catch (_e) { reverted = true; }
  ok(reverted, 'a supply that does not close (900+200+100≠1000) reverts — hidden supply unconstructable');

  // ── backend: submit + verify the disclosure ──
  const disc = await post(`/api/launches/${launchId}/disclose`, { schedule,
    meta: { name: 'AuroraGate', symbol: 'AURG', description: 'gate launch', creator: creatorA } });
  ok(disc.status === 200 && disc.body.verified, 'backend verified the disclosed schedule vs the on-chain commitment');

  // ── (b) sealed commits — 5,4,3,2 gwei/token, 400 each ──
  console.log('(b) sealed commit → reveal');
  const bids = [
    { w: alice, a: aliceA, price: 5n * G, qty: 400n, salt: ethers.id('a') },
    { w: bob,   a: bobA,   price: 4n * G, qty: 400n, salt: ethers.id('b') },
    { w: carol, a: carolA, price: 3n * G, qty: 400n, salt: ethers.id('c') },
    { w: dave,  a: daveA,  price: 2n * G, qty: 400n, salt: ethers.id('d') },
  ];
  for (const b of bids) {
    const seal = await pad(b.w).sealOf(b.price, b.qty, b.salt, b.a);
    await (await pad(b.w).commitBid(launchId, seal, '0x', { value: b.price * b.qty })).wait();
  }
  ok(true, 'four sealed bids committed (no bid observable during commit)');

  // a reveal DURING commit must fail (no peek)
  let peekFailed = false;
  try { await pad(alice).revealBid.staticCall(launchId, bids[0].price, bids[0].qty, bids[0].salt); }
  catch (_e) { peekFailed = true; }
  ok(peekFailed, 'reveal during commit window rejected (NotRevealPhase — no peek)');

  // advance into the reveal window
  await warp(101);
  for (const b of bids) await (await pad(b.w).revealBid(launchId, b.price, b.qty, b.salt)).wait();
  ok(Number(await pad(creator).revealedCount(launchId)) === 4, 'four reveals bound to their commitments');

  // a mismatched reveal is impossible — check the last one can't be re-revealed with a different bid
  let switchFailed = false;
  try { await pad(alice).revealBid.staticCall(launchId, 9n * G, 400n, bids[0].salt); }
  catch (_e) { switchFailed = true; }
  ok(switchFailed, 'late-switch to a different bid rejected (AlreadyRevealed/BidMismatch)');

  // ── (c) uniform-price clearing ──
  console.log('(c) uniform-price clearing');
  await warp(101); // past the reveal window
  const order = [0, 1, 2, 3].map(BigInt); // revealed push-order is already descending by price
  await (await pad(creator).finalizeClearing(launchId, order, '0x')).wait();
  const clearingPrice = await pad(creator).clearingPriceOf(launchId);
  const soldQty = await pad(creator).soldQtyOf(launchId);
  ok(clearingPrice === 3n * G, `uniform clearing price = 3 gwei (got ${ethers.formatUnits(clearingPrice, 'gwei')})`);
  ok(soldQty === 1000n, `full saleSupply cleared — sold ${soldQty}`);

  // a bad permutation (drop) reverts
  let permFailed = false;
  try { await pad(creator).finalizeClearing.staticCall(launchId, [0n, 1n, 2n], '0x'); } catch (_e) { permFailed = true; }
  ok(permFailed, 'a clearing order that drops a bid reverts (no-drop / no-insert)');

  // ── (d) settlement — every winner pays the SAME price ──
  console.log('(d) non-custodial settlement');
  for (const b of bids) await (await pad(creator).settleBid(launchId, b.a)).wait();
  const tok = new ethers.Contract(token, TOKEN_ABI, provider);
  const U = 10n ** 18n;
  ok(await tok.balanceOf(aliceA) === 400n * U, 'alice full fill (400)');
  ok(await tok.balanceOf(carolA) === 200n * U, 'carol marginal fill (200)');
  ok(await tok.balanceOf(daveA) === 0n, 'dave below-clearing, no fill (0)');

  // ── (e) graduation into the provably-solvent liquid market ──
  console.log('(e) graduation → provably-solvent pool + live trading');
  const [qSeed, tSeed] = await pad(creator).graduationSeed(launchId);
  ok(qSeed === (3n * G * 1000n) / 2n, `disclosed quote seed = 50% of proceeds (${ethers.formatEther(qSeed)} ETH)`);
  // a wrong/hidden seeding reverts (the disclosed fraction is enforced)
  let seedFailed = false;
  try { await pad(creator).graduate.staticCall(launchId, qSeed - 1n, tSeed); } catch (_e) { seedFailed = true; }
  ok(seedFailed, 'a wrong/hidden graduation seeding reverts (GraduationSeedMismatch)');
  await (await pad(creator).graduate(launchId, qSeed, tSeed)).wait();
  ok(await pad(creator).isGraduated(launchId), 'launch graduated into a solvent pool');
  const poolAddr = await pad(creator).poolOf(launchId);
  const pool = new ethers.Contract(poolAddr, POOL_ABI, provider);
  const [rq, rt] = await pool.reserves();
  ok(rq === qSeed && rt === tSeed, 'pool seeded with exactly the disclosed reserves');
  // a live buy clears against the never-insolvent pool
  await (await pool.connect(alice).buy(0n, { value: 100n * G })).wait();
  ok(true, 'a buy clears against the solvent pool');
  // a trade that would drain the pool below its floor REVERTS (the solvency tooth)
  let drainFailed = false;
  try { await pool.connect(alice).buy.staticCall(0n, { value: 20000n * G }); } catch (_e) { drainFailed = true; }
  ok(drainFailed, 'a drain below the reserve floor reverts (PoolFloorBreached ↔ pool_solvent_forever)');

  await (await pad(creator).withdrawProceeds(launchId)).wait();
  ok(true, 'creator withdrew the remaining proceeds (non-custodial, post-graduation)');

  // creator alloc still locked (dev-dump guard)
  let lockFailed = false;
  try { await pad(creator).claimCreatorAllocation.staticCall(launchId); } catch (_e) { lockFailed = true; }
  ok(lockFailed, 'creator allocation still vesting-locked (dev-dump guard)');

  // ── backend REST reflects the real launch ──
  console.log('(backend) REST API reflects the on-chain launch');
  let d = null;
  for (let i = 0; i < 20; i++) { // give the indexer's block-poller a moment
    d = (await get(`/api/launches/${launchId}`)).body;
    if (d && d.graduated && d.poolState && (d.holders?.length || 0) >= 3) break;
    await sleep(500);
  }
  ok(d && d.disclosure?.verified, 'GET /api/launches/:id — disclosure verified');
  ok(d && d.clearingPrice === (3n * G).toString(), `GET /api/launches/:id — clearing price ${d && ethers.formatUnits(d.clearingPrice,'gwei')} gwei`);
  ok(d && (d.holders?.length || 0) >= 3, `GET /api/launches/:id — holder distribution has ${d?.holders?.length} holders`);
  ok(d && (d.bids?.length || 0) === 4, `GET /api/launches/:id — revealed book has ${d?.bids?.length} bids`);
  ok(d && d.graduated === true, 'GET /api/launches/:id — backend indexed the graduation');
  ok(d && d.poolState && d.poolState.reserveToken !== '0' && d.poolState.spotWeiPerToken !== '0',
     `GET /api/launches/:id — live pool reserves + spot ${d?.poolState && spotFmt(d.poolState.spotWeiPerToken)} indexed`);
  const list = (await get('/api/launches')).body;
  ok(list && list.launches.some((x) => x.id === launchId && typeof x.rank === 'number'),
     'GET /api/launches — launch present with a replayable rank score');

  console.log(`\n=== GATE ${fail === 0 ? '\x1b[32mPASS\x1b[0m' : '\x1b[31mFAIL\x1b[0m'} — ${pass} passed, ${fail} failed ===\n`);
  process.exit(fail === 0 ? 0 : 1);
}
main().catch((e) => { console.error('gate error:', e); process.exit(2); });
