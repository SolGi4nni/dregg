import { AccountUpdate, Field, Mina, PrivateKey } from 'o1js';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  CELL,
  CELL_ROW_LANES,
  DreggCellFact,
  anchorForCellRow,
  cellCommitOfBigInt,
} from '../src/DreggCellFact.js';
import {
  ATTEST_DEPTH,
  CELL_FACT_BB_DEPTH,
  DreggAnchorStatement,
  DreggAttestedGate,
  DreggCellFactStatement,
  DreggMembershipAttestation,
  signPlaceholderAnchor,
} from '../src/DreggPoseidonAttestation.js';
import { BbDigest } from '../src/Poseidon2Merkle.js';
import { atTier, tierStop, tierStop1 } from '../src/tier.js';

// ---------------------------------------------------------------------------
// THE MINA→DREGG SEMANTIC RUNG, on a REAL dregg cell.
//
// ⚑ WHAT MAKES THE CELL REAL. `src/generated/kimchi-cellcommit-b.json` is the
// verbatim emission of `Dregg2.Circuit.Emit.KimchiCellCommit.commitOps` — the
// deployed `incrementNonce` descriptor's four GROUP-4 hash sites, with a
// satisfying witness. Its `honestCommit` is a felt LEAN computed, and its
// witness columns 76..87 plus 186 are the cell that felt commits to: balance
// 100, nonce 6, all eight fields and the cap root zero. Nothing below invents a
// cell; [1] recomputes `honestCommit` from those lanes out of circuit and reds
// if it disagrees, which is the cross-check that this file's `cellCommitOf`
// really is the Lean one.
//
// ⚑ WHAT IS SYNTHETIC, SAID PLAINLY. The MMCS tree the cell sits in, and the
// anchored Pasta root above it. dregg emits no live BabyBear-Poseidon2
// commitment over cell state today — `ANCHOR_MERKLE_DEPTH`'s own docstring says
// so — so there is no deployed tree to open against. That is a real gap and it
// is NOT this rung's: the distance it closes is "a leaf" → "a cell's named
// columns", and the distance it does not is "an anchored root" → "dregg's state
// root", which is `PLACEHOLDER_CUTOVER`'s.
// ---------------------------------------------------------------------------

const __dirname_ = dirname(fileURLToPath(import.meta.url));
const t0 = Date.now();

let failures = 0;
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;
function ok(msg: string) {
  console.log(`  ✓ ${msg}`);
}
function check(cond: boolean, good: string, bad: string) {
  if (cond) ok(good);
  else {
    failures++;
    console.log(`  ✗ ${bad}`);
  }
}

function artifact(name: string): string {
  let d = __dirname_;
  for (let i = 0; i < 8; i++) {
    try {
      readFileSync(resolve(d, 'package.json'));
      return resolve(d, `src/generated/${name}`);
    } catch {
      d = resolve(d, '..');
    }
  }
  throw new Error(`cell-fact: could not locate ${name} from the package root`);
}

// ===========================================================================
// [1] The REAL cell, and the Lean-emitted commitment it must reproduce.
// ===========================================================================

console.log('\n[1] the real dregg cell, out of the Lean emission');

const emitted = JSON.parse(readFileSync(artifact('kimchi-cellcommit-b.json'), 'utf8')) as {
  honestCommit: string;
  cols: Record<string, number>;
  siteInCols: number[][];
  witness: string[];
};

// The 13 absorbed lanes, read at the columns the emission itself names: the
// three GROUP-4 sites' inputs, then the state-record digest. Reading them from
// `siteInCols` rather than from hardcoded offsets is what keeps this honest if
// the emission's layout ever moves.
const [s0, s1, s2, s3] = emitted.siteInCols;
const rowCols = [...s0, ...s1, ...s2, s3[3]];
const row: bigint[] = rowCols.map((c) => BigInt(emitted.witness[c]));
const stateCommitCol = emitted.cols.stateCommit;

check(
  row.length === CELL_ROW_LANES,
  `read a ${CELL_ROW_LANES}-lane cell row from the emitted witness at columns [${rowCols.join(',')}]`,
  `the emitted witness gave ${row.length} lanes, not ${CELL_ROW_LANES}`,
);
console.log(
  `    cell: balance_lo=${row[CELL.balanceLo]} balance_hi=${row[CELL.balanceHi]}` +
    ` nonce=${row[CELL.nonce]} cap_root=${row[CELL.capRoot]}` +
    ` record_digest=${row[CELL.recordDigest]}`,
);

const recomputed = cellCommitOfBigInt(row);
check(
  recomputed === BigInt(emitted.honestCommit),
  `cellCommitOf(row) = ${recomputed} reproduces the LEAN-emitted honestCommit`,
  `cellCommitOf(row) = ${recomputed} != Lean honestCommit ${emitted.honestCommit}`,
);
check(
  recomputed === BigInt(emitted.witness[stateCommitCol]),
  `and it is the felt the emitted witness carries in the state_commit column (${stateCommitCol})`,
  `it disagrees with the emitted state_commit column ${stateCommitCol}`,
);

// A control that the recomputation is not a constant: one nanomina moves it.
const bumped = [...row];
bumped[CELL.balanceLo] += 1n;
check(
  cellCommitOfBigInt(bumped) !== recomputed,
  'a one-unit balance change moves the commitment (the recomputation is not constant)',
  'a one-unit balance change left the commitment unchanged',
);

// ===========================================================================
// [2] The opening material. Deterministic, so the run is reproducible.
// ===========================================================================

console.log('\n[2] the opening material');

/** A deterministic BabyBear digest, so the transcript reproduces exactly. */
function seedDigest(tag: number): bigint[] {
  return Array.from({ length: 8 }, (_, j) => BigInt(1 + tag * 1_000_003 + j * 7919) % (1n << 31n));
}

const bbSiblings: bigint[][] = Array.from({ length: CELL_FACT_BB_DEPTH }, (_, h) => seedDigest(h));
const bbIsRight: boolean[] = Array.from({ length: CELL_FACT_BB_DEPTH }, (_, h) => h % 2 === 1);
const pastaSiblings: bigint[] = Array.from({ length: ATTEST_DEPTH }, (_, i) => BigInt(1000 + i));

const honest = anchorForCellRow(row, bbSiblings, bbIsRight, pastaSiblings);
console.log(`    bb leaf digest lane0 = ${honest.leaf[0]}`);
console.log(`    bb root       lane0 = ${honest.bbRoot[0]}`);
console.log(`    anchored Pasta root = ${honest.anchored.toBigInt()}`);

// The DISHONEST prover's material: an internally consistent tree over a cell
// claiming one more nanomina. It proves fine — against a DIFFERENT root, which
// is exactly the point of [5].
const forged = anchorForCellRow(bumped, bbSiblings, bbIsRight, pastaSiblings);
check(
  forged.anchored.toBigInt() !== honest.anchored.toBigInt(),
  'a cell with one more nanomina anchors to a DIFFERENT root',
  'the forged cell anchored to the same root (the fold is not binding)',
);

if (!atTier(1)) {
  tierStop(
    'cell-fact',
    4,
    secs(t0),
    'compiling DreggCellFactStatement; proving the honest cell fact; the four in-circuit ' +
      'tamper refusals; the zkApp actOnCellFact leg',
  );
  process.exit(failures === 0 ? 0 : 1);
}

// ===========================================================================
// [3] The statement compiles, and the honest cell PROVES.
// ===========================================================================

console.log('\n[3] the cell-fact statement');

const analysis = await DreggCellFactStatement.analyzeMethods();
console.log(`    proveCellFact: ${analysis.proveCellFact.rows} rows`);

let t = Date.now();
await DreggCellFactStatement.compile();
ok(`compiled DreggCellFactStatement in ${secs(t)}`);

const toDigests = (ds: bigint[][]) => ds.map((d) => BbDigest.from(d));
const toBools = (bs: boolean[]) => bs.map((b) => Field(b ? 1 : 0).equals(Field(1)));

t = Date.now();
const { proof: honestProof } = await DreggCellFactStatement.proveCellFact(
  honest.anchored,
  row.map((x) => Field(x)),
  toDigests(bbSiblings),
  toBools(bbIsRight),
  pastaSiblings.map((x) => Field(x)),
);
ok(`proved the honest cell fact in ${secs(t)}`);

const fact = honestProof.publicOutput as DreggCellFact;
check(
  fact.balanceLo.toBigInt() === row[CELL.balanceLo],
  `the published fact carries balance_lo = ${fact.balanceLo.toBigInt()} — dregg's OWN column, ` +
    'not a leaf hash',
  `the published balance_lo ${fact.balanceLo.toBigInt()} is not the cell's ${row[CELL.balanceLo]}`,
);
check(
  fact.nonce.toBigInt() === row[CELL.nonce] &&
    fact.balanceHi.toBigInt() === row[CELL.balanceHi] &&
    fact.capRoot.toBigInt() === row[CELL.capRoot],
  `and nonce = ${fact.nonce.toBigInt()}, balance_hi = ${fact.balanceHi.toBigInt()}, ` +
    `cap_root = ${fact.capRoot.toBigInt()}`,
  'the published nonce / balance_hi / cap_root do not match the cell',
);
check(
  fact.stateCommit.toBigInt() === recomputed,
  `and stateCommit = ${fact.stateCommit.toBigInt()}, the LEAN-emitted commitment, recomputed ` +
    'IN CIRCUIT from the same row',
  `the in-circuit stateCommit ${fact.stateCommit.toBigInt()} != the Lean one ${recomputed}`,
);

let honestVerifies = true;
try {
  await honestProof.verify();
} catch {
  honestVerifies = false;
}
check(honestVerifies, 'the honest proof verifies', 'the honest proof did not verify');

// ===========================================================================
// [4] TAMPERS. Each must be REFUSED, and refused for a REASON we can name.
// ===========================================================================

console.log('\n[4] tampers');

/** Run a prove attempt and report whether it was refused, with the message. */
async function refused(
  what: string,
  build: () => Promise<unknown>,
): Promise<void> {
  let accepted = false;
  let msg = '';
  try {
    await build();
    accepted = true;
  } catch (e) {
    msg = (e as Error).message.split('\n')[0].slice(0, 140);
  }
  check(!accepted, `REFUSED: ${what} — ${msg}`, `ACCEPTED: ${what} (UNSOUND)`);
}

// (a) A LIE ABOUT THE BALANCE, with the honest opening. The prover keeps every
//     sibling and the anchored root and swaps one nanomina into the row. The
//     leaf digest moves, so the fold no longer reaches the root.
await refused('one more nanomina, honest opening, honest anchored root', () =>
  DreggCellFactStatement.proveCellFact(
    honest.anchored,
    bumped.map((x) => Field(x)),
    toDigests(bbSiblings),
    toBools(bbIsRight),
    pastaSiblings.map((x) => Field(x)),
  ),
);

// (b) A TAMPERED SIBLING with the honest row.
const badSibs = bbSiblings.map((d, h) => (h === 0 ? [d[0] + 1n, ...d.slice(1)] : d));
await refused('the honest cell under a tampered MMCS sibling', () =>
  DreggCellFactStatement.proveCellFact(
    honest.anchored,
    row.map((x) => Field(x)),
    toDigests(badSibs),
    toBools(bbIsRight),
    pastaSiblings.map((x) => Field(x)),
  ),
);

// (c) A TRANSPOSED MMCS DIRECTION.
await refused('the honest cell with one MMCS direction flipped', () =>
  DreggCellFactStatement.proveCellFact(
    honest.anchored,
    row.map((x) => Field(x)),
    toDigests(bbSiblings),
    toBools(bbIsRight.map((b, h) => (h === 1 ? !b : b))),
    pastaSiblings.map((x) => Field(x)),
  ),
);

// (d) AN OUT-OF-RANGE LANE. `p + 100` is the same BabyBear element as `100`, so
//     without the range check a prover could present a second pre-image of the
//     same balance. The circuit bounds every witnessed lane.
const aliased = [...row];
aliased[CELL.balanceLo] = 2013265921n + row[CELL.balanceLo];
await refused('a balance lane aliased by the BabyBear modulus', () =>
  DreggCellFactStatement.proveCellFact(
    honest.anchored,
    aliased.map((x) => Field(x)),
    toDigests(bbSiblings),
    toBools(bbIsRight),
    pastaSiblings.map((x) => Field(x)),
  ),
);

// (e) THE ATTRIBUTABILITY CONTROL. A refusal guard that passes when the circuit
//     is simply unsatisfiable proves nothing, so re-prove the HONEST statement
//     after all four refusals and require it to still go through.
t = Date.now();
const { proof: honestAgain } = await DreggCellFactStatement.proveCellFact(
  honest.anchored,
  row.map((x) => Field(x)),
  toDigests(bbSiblings),
  toBools(bbIsRight),
  pastaSiblings.map((x) => Field(x)),
);
check(
  honestAgain.publicOutput.balanceLo.toBigInt() === row[CELL.balanceLo],
  `CONTROL: the honest cell still proves after four refusals (${secs(t)}) — the refusals are ` +
    'the tampers, not an unsatisfiable circuit',
  'the honest cell stopped proving, so the refusals above are not attributable',
);

// (f) THE FORGED-ANCHOR CONTROL. The dishonest prover CAN prove balance 101 —
//     against its own root. That proof is not a forgery of anything; it is the
//     reason clause 2 of `actOnCellFact` exists.
t = Date.now();
const { proof: forgedProof } = await DreggCellFactStatement.proveCellFact(
  forged.anchored,
  bumped.map((x) => Field(x)),
  toDigests(bbSiblings),
  toBools(bbIsRight),
  pastaSiblings.map((x) => Field(x)),
);
check(
  forgedProof.publicOutput.balanceLo.toBigInt() === bumped[CELL.balanceLo] &&
    forgedProof.publicInput.toBigInt() !== honest.anchored.toBigInt(),
  `a cell claiming ${bumped[CELL.balanceLo]} proves only against its OWN root (${secs(t)})`,
  'the forged cell proved against the honest root',
);

if (!atTier(2)) {
  tierStop1('cell-fact', 12, secs(t0), 'the zkApp actOnCellFact leg on a local chain');
  process.exit(failures === 0 ? 0 : 1);
}

// ===========================================================================
// [5] THE CONTRACT. A Mina zkApp requires a dregg BALANCE.
//
// ⚑ THE TWO STATEMENTS MEET AT A VALUE. `CELL_FACT_BB_DEPTH` is
// `ANCHOR_MERKLE_DEPTH`, so the BabyBear leaf `DreggAnchorStatement` opens is
// the SAME leaf the cell fact opens: `spongeBB(cell row)`. One opening feeds
// both proofs, the anchored root is the cell's own root, and the accept leg is
// therefore reachable. If they were at different heights this section could
// only ever show a refusal, and a leg that can only go red is not a gate.
// ===========================================================================

console.log('\n[5] the zkApp acts on the balance');

const gateAnalysis = await DreggAttestedGate.analyzeMethods();
console.log(`    actOnCellFact: ${gateAnalysis.actOnCellFact.rows} rows`);

t = Date.now();
await DreggAnchorStatement.compile();
ok(`compiled DreggAnchorStatement in ${secs(t)}`);
t = Date.now();
await DreggMembershipAttestation.compile();
ok(`compiled DreggMembershipAttestation in ${secs(t)}`);
t = Date.now();
await DreggAttestedGate.compile();
ok(`compiled DreggAttestedGate in ${secs(t)}`);

t = Date.now();
const { proof: anchorProof } = await DreggAnchorStatement.proveAnchorShape(
  honest.anchored,
  BbDigest.from(honest.leaf),
  toDigests(bbSiblings),
  toBools(bbIsRight),
  pastaSiblings.map((x) => Field(x)),
);
check(
  anchorProof.publicInput.toBigInt() === honest.anchored.toBigInt(),
  `the anchor statement proves the CELL'S OWN root in ${secs(t)} — one opening, two statements`,
  'the anchor statement proved a different root',
);

const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
Mina.setActiveInstance(Local);
const deployer = Local.testAccounts[0];
const zkAppKey = PrivateKey.random();
const zkApp = new DreggAttestedGate(zkAppKey.toPublicKey());
const relayKey = PrivateKey.random();

const deployTx = await Mina.transaction(deployer, async () => {
  AccountUpdate.fundNewAccount(deployer);
  await zkApp.deploy({ placeholderRelay: relayKey.toPublicKey() });
});
await deployTx.prove();
await deployTx.sign([deployer.key, zkAppKey]).send();
ok('deployed the gate');

// ⚑ Anchored through `setDreggRoot`, so the root carries exactly the obligation
// the deployed path carries — INCLUDING `placeholderAuth`, the relay key. That
// key is the open sin this rung inherits and does not close.
const setTx = await Mina.transaction(deployer, async () => {
  await zkApp.setDreggRoot(
    anchorProof,
    signPlaceholderAnchor(relayKey, Field(0), honest.anchored),
  );
});
await setTx.prove();
await setTx.sign([deployer.key]).send();
check(
  zkApp.dreggRoot.get().toBigInt() === honest.anchored.toBigInt(),
  "the gate anchored the cell's root",
  "the gate did not anchor the cell's root",
);

// THE ACCEPT. A Mina contract requires that a dregg cell held at least 100.
t = Date.now();
const floor = row[CELL.balanceLo];
const actTx = await Mina.transaction(deployer, async () => {
  await zkApp.actOnCellFact(honestProof, Field(floor));
});
await actTx.prove();
await actTx.sign([deployer.key]).send();
check(
  zkApp.lastCellFact.get().toBigInt() === fact.digest().toBigInt(),
  `the zkApp REQUIRED balance_lo >= ${floor} of a dregg cell and recorded the fact (${secs(t)})`,
  'the zkApp did not record the cell fact',
);

// REFUSAL 1: a floor the cell does not meet.
let overAccepted = false;
try {
  const tx = await Mina.transaction(deployer, async () => {
    await zkApp.actOnCellFact(honestProof, Field(floor + 1n));
  });
  await tx.prove();
  await tx.sign([deployer.key]).send();
  overAccepted = true;
} catch {
  /* expected: balanceFloor.assertLessThanOrEqual(fact.balanceLo) */
}
check(
  !overAccepted,
  `the zkApp REFUSES a floor of ${floor + 1n} — one nanomina above what dregg's cell holds`,
  'the zkApp accepted a floor above the cell balance (UNSOUND)',
);

// REFUSAL 2: the forged cell, which claims MORE and proves only against its own
// root. This is the whole reason clause (2) exists.
let forgedAccepted = false;
try {
  const tx = await Mina.transaction(deployer, async () => {
    await zkApp.actOnCellFact(forgedProof, Field(0));
  });
  await tx.prove();
  await tx.sign([deployer.key]).send();
  forgedAccepted = true;
} catch {
  /* expected: proof.publicInput.assertEquals(root) */
}
check(
  !forgedAccepted,
  `the zkApp REFUSES the cell claiming ${bumped[CELL.balanceLo]}: it is committed under a ` +
    'different root',
  'the zkApp accepted a cell fact read out of a root it does not hold (UNSOUND)',
);

// CONTROL: the honest fact still goes through after both refusals.
const againTx = await Mina.transaction(deployer, async () => {
  await zkApp.actOnCellFact(honestProof, Field(0));
});
await againTx.prove();
await againTx.sign([deployer.key]).send();
check(
  zkApp.lastCellFact.get().toBigInt() === fact.digest().toBigInt(),
  'CONTROL: the honest fact still passes after both refusals',
  'the honest fact stopped passing, so the refusals are not attributable',
);

console.log(
  failures === 0
    ? `\nPASS — cell-fact gate, ${CELL_FACT_BB_DEPTH}-deep MMCS, real Lean-emitted cell`
    : `\nFAIL — ${failures} check(s) failed`,
);
process.exit(failures === 0 ? 0 : 1);
