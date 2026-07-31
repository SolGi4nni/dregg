// FOLD-TREE — the merge node, its controls, and the anchor it makes possible.
//
//   O1JS_BACKEND=native npm run fold-tree
//
// ── WHAT THIS IS FOR ───────────────────────────────────────────────────────
// `fold-mu` measured what a merge COSTS. This measures whether it REFUSES.
//
// ⚠ THE LEAVES HERE ARE STAND-INS, AND EVERY LINE THAT PRINTS SAYS SO. The
// reason is not convenience: `DreggFold` verifies leaf proofs BY CLASS, so a
// run over dregg's real leaves has to COMPILE the real slice programs in this
// process — 88 head positions and 43 block positions at ~47,000 rows each, none
// of which has ever been proved once. The stand-ins have the exact shape a
// uniform slice has (`publicInput: Field`, `publicOutput: ClaimedBoundary`,
// `maxProofsVerified = 1`) and DIFFERENT constraint systems from each other, so
// every row below is VK-independent — the same discipline `head-gate-rehearsal`
// runs on, and for the same reason.
//
// ⚑ FOUR CONTROLS, THIS REPO'S STANDARD, AND EACH REMOVES EXACTLY ONE THING.
// A refusal is only attributable if an otherwise-identical circuit ACCEPTS the
// same forged object.
//
//   ADJACENCY  pair(leaf1, leaf3) — a splice that skips leaf 2.
//              armed: refused.   `adjacent: false`: accepted.
//   CLAIM      two halves stating different claims.
//              armed: refused.   `carryClaim: false`: accepted, root states
//              the left one.
//   COUNT      a root naming more leaves than it folded.
//              armed: impossible — `count` is `l.count + r.count`.
//              `countAdditive: false`: the prover names it, and an anchor
//              pinning `count == N` takes a 2-leaf tree as N.
//   LEAF LIST  a fold built over a DIFFERENT leaf program.
//              armed: a different verification key, so the anchor's
//              `vk.hash == FOLD_VK_HASH` refuses the whole tree; and the armed
//              program will not take the foreign leaf at all.
//
// ── THE TWO PHASES ─────────────────────────────────────────────────────────
// `DynamicProof.tag()` names itself off a process-global counter, so the ONE
// side-loaded class in this design — `DreggFoldRootProof`, how the gate reads a
// root — gets its own process.
//
//   tree   the producers, the folds, the four control rows, the root proof
//   gate   that root against `DreggFoldGate`

import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { relative, resolve } from 'node:path';
import { Field, Poseidon, SelfProof, VerificationKey, ZkProgram } from 'o1js';
//  ⚑ STATIC where it is safe, DYNAMIC where a module-scope `DynamicProof` lives.
//  `RootClaim` and `DreggFold` create no side-loaded class at import time;
//  `DreggHeadAnchor` (`DreggTerminalProof`) and `DreggFoldAnchor`
//  (`DreggFoldRootProof`) do, and `DynamicProof.tag()` is order-dependent.
import { ChainClaim, ClaimedBoundary } from '../src/RootClaim.js';
import { FoldNode, makeDreggFold } from '../src/DreggFold.js';

const WORK = process.env.FOLD_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const PHASE = process.env.FOLD_PHASE ?? 'all';
const OUT = (n: string) => resolve(WORK, `fold-${n}`);

const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(2)}s`;
let failed = 0;
const ok = (s: string) => console.log(`    ok   ${s}`);
const fail = (s: string) => {
  failed++;
  console.log(`    FAIL ${s}`);
};

/** A refusal has to be a CONSTRAINT failure or o1js refusing the object. A
 *  `TypeError` is a broken harness wearing a refusal's clothes, and this repo
 *  has shipped one. */
const isRefusal = (e: unknown): boolean => {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|DreggFoldGate|proof|verification key/i.test(
    m,
  );
};

async function refuses(what: string, run: () => Promise<unknown>): Promise<boolean> {
  const t = Date.now();
  try {
    await run();
    fail(`${what} — ACCEPTED. It must not be.`);
    return false;
  } catch (e) {
    if (!isRefusal(e)) {
      fail(`${what} — threw, but not as a refusal: ${String((e as Error)?.message ?? e).slice(0, 200)}`);
      return false;
    }
    ok(`${what} — REFUSED (${secs(t)})`);
    return true;
  }
}

async function accepts(what: string, run: () => Promise<any>): Promise<any> {
  const t = Date.now();
  try {
    const r = await run();
    ok(`${what} — accepted (${secs(t)})`);
    return r;
  } catch (e) {
    fail(
      `${what} — REFUSED, and this row exists to show it is accepted: ` +
        String((e as Error)?.message ?? e).slice(0, 200),
    );
    return null;
  }
}

/**
 * A producer of the SHAPE a uniform slice has: `publicInput: Field` (the
 * interval's entry boundary), `publicOutput: ClaimedBoundary`, and a `relay`
 * branch so `maxProofsVerified === 1` exactly as a slice's `prev.verify` makes
 * it. `rounds > 0` perturbs the constraint system so the key genuinely differs —
 * without it "a different leaf program" is the same key and the leaf-list row
 * tests nothing.
 */
const producer = (name: string, rounds: number) =>
  ZkProgram({
    name,
    publicInput: Field,
    publicOutput: ClaimedBoundary,
    methods: {
      emit: {
        privateInputs: [Field, ChainClaim],
        async method(bIn: Field, bOut: Field, claim: ChainClaim) {
          let acc = bIn;
          for (let i = 0; i < rounds; i++) acc = Poseidon.hash([acc, Field(i)]);
          acc.assertNotEquals(Field(0xdead_beefn));
          bIn.assertNotEquals(bOut);
          return { publicOutput: new ClaimedBoundary({ boundary: bOut, claim }) };
        },
      },
      relay: {
        privateInputs: [SelfProof],
        async method(_b: Field, prev: SelfProof<Field, ClaimedBoundary>) {
          prev.verify();
          return { publicOutput: prev.publicOutput };
        },
      },
    },
  });

const CLAIM = new ChainClaim({
  genesisRoot: Field(0x7393_bc8b_0218_6f4bn),
  finalRoot: Field(0xf1_4a_1en),
  numTurns: Field(7),
  chainDigest: Field(0xd1_9e_57n),
});
/** A DIFFERENT claim, for the claim-drift row. */
const OTHER_CLAIM = new ChainClaim({
  genesisRoot: Field(0x7393_bc8b_0218_6f4bn),
  finalRoot: Field(0xbad_1en),
  numTurns: Field(9),
  chainDigest: Field(0xd1_9e_58n),
});
/** Four boundaries: the chain b0 -> b1 -> b2 -> b3 -> b4. */
const B = [0x0b_00n, 0x0b_01n, 0x0b_02n, 0x0b_03n, 0x0b_04n].map((x) => Field(x));

// ===========================================================================
// PHASE `tree`
// ===========================================================================
async function phaseTree() {
  console.log('[1] THE LEAF PROGRAMS — the shape a uniform slice has\n');
  console.log(
    "    ⚠ STAND-INS, and the reason is structural: `DreggFold` verifies leaves BY CLASS, so a run\n" +
      '      over dregg\'s real leaves compiles the real slice programs here. Every row below is\n' +
      '      VK-independent — `head-gate-rehearsal.ts`\'s discipline, for the same reason.\n',
  );
  let t = Date.now();
  const HeadLike = producer('fold-standin-HEAD-NOT-DREGGS-CHAIN', 0);
  const BlockLike = producer('fold-standin-BLOCK-NOT-DREGGS-CHAIN', 3);
  const Alien = producer('fold-standin-ALIEN-not-in-the-leaf-list', 7);
  const hvk = (await HeadLike.compile()).verificationKey;
  const bvk = (await BlockLike.compile()).verificationKey;
  const avk = (await Alien.compile()).verificationKey;
  console.log(`    3 producers compiled in ${secs(t)}`);
  const keys = [hvk, bvk, avk].map((v) => v.hash.toBigInt());
  if (new Set(keys.map(String)).size !== 3)
    fail('two producers share a verification key — every leaf-list row below would test nothing');
  else ok('three leaf programs with three DIFFERENT constraint systems and three different keys');

  t = Date.now();
  const h0 = (await HeadLike.emit(B[0], B[1], CLAIM)).proof;
  const b1 = (await BlockLike.emit(B[1], B[2], CLAIM)).proof;
  const b2 = (await BlockLike.emit(B[2], B[3], CLAIM)).proof;
  const b3 = (await BlockLike.emit(B[3], B[4], CLAIM)).proof;
  const bDrift = (await BlockLike.emit(B[1], B[2], OTHER_CLAIM)).proof;
  const alien = (await Alien.emit(B[1], B[2], CLAIM)).proof;
  console.log(`    6 leaf proofs in ${secs(t)} — a 4-interval chain b0->b1->b2->b3->b4`);

  class HeadProof extends ZkProgram.Proof(HeadLike) {}
  class BlockProof extends ZkProgram.Proof(BlockLike) {}
  class AlienProof extends ZkProgram.Proof(Alien) {}

  const LEAVES = [
    { name: 'head', cls: HeadProof },
    { name: 'block', cls: BlockProof },
  ];
  //  The adjacencies that occur in the coarse tree: the head strand is followed
  //  by a query block, and a query block by the next query block.
  const ADJ: [number, number][] = [
    [0, 1],
    [1, 1],
  ];

  // =====================================================================
  console.log('\n[2] THE FOLD — one program, one key, every branch 0 or 2 proofs\n');
  console.log(
    '    ⚑ MEASURED, and it is why the key TREE is gone: a branch verifying EXACTLY ONE proof\n' +
      '      inside a program whose maxProofsVerified is 2 cannot be proved on o1js 2.15, and a\n' +
      '      SIDE-LOADED verification poisons its whole descendant subtree for arity 2. So a merge\n' +
      '      tree cannot consume side-loaded leaves at all, `lift`/`vkRoot`/`vkPath` are deleted,\n' +
      '      and the leaf keys are pinned the stronger way — inside the fold key.\n',
  );
  t = Date.now();
  const A = makeDreggFold({ leafClasses: LEAVES, adjacencies: ADJ });
  const fvk = (await A.prog.compile()).verificationKey;
  console.log(`    compiled ${A.name} in ${secs(t)}   vk ${fvk.hash.toBigInt()}`);
  console.log(`    branches: ${A.pairName(0, 1)}, ${A.pairName(1, 1)}, merge, unit`);

  // =====================================================================
  console.log('\n[3] THE ARMED TREE — four intervals become one node\n');
  t = Date.now();
  const n01 = (await (A.prog as any)[A.pairName(0, 1)](h0, b1, Field(0))).proof;
  const n23 = (await (A.prog as any)[A.pairName(1, 1)](b2, b3, Field(0))).proof;
  const root = (await A.prog.merge(n01, n23, Field(0))).proof;
  console.log(`    2 pairs + 1 merge in ${secs(t)}`);
  const R = root.publicOutput as FoldNode;
  if (R.bIn.toBigInt() !== B[0].toBigInt() || R.bOut.toBigInt() !== B[4].toBigInt())
    fail(`the root spans ${R.bIn.toBigInt()}..${R.bOut.toBigInt()}, not b0..b4`);
  else ok('the ROOT states the OUTER interval — leftmost leaf in, rightmost leaf out');
  if (R.count.toBigInt() !== 4n) fail(`the root counts ${R.count.toBigInt()} leaves, not 4`);
  else ok('the root counts 4 leaves');
  if (R.claim.numTurns.toBigInt() !== 7n) fail('the root does not carry the leaves\' claim');
  else ok('the root carries the claim every leaf stated');
  if (!(await A.prog.verify(root))) fail('the root does not verify under the fold key');
  else ok('the root verifies under the SAME key `pair` produced — one key, every level');

  //  ---- the identity, and why a ragged tree needs it ----------------------
  t = Date.now();
  const u = (await A.prog.unit(B[4], R.claim)).proof;
  const padded = (await A.prog.merge(root, u, Field(0))).proof;
  const PR = padded.publicOutput as FoldNode;
  const same =
    PR.bIn.toBigInt() === R.bIn.toBigInt() &&
    PR.bOut.toBigInt() === R.bOut.toBigInt() &&
    PR.count.toBigInt() === R.count.toBigInt();
  if (!same) fail('folding the IDENTITY changed the node — it is not an identity');
  else
    ok(
      `merging the zero-length identity leaves the node byte-identical (${secs(t)}) — which is how ` +
        'an ODD tail reaches the root without a 1-proof branch',
    );

  //  ---- associativity, measured -------------------------------------------
  t = Date.now();
  const leftDeep1 = (await (A.prog as any)[A.pairName(0, 1)](h0, b1, Field(0))).proof;
  const rightPair = (await (A.prog as any)[A.pairName(1, 1)](b2, b3, Field(0))).proof;
  const assoc = (await A.prog.merge(leftDeep1, rightPair, Field(0))).proof;
  const AS = assoc.publicOutput as FoldNode;
  if (
    AS.bIn.toBigInt() !== R.bIn.toBigInt() ||
    AS.bOut.toBigInt() !== R.bOut.toBigInt() ||
    AS.count.toBigInt() !== R.count.toBigInt()
  )
    fail('re-folding the same leaves gave a different root node');
  else ok(`re-folding the same four leaves gives an IDENTICAL root node (${secs(t)})`);

  // =====================================================================
  console.log('\n[4] THE SPLICE — and the control that attributes the refusal\n');
  await refuses('ARMED: pair(leaf1, leaf3) — a splice that skips leaf 2', async () =>
    (A.prog as any)[A.pairName(1, 1)](b1, b3, Field(0)),
  );
  t = Date.now();
  const U = makeDreggFold({ leafClasses: LEAVES, adjacencies: ADJ, adjacent: false });
  await U.prog.compile();
  console.log(`    compiled ${U.name} in ${secs(t)} — ONE assertion removed`);
  const spliced = await accepts('CONTROL (adjacent: false): the SAME non-adjacent pair', async () =>
    (U.prog as any)[U.pairName(1, 1)](b1, b3, Field(0)),
  );
  if (spliced)
    ok(
      'the splice refusal is attributable to `l.bOut == r.bIn` and to nothing else — the same two ' +
        'leaves compose the moment that line is gone',
    );

  // =====================================================================
  console.log('\n[5] THE CLAIM — two halves that do not agree\n');
  await refuses('ARMED: pair(leaf1, leaf1-with-another-claim) — adjacent, two claims', async () =>
    (A.prog as any)[A.pairName(0, 1)](h0, bDrift, Field(0)),
  );
  t = Date.now();
  const D = makeDreggFold({ leafClasses: LEAVES, adjacencies: ADJ, carryClaim: false });
  await D.prog.compile();
  console.log(`    compiled ${D.name} in ${secs(t)} — the four claim equalities removed`);
  const drifted = await accepts('CONTROL (carryClaim: false): the SAME two leaves', async () =>
    (D.prog as any)[D.pairName(0, 1)](h0, bDrift, Field(0)),
  );
  if (drifted)
    ok('the claim refusal is attributable to `assertClaimCarried` and to nothing else');

  // =====================================================================
  console.log('\n[6] THE COUNT — the anchor\'s only pin on how much was folded\n');
  t = Date.now();
  const C = makeDreggFold({ leafClasses: LEAVES, adjacencies: ADJ, countAdditive: false });
  await C.prog.compile();
  const forged = (await (C.prog as any)[C.pairName(0, 1)](h0, b1, Field(4))).proof;
  console.log(`    compiled ${C.name} and forged in ${secs(t)}`);
  const armedTwo = (n01.publicOutput as FoldNode).count.toBigInt();
  const forgedTwo = (forged.publicOutput as FoldNode).count.toBigInt();
  console.log(`    two leaves, ARMED   -> count ${armedTwo}`);
  console.log(`    two leaves, CONTROL -> count ${forgedTwo}   (the prover named it)`);
  if (armedTwo !== 2n) fail(`the armed pair of two leaves counted ${armedTwo}`);
  if (forgedTwo !== 4n) fail("the count-forgery control did not take the prover's 4");
  //  The anchor predicate, out of circuit, exactly as `DreggFoldGate` spells it.
  const anchorAccepts = (n: FoldNode, leaves: number) =>
    n.count.toBigInt() === BigInt(leaves) && n.bIn.toBigInt() === B[0].toBigInt();
  if (anchorAccepts(n01.publicOutput as FoldNode, 4))
    fail('an anchor pinning 4 leaves accepted the ARMED 2-leaf tree — the count pin does nothing');
  else ok('an anchor pinning 4 leaves REFUSES the armed 2-leaf tree (count 2)');
  if (!anchorAccepts(forged.publicOutput as FoldNode, 4))
    fail('the forged 2-leaf tree was refused for some OTHER reason — the row is not attributable');
  else
    ok(
      "the SAME anchor ACCEPTS the control's 2-leaf tree that named 4 — so `count = l.count + " +
        'r.count` is the whole of what makes a partial tree unpresentable',
    );
  if (anchorAccepts(R, 4)) ok('and it accepts the genuine 4-leaf root');
  else fail('the anchor predicate refused the genuine root');

  // =====================================================================
  console.log('\n[7] THE LEAF LIST — a program the fold does not name\n');
  await refuses('ARMED: pair(head0, ALIEN) — a proof of a program not in the leaf list', async () =>
    (A.prog as any)[A.pairName(0, 1)](h0, alien as any, Field(0)),
  );
  t = Date.now();
  const X = makeDreggFold({
    leafClasses: [
      { name: 'head', cls: HeadProof },
      { name: 'block', cls: AlienProof },
    ],
    adjacencies: ADJ,
    suffix: '-ALIENLEAVES',
  });
  const xvk = (await X.prog.compile()).verificationKey;
  console.log(`    compiled a fold over the ALIEN leaf program in ${secs(t)}`);
  if (xvk.hash.toBigInt() === fvk.hash.toBigInt())
    fail('swapping a leaf program did not change the fold key — the leaf list is NOT in the key');
  else
    ok(
      'swapping ONE leaf program changes the FOLD verification key ' +
        `(${String(fvk.hash.toBigInt()).slice(0, 12)}… vs ${String(xvk.hash.toBigInt()).slice(0, 12)}…) — ` +
        "so an anchor's `vk.hash == FOLD_VK_HASH` pins the whole leaf list at compile time, with " +
        'no carried key root and no runtime comparison',
    );
  const alienRoot = await accepts(
    'CONTROL: the ALIEN fold happily folds the alien leaf (its own leaves are fine)',
    async () => (X.prog as any)[X.pairName(0, 1)](h0, alien as any, Field(0)),
  );
  if (alienRoot)
    ok('the leaf-list refusal is attributable to WHICH CLASSES the fold was compiled against');

  // =====================================================================
  //  ⚑ THE PARTIAL TREE the gate's count row needs: two leaves, not four.
  mkdirSync(WORK, { recursive: true });
  writeFileSync(OUT('root-proof.json'), JSON.stringify(root.toJSON()));
  writeFileSync(OUT('partial-proof.json'), JSON.stringify(n01.toJSON()));
  writeFileSync(OUT('fold-vk.json'), JSON.stringify(fvk));
  writeFileSync(
    OUT('gate-pins.json'),
    JSON.stringify(
      {
        label:
          "STAND-IN leaf programs folded to a 4-leaf root — NOT dregg's chain, and never reported as one",
        foldVkHash: String(fvk.hash.toBigInt()),
        foldLeaves: 4,
        chainEntryBoundary: String(B[0].toBigInt()),
        genesisRoot: String(CLAIM.genesisRoot.toBigInt()),
        finalRoot: String(CLAIM.finalRoot.toBigInt()),
        numTurns: String(CLAIM.numTurns.toBigInt()),
        leafVkHashes: { head: String(keys[0]), block: String(keys[1]), alien: String(keys[2]) },
        alienFoldVkHash: String(xvk.hash.toBigInt()),
      },
      null,
      2,
    ) + '\n',
  );
  console.log(`\n    wrote ${relative(process.cwd(), OUT('gate-pins.json'))} and two proofs`);
}

// ===========================================================================
// PHASE `gate` — the reworked anchor: three comparisons, no preimage.
// ===========================================================================
async function phaseGate() {
  const { AccountUpdate, Mina, PrivateKey } = await import('o1js');
  const { DreggBootstrap } = await import('../src/DreggHeadAnchor.js');
  const { DreggFoldRootProof, makeDreggFoldGate, __resetFoldGateFactoryForTest } = await import(
    '../src/DreggFoldAnchor.js'
  );

  const pins = JSON.parse(readFileSync(OUT('gate-pins.json'), 'utf8'));
  const rootJson = JSON.parse(readFileSync(OUT('root-proof.json'), 'utf8'));
  const partialJson = JSON.parse(readFileSync(OUT('partial-proof.json'), 'utf8'));
  const fvk = VerificationKey.fromJSON(JSON.parse(readFileSync(OUT('fold-vk.json'), 'utf8')));

  const P = {
    label: pins.label,
    foldVkHash: BigInt(pins.foldVkHash),
    foldLeaves: Number(pins.foldLeaves),
    chainEntryBoundary: BigInt(pins.chainEntryBoundary),
    genesisRoot: BigInt(pins.genesisRoot),
  };

  console.log('[8] THE REWORKED ANCHOR — `advanceHead(root, vk)`, two arguments\n');
  console.log('    the three lines this gate is:');
  console.log(`        vk.hash    == ${P.foldVkHash}`);
  console.log(`        node.count == ${P.foldLeaves}`);
  console.log(`        node.bIn   == ${P.chainEntryBoundary}`);
  console.log(
    '    and `(friCommit, accOutDigest)` are not among them. Neither is a `chainVkRoot`:\n' +
      "    the leaf programs' keys are inside `FOLD_VK_HASH`.\n",
  );

  const root = await (DreggFoldRootProof as any).fromJSON(rootJson);
  const partial = await (DreggFoldRootProof as any).fromJSON(partialJson);

  let t = Date.now();
  const built = makeDreggFoldGate(P);
  const Gate = built.DreggFoldGate;
  await Gate.compile();
  ok(`compiled ${built.variant} in ${secs(t)}`);

  const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
  Mina.setActiveInstance(Local);
  const deployer = Local.testAccounts[0];
  const zkAppKey = PrivateKey.random();
  const app = new Gate(zkAppKey.toPublicKey());

  t = Date.now();
  const bootstrap = DreggBootstrap.weakSubjectivityAnchor(
    Field(P.genesisRoot),
    'fold-tree rehearsal anchor — an operator asserting genesis out of band, which is what this is',
  );
  const dep = await Mina.transaction(deployer, async () => {
    AccountUpdate.fundNewAccount(deployer);
    await app.deploy({ bootstrap });
  });
  await dep.prove();
  await dep.sign([deployer.key, zkAppKey]).send();
  ok(`deployed at the weak-subjectivity anchor (${secs(t)})`);

  console.log('\n    the ROWS — each against a real prove()\n');
  await refuses(
    'a PARTIAL tree (2 leaves where the gate names 4) — the six-of-nineteen shape',
    async () => {
      const tx = await Mina.transaction(deployer, async () => {
        await app.advanceHead(partial, fvk);
      });
      await tx.prove();
      await tx.sign([deployer.key]).send();
    },
  );
  const good = await accepts('the genuine 4-leaf root', async () => {
    const tx = await Mina.transaction(deployer, async () => {
      await app.advanceHead(root, fvk);
    });
    await tx.prove();
    await tx.sign([deployer.key]).send();
    return true;
  });
  if (good) {
    const head = app.head.get().toBigInt();
    const turns = app.turns.get().toBigInt();
    if (head !== BigInt(pins.finalRoot)) fail(`the head moved to ${head}, not the claim's finalRoot`);
    else ok(`the head moved to the claim's finalRoot, turns = ${turns}`);
  }

  console.log('\n    the CONTROL that makes the partial-tree refusal attributable\n');
  __resetFoldGateFactoryForTest();
  t = Date.now();
  const c = makeDreggFoldGate(P, { requireCount: false });
  const CGate = c.DreggFoldGate;
  await CGate.compile();
  ok(`compiled ${c.variant} in ${secs(t)} — the \`count\` comparison removed, and nothing else`);
  const ckey = PrivateKey.random();
  const capp = new CGate(ckey.toPublicKey());
  const dep2 = await Mina.transaction(deployer, async () => {
    AccountUpdate.fundNewAccount(deployer);
    await capp.deploy({ bootstrap });
  });
  await dep2.prove();
  await dep2.sign([deployer.key, ckey]).send();
  const accepted = await accepts('CONTROL (requireCount: false): the SAME partial tree', async () => {
    const tx = await Mina.transaction(deployer, async () => {
      await capp.advanceHead(partial, fvk);
    });
    await tx.prove();
    await tx.sign([deployer.key]).send();
    return true;
  });
  if (accepted)
    ok(
      'the partial-tree refusal is attributable to `node.count == FOLD_LEAVES` and to nothing ' +
        'else — the obligation the OLD gate needed a `(friCommit, accOutDigest)` preimage for',
    );
}

// ===========================================================================
async function main() {
  if (PHASE === 'tree') return phaseTree();
  if (PHASE === 'gate') return phaseGate();

  console.log('=== FOLD-TREE — the merge node, its controls, and the anchor ===\n');
  console.log(`    backend ${process.env.O1JS_BACKEND ?? 'wasm (default)'}   node ${process.version}\n`);
  for (const p of ['tree', 'gate']) {
    const t = Date.now();
    try {
      execFileSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
        stdio: 'inherit',
        env: { ...process.env, FOLD_PHASE: p, FOLD_WORKDIR: WORK },
      });
    } catch {
      failed++;
      console.log(`\n    FAIL phase \`${p}\` exited non-zero after ${secs(t)}`);
    }
  }
  console.log(
    failed === 0 ? '\n=== FOLD-TREE: PASS ===\n' : `\n=== FOLD-TREE: ${failed} PHASE FAILURE(S) ===\n`,
  );
  process.exit(failed === 0 ? 0 : 1);
}

main()
  .then(() => {
    if (PHASE !== 'all') {
      console.log(
        failed === 0 ? `\n    phase \`${PHASE}\` PASS\n` : `\n    phase \`${PHASE}\`: ${failed} FAILURE(S)\n`,
      );
      process.exit(failed === 0 ? 0 : 1);
    }
  })
  .catch((e) => {
    console.error(e);
    process.exit(1);
  });
