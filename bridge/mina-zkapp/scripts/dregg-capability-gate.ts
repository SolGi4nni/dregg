// DREGG CAPABILITY GATE — RUN IT, and report o1js's literal verdict on every case.
//
//   TS_NODE_TRANSPILE_ONLY=true node --loader ts-node/esm --no-warnings \
//     scripts/dregg-capability-gate.ts [--devnet-vk] [--skip-arity] [--skip-flags]
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE QUESTION
//
//   Can a Mina zkApp exercise a dregg capability?
//
// and specifically the part a generic proof-verifier cannot reach: can it honor a NARROWED one,
// under a key it has never seen, and refuse the exercise the narrowing removed?
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE DISCIPLINE THIS SCRIPT INHERITS
//
// `scripts/mina-proof-verify-gate.mjs` refuses to report on anything until its controls have moved
// in BOTH directions, on the grounds that a script which only ever prints `false` is equally
// consistent with a broken harness. Same rule here, and stricter, because this gate has more ways to
// be vacuously green: a contract that accepted everything would pass every GREEN case. So every RED
// case names the exact conjunct it is aimed at, and the summary refuses unless every GREEN passed
// AND every RED failed.
//
// ⚑ THE ATTENUATION CONTROL IS THE ONE THAT MATTERS. R1 exercises an effect the ROOT holds and the
// NARROWING dropped, and pairs with G4 — the SAME effect, the SAME gate, under the root's own
// capability, ACCEPTED. Either alone would be consistent with a gate that just dislikes SET_FIELD;
// together they isolate the narrowing as the cause.
//
// ⚑ AND THE MEASUREMENTS ARE RE-RUN, NOT CITED. Stage 2 re-measures the `maxProofsVerified` pin and
// stage 11 the feature-flag pin, every run, because both are load-bearing for the design and both
// contradict something o1js's own documentation implies.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE NUMBERS ARE FROM A REAL DREGG TURN, NOT INVENTED
//
// `demo/two-ai-handoff/state/` holds a real two-party dregg capability handoff, verified at the time
// by an independent node running an independent binary (`charlie.verdict.json`: "Effect VM proof
// verified (trace_len=2, pi_count=74)", for both turns). This run's subject cell, transfer amount and
// turn hashes are read out of those files:
//
//   alice_cell         28292ff1b04ee1a666d2c4f7556d240b12f485edac0ff1a89c24dddffb680cee
//   grant_turn_hash    a50d29f08df55871f0fc94113a41f90908889302fee5d5a53a11c2ee7ebe53c4   (Alice GRANTS)
//   bob_exercise_turn  e6bce25f9e8e01e1e9294e903e7fd09c4e11c7dc9df2ea7c878585c0b58571a2   (Bob EXERCISES)
//   transfer_amount    100
//
// ⚠ AND WHAT THAT DOES NOT MEAN. Using the real cell id and the real amount makes the Mina-side
// capability be ABOUT a real dregg object. It does not make this a verification of that turn — see
// `DreggCapabilityGate.checkAndRecord` step 5, which marks the exact line COMMITTED, NOT VERIFIED.
// The files are read at run time and their digests printed, so a reader can check they were not
// paraphrased.

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  AccountUpdate,
  DynamicProof,
  FeatureFlags,
  Field,
  Mina,
  PrivateKey,
  UInt64,
  Undefined,
  VerificationKey,
  ZkProgram,
} from 'o1js';

import {
  DreggAttenuate,
  DreggCapability,
  DreggDelegatedCapabilityProof,
  DreggRootCapabilityProof,
  DreggDelegatedCapabilityProofAllNone,
  DreggRootCapabilityProofAllNone,
  DreggCapabilityRoot,
  DreggRogueAttenuate,
  EFFECT_BITS,
  EFFECT_EMIT_EVENT,
  EFFECT_GRANT_CAPABILITY,
  EFFECT_SET_FIELD,
  EFFECT_ALL,
  EFFECT_TRANSFER,
  FACET_TRANSFER_ONLY,
  isEffectPermitted,
  isFacetAttenuation,
} from '../src/DreggCapability.js';
import { DreggCapabilityGate } from '../src/DreggCapabilityGate.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
/** Walk up to the repo root by looking for the file this gate transcribes, rather than counting
 *  `..`s: the same source runs from `scripts/` under ts-node AND from `dist/scripts/` under
 *  `npm run capability-gate`, and those are different depths. `DREGG_REPO_ROOT` wins if set, as it
 *  does for every other leg of scripts/check-mina-attestation.sh. */
const REPO = (() => {
  const env = process.env.DREGG_REPO_ROOT;
  if (env !== undefined && env !== '') return env;
  let d = HERE;
  for (;;) {
    try {
      readFileSync(path.join(d, 'cell', 'src', 'facet.rs'));
      return d;
    } catch {
      const up = path.dirname(d);
      if (up === d) throw new Error(`cannot find a repo root containing cell/src/facet.rs above ${HERE}`);
      d = up;
    }
  }
})();
const argv = process.argv.slice(2);
const WANT_DEVNET_VK = argv.includes('--devnet-vk');
const SKIP_ARITY = argv.includes('--skip-arity');
const SKIP_FLAGS = argv.includes('--skip-flags');

const t0 = Date.now();
const stamp = () => `${((Date.now() - t0) / 1000).toFixed(1)}s`;
const say = (s = '') => console.log(s);
const step = (s: string) => console.log(`\n[${stamp()}] ── ${s}`);
const record: any = { what: 'dregg capability exercised through a Mina zkApp side-loaded slot', ranAt: new Date().toISOString() };

// ═════════════════════════════════════════════════════════════════════════════ 0. transcription gate
// The facet bits in DreggCapability.ts are a TRANSCRIPTION of cell/src/facet.rs. A transcription
// that drifts is worse than no transcription, because every downstream assertion keeps passing
// against the wrong lattice. So: re-read the Rust and refuse to run on any disagreement.

step('0. TRANSCRIPTION GATE — cell/src/facet.rs is the source of the lattice');
const FACET_RS = path.join(REPO, 'cell', 'src', 'facet.rs');
const facetSrc = readFileSync(FACET_RS, 'utf8');
const facetSha = createHash('sha256').update(facetSrc).digest('hex');
say(`  ${FACET_RS}`);
say(`  sha256 ${facetSha}`);

const rustBits = new Map<string, bigint>();
for (const m of facetSrc.matchAll(/^pub const EFFECT_([A-Z0-9_]+):\s*EffectMask\s*=\s*1\s*<<\s*(\d+);/gm)) {
  rustBits.set(m[1], BigInt(m[2]));
}
let transcriptionOk = rustBits.size > 0;
if (!transcriptionOk) say('  RED: parsed ZERO `pub const EFFECT_* = 1 << n` lines out of facet.rs — the shape changed');
for (const [name, shift] of EFFECT_BITS) {
  const r = rustBits.get(name);
  if (r === undefined) { say(`  RED: EFFECT_${name} is declared here but NOT in facet.rs`); transcriptionOk = false; }
  else if (r !== shift) { say(`  RED: EFFECT_${name} is 1<<${shift} here but 1<<${r} in facet.rs`); transcriptionOk = false; }
}
for (const name of rustBits.keys()) {
  if (!EFFECT_BITS.some(([n]) => n === name)) { say(`  RED: facet.rs declares EFFECT_${name} and this file does not carry it`); transcriptionOk = false; }
}
// The two predicates, out of circuit, against the Rust's own unit tests (facet.rs:575-613).
const predOk =
  isFacetAttenuation(EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT, EFFECT_SET_FIELD | EFFECT_EMIT_EVENT) &&
  !isFacetAttenuation(EFFECT_SET_FIELD | EFFECT_EMIT_EVENT, EFFECT_SET_FIELD | EFFECT_TRANSFER) &&
  isEffectPermitted(FACET_TRANSFER_ONLY, EFFECT_TRANSFER) &&
  !isEffectPermitted(FACET_TRANSFER_ONLY, EFFECT_SET_FIELD) &&
  !isEffectPermitted(0n, EFFECT_TRANSFER); // P2-1: Some(0) denies
if (!predOk) say('  RED: the out-of-circuit predicates disagree with facet.rs:575-613');
transcriptionOk = transcriptionOk && predOk;
say(`  ${transcriptionOk ? 'GREEN' : 'RED'}: ${rustBits.size} effect bits${transcriptionOk ? ', all agree with facet.rs, and the two predicates reproduce its unit tests' : ' — DISAGREEMENT, refusing to run'}`);
record.transcriptionGate = { file: FACET_RS, sha256: facetSha, bits: rustBits.size, ok: transcriptionOk };
if (!transcriptionOk) { say('\nrefusing to report: the in-circuit lattice would not be dregg\'s.'); process.exit(1); }

// ═════════════════════════════════════════════════════════════════════════════ 1. the real dregg turn

step('1. THE SUBJECT IS A REAL DREGG TURN');
const STATE_DIR = path.join(REPO, 'demo', 'two-ai-handoff', 'state');
const readJson = (p: string) => JSON.parse(readFileSync(p, 'utf8'));
const aliceOut = readJson(path.join(STATE_DIR, 'alice.out.json'));
const bobEx = readJson(path.join(STATE_DIR, 'bob.exercise.json'));
const charlie = readJson(path.join(STATE_DIR, 'charlie.verdict.json'));

const ALICE_CELL: string = aliceOut.alice_cell;
const GRANT_TURN: string = aliceOut.grant_turn_hash;
const EXERCISE_TURN: string = bobEx.exercise_turn_hash;
const TRANSFER_AMOUNT: number = bobEx.transfer_amount;

/** 32 hex bytes -> two Fields, high 16 bytes then low 16. Stated rather than hidden: a CellId is
 *  256 bits and Pallas Fp is ~254, so one element cannot hold it. */
const hex32ToFields = (hex: string): [Field, Field] => {
  const h = hex.startsWith('0x') ? hex.slice(2) : hex;
  if (!/^[0-9a-fA-F]{64}$/.test(h)) throw new Error(`not 32 hex bytes: ${hex}`);
  return [Field(BigInt('0x' + h.slice(0, 32))), Field(BigInt('0x' + h.slice(32)))];
};
const [SUBJECT_HI, SUBJECT_LO] = hex32ToFields(ALICE_CELL);
const [TURN_HI, TURN_LO] = hex32ToFields(EXERCISE_TURN);

say(`  ${STATE_DIR}`);
record.dreggTurn = { dir: STATE_DIR, files: {} as any, aliceCell: ALICE_CELL, grantTurn: GRANT_TURN, exerciseTurn: EXERCISE_TURN, transferAmount: TRANSFER_AMOUNT };
for (const f of ['alice.out.json', 'bob.exercise.json', 'charlie.verdict.json']) {
  const sha = createHash('sha256').update(readFileSync(path.join(STATE_DIR, f))).digest('hex');
  record.dreggTurn.files[f] = sha;
  say(`    ${f.padEnd(22)} sha256 ${sha}`);
}
say(`  alice_cell        ${ALICE_CELL}   -> subject (hi,lo)`);
say(`  grant_turn_hash   ${GRANT_TURN}   (Alice GRANTS the bearer cap)`);
say(`  bob_exercise_turn ${EXERCISE_TURN}   (Bob EXERCISES it)`);
say(`  transfer_amount   ${TRANSFER_AMOUNT}`);
say(`  charlie (independent node, independent binary): grant_verified=${charlie.grant_verified} exercise_verified=${charlie.exercise_verified} — "${charlie.exercise_reason}"`);
say('  ⚠ those verdicts are dregg-side, about the dregg STARK. Nothing below re-checks them.');

// ═════════════════════════════════════════════════════════════════════════════ 2. the arity pin
// ⚑ RE-MEASURED, NOT CITED. This is the constraint that dictates the contract's shape (two methods,
// two slots), and it contradicts o1js proof.d.ts:113-114's "if you are unsure ... use 2".

step('2. THE `maxProofsVerified` PIN — measured by verifying ONE arity-0 proof through three slots');
const arityMatrix: Array<{ tagArity: number; verdict: string; detail: string }> = [];
if (SKIP_ARITY) {
  say('  --skip-arity: not measured this run');
} else {
  const tc0 = Date.now();
  const rootVk0 = (await DreggCapabilityRoot.compile()).verificationKey;
  const probeProof = (await DreggCapabilityRoot.issue(SUBJECT_HI, SUBJECT_LO, Field(EFFECT_TRANSFER), UInt64.from(1n))).proof;
  say(`  a real arity-${probeProof.maxProofsVerified} root proof, produced in ${((Date.now() - tc0) / 1000).toFixed(1)}s (compile included)`);
  for (const tagArity of [0, 1, 2] as const) {
    class P extends DynamicProof<undefined, DreggCapability> {
      static publicInputType = Undefined;
      static publicOutputType = DreggCapability;
      static maxProofsVerified = tagArity;
      static featureFlags = FeatureFlags.allMaybe;
    }
    const probe = ZkProgram({
      name: `arity-probe-${tagArity}`,
      publicOutput: Field,
      methods: {
        go: {
          privateInputs: [P, VerificationKey],
          async method(p: any, vk: VerificationKey) {
            p.verify(vk);
            return { publicOutput: (p.publicOutput as DreggCapability).effectMask };
          },
        },
      },
    });
    const t = Date.now();
    try {
      await probe.compile();
      await (probe as any).go(P.fromProof(probeProof as any), rootVk0);
      arityMatrix.push({ tagArity, verdict: 'PROVED', detail: `${((Date.now() - t) / 1000).toFixed(1)}s` });
    } catch (e: any) {
      arityMatrix.push({ tagArity, verdict: 'REFUSED', detail: String(e?.message ?? e).split('\n').slice(0, 4).join(' / ') });
    }
    const r = arityMatrix[arityMatrix.length - 1];
    say(`  slot maxProofsVerified=${tagArity} -> ${r.verdict.padEnd(8)} ${r.detail}`);
  }
  const onlyZero = arityMatrix.filter((r) => r.verdict === 'PROVED').map((r) => r.tagArity);
  say(`  ⚑ MEASURED: an arity-0 proof is admitted by slot arity ${JSON.stringify(onlyZero)} and no other.`);
  say('    So `maxProofsVerified` must EQUAL the foreign proof\'s arity, not bound it. o1js\'s own');
  say('    advice ("if you are unsure ... use 2", proof.d.ts:113-114) produces the arity-2 line above.');
  say('    ⚑ CONSEQUENCE: one slot admits ONE arity — hence two gate methods, root vs delegate.');
}
record.arityPin = arityMatrix;

// ═════════════════════════════════════════════════════════════════════════════ 3. compile

step('3. COMPILE — root, attenuator, gate');
say('  Pickles.sideLoaded.create(name, maxProofsVerified, |pubIn|=0, |pubOut|=5, allMaybe)');
say('    ^ o1js 2.15.0 dist/node/lib/proof-system/zkprogram.js:594 — every argument frozen HERE');
say(`  |publicOutput| = DreggCapability.sizeInFields() = ${DreggCapability.sizeInFields()}`);

let tc = Date.now();
const rootVk = (await DreggCapabilityRoot.compile()).verificationKey;
say(`  [${stamp()}] DreggCapabilityRoot    ${((Date.now() - tc) / 1000).toFixed(1)}s  vkHash ${rootVk.hash}`);
tc = Date.now();
const attVk = (await DreggAttenuate.compile()).verificationKey;
say(`  [${stamp()}] DreggAttenuate         ${((Date.now() - tc) / 1000).toFixed(1)}s  vkHash ${attVk.hash}`);
tc = Date.now();
const rogueVk = (await DreggRogueAttenuate.compile()).verificationKey;
say(`  [${stamp()}] DreggRogueAttenuate    ${((Date.now() - tc) / 1000).toFixed(1)}s  vkHash ${rogueVk.hash}`);
say('    ^ THE ADVERSARY. Same signature, same honest ancestry derivation, NO narrowing check.');
tc = Date.now();
const gateVk = (await DreggCapabilityGate.compile()).verificationKey;
say(`  [${stamp()}] DreggCapabilityGate    ${((Date.now() - tc) / 1000).toFixed(1)}s  vkHash ${gateVk.hash}`);

const b64len = (s: string) => Buffer.from(s, 'base64').length;
say(`  root vk ${b64len(rootVk.data)} B   attenuator vk ${b64len(attVk.data)} B   gate vk ${b64len(gateVk.data)} B`);
say('  ⚑ THE ROOT AUTHORITY IS rootVk.hash. The gate holds that one Field and no key material.');
record.keys = { rootVkHash: rootVk.hash.toString(), attenuatorVkHash: attVk.hash.toString(), rogueVkHash: rogueVk.hash.toString(), gateVkHash: gateVk.hash.toString() };

// ═════════════════════════════════════════════════════════════════════════════ 4. produce real proofs

step('4. PROVE — a root capability, then TWO levels of narrowing, neither involving the issuer');

const ROOT_MASK = EFFECT_TRANSFER | EFFECT_SET_FIELD | EFFECT_EMIT_EVENT | EFFECT_GRANT_CAPABILITY;
const ROOT_CEILING = 1_000_000n; // bob_pre_balance from the real turn
const CHILD_MASK = FACET_TRANSFER_ONLY | EFFECT_EMIT_EVENT; // depth 1: keep transfer + events
const CHILD_CEILING = 1000n;
const GRAND_MASK = FACET_TRANSFER_ONLY; // depth 2: facet.rs:124 — send value, nothing else
const GRAND_CEILING = BigInt(TRANSFER_AMOUNT); // exactly what the real turn moved

const hx = (m: bigint) => `0x${m.toString(16).padStart(8, '0')}`;
say(`  root        mask ${hx(ROOT_MASK)}  ceiling ${ROOT_CEILING}`);
say(`  depth 1     mask ${hx(CHILD_MASK)}  ceiling ${CHILD_CEILING}`);
say(`  depth 2     mask ${hx(GRAND_MASK)}  ceiling ${GRAND_CEILING}   (FACET_TRANSFER_ONLY, the real amount)`);
say(`  is_facet_attenuation(root,d1)=${isFacetAttenuation(ROOT_MASK, CHILD_MASK)}  (d1,d2)=${isFacetAttenuation(CHILD_MASK, GRAND_MASK)}   (predicted, out of circuit)`);

tc = Date.now();
const rootProof = (await DreggCapabilityRoot.issue(SUBJECT_HI, SUBJECT_LO, Field(ROOT_MASK), UInt64.from(ROOT_CEILING))).proof;
say(`  [${stamp()}] root proof    ${((Date.now() - tc) / 1000).toFixed(1)}s  arity=${rootProof.maxProofsVerified}  authority=${rootProof.publicOutput.authority} (sentinel)`);

tc = Date.now();
const d1Proof = (await DreggAttenuate.attenuateRoot(
  DreggRootCapabilityProof.fromProof(rootProof as any),
  rootVk,
  Field(CHILD_MASK),
  UInt64.from(CHILD_CEILING),
)).proof;
say(`  [${stamp()}] depth-1 proof ${((Date.now() - tc) / 1000).toFixed(1)}s  arity=${d1Proof.maxProofsVerified}  authority=${d1Proof.publicOutput.authority}`);

tc = Date.now();
const d2Proof = (await DreggAttenuate.attenuateDelegated(
  DreggDelegatedCapabilityProof.fromProof(d1Proof as any),
  attVk,
  Field(GRAND_MASK),
  UInt64.from(GRAND_CEILING),
)).proof;
say(`  [${stamp()}] depth-2 proof ${((Date.now() - tc) / 1000).toFixed(1)}s  arity=${d2Proof.maxProofsVerified}  authority=${d2Proof.publicOutput.authority}`);

const authOk =
  d1Proof.publicOutput.authority.toString() === rootVk.hash.toString() &&
  d2Proof.publicOutput.authority.toString() === rootVk.hash.toString();
say(`  ⚑ both delegates carry authority == rootVk.hash : ${authOk}`);
say(`  ⚑ and depth 2 was produced under the ATTENUATOR's key (${attVk.hash.toString().slice(0, 12)}…), inheriting the root's authority unchanged.`);
if (!authOk) { say('  RED: the attenuator did not carry the root authority; every check below would be meaningless'); process.exit(1); }
record.chain = {
  rootMask: hx(ROOT_MASK), rootCeiling: String(ROOT_CEILING),
  depth1Mask: hx(CHILD_MASK), depth1Ceiling: String(CHILD_CEILING),
  depth2Mask: hx(GRAND_MASK), depth2Ceiling: String(GRAND_CEILING),
  authorityCarried: authOk,
};

// The prover-side refusals. These are the attenuator's OWN checks and they fire before any proof
// exists, which is the correct place for them: an amplifying delegation should be UNPRODUCIBLE,
// not merely unhonored.
step('5. PROVER-SIDE REFUSALS — an amplifying narrowing must be UNPRODUCIBLE, not merely unhonored');
const proverRefusals: Array<{ label: string; ok: boolean; msg: string }> = [];
const tryAtt = async (label: string, fn: () => Promise<unknown>) => {
  try {
    await fn();
    proverRefusals.push({ label, ok: false, msg: 'PROVED — the attenuator did NOT refuse' });
  } catch (e: any) {
    proverRefusals.push({ label, ok: true, msg: String(e?.message ?? e).split('\n')[0] });
  }
  const r = proverRefusals[proverRefusals.length - 1];
  say(`  ${r.ok ? 'REFUSED (good)' : '⚠ ACCEPTED (BAD)'}  ${r.label}\n      | ${r.msg}`);
};
await tryAtt('P1 widen the mask at depth 1 (add a bit the root does not hold: MINT)', () =>
  DreggAttenuate.attenuateRoot(DreggRootCapabilityProof.fromProof(rootProof as any), rootVk, Field(ROOT_MASK | (1n << 26n)), UInt64.from(CHILD_CEILING)),
);
await tryAtt('P2 raise the ceiling at depth 1 above the root (1_000_001)', () =>
  DreggAttenuate.attenuateRoot(DreggRootCapabilityProof.fromProof(rootProof as any), rootVk, Field(CHILD_MASK), UInt64.from(ROOT_CEILING + 1n)),
);
await tryAtt('P3 widen at depth 2: re-add SET_FIELD the depth-1 narrowing dropped', () =>
  DreggAttenuate.attenuateDelegated(DreggDelegatedCapabilityProof.fromProof(d1Proof as any), attVk, Field(GRAND_MASK | EFFECT_SET_FIELD), UInt64.from(GRAND_CEILING)),
);
await tryAtt('P4 raise the ceiling at depth 2 above depth 1 (1001)', () =>
  DreggAttenuate.attenuateDelegated(DreggDelegatedCapabilityProof.fromProof(d1Proof as any), attVk, Field(GRAND_MASK), UInt64.from(CHILD_CEILING + 1n)),
);
record.proverRefusals = proverRefusals;

// ═════════════════════════════════════════════════════════════════════════════ 6. deploy + exercise

step('6. DEPLOY the gate on a local chain with proofs ENABLED');
const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
Mina.setActiveInstance(Local);
const [payer] = Local.testAccounts;
const zkKey = PrivateKey.random();
const zkAddr = zkKey.toPublicKey();
const gate = new DreggCapabilityGate(zkAddr);

tc = Date.now();
{
  const tx = await Mina.transaction(payer, async () => {
    AccountUpdate.fundNewAccount(payer);
    await gate.deploy({ rootAuthority: rootVk.hash, attenuatorProgram: attVk.hash, subjectHi: SUBJECT_HI, subjectLo: SUBJECT_LO });
  });
  await tx.prove();
  await tx.sign([payer.key, zkKey]).send();
}
say(`  [${stamp()}] deployed in ${((Date.now() - tc) / 1000).toFixed(1)}s at ${zkAddr.toBase58()}`);
say(`  rootAuthority     = ${gate.rootAuthority.get()}   (which capability TREE)`);
say(`  attenuatorProgram = ${gate.attenuatorProgram.get()}   (which narrowing RULE)`);
say(`  subject           = ${ALICE_CELL}`);

type Case = {
  id: string;
  want: 'GREEN' | 'RED';
  aimedAt: string;
  via: 'direct' | 'delegated';
  proof: any;
  vk: VerificationKey;
  effectBit: bigint;
  amount: bigint;
};
const results: Array<{ id: string; want: string; aimedAt: string; got: 'ACCEPTED' | 'REFUSED'; ms: number; msg: string; chain?: string }> = [];

async function run(c: Case) {
  const t = Date.now();
  let got: 'ACCEPTED' | 'REFUSED';
  let msg = '';
  let chain: string | undefined;
  try {
    const tx = await Mina.transaction(payer, async () => {
      if (c.via === 'direct') {
        await gate.exerciseDirect(DreggRootCapabilityProof.fromProof(c.proof) as any, c.vk, Field(c.effectBit), UInt64.from(c.amount), TURN_HI, TURN_LO);
      } else {
        await gate.exerciseDelegated(DreggDelegatedCapabilityProof.fromProof(c.proof) as any, c.vk, Field(c.effectBit), UInt64.from(c.amount), TURN_HI, TURN_LO);
      }
    });
    await tx.prove();
    await tx.sign([payer.key]).send();
    got = 'ACCEPTED';
    chain = gate.receiptChain.get().toString();
  } catch (e: any) {
    got = 'REFUSED';
    msg = String(e?.message ?? e).split('\n').slice(0, 3).join(' / ');
  }
  results.push({ id: c.id, want: c.want, aimedAt: c.aimedAt, got, ms: Date.now() - t, msg, chain });
  const expected = got === (c.want === 'GREEN' ? 'ACCEPTED' : 'REFUSED');
  say(`  [${stamp()}] ${c.id}`);
  say(`      ${c.want.padEnd(5)} -> ${got.padEnd(8)} ${expected ? 'as expected' : '⚠ NOT AS EXPECTED'}   (${((Date.now() - t) / 1000).toFixed(1)}s)  [aimed at: ${c.aimedAt}]`);
  if (msg) say(`      | ${msg}`);
  if (chain) say(`      | receiptChain ${chain}, turnsHonored ${gate.turnsHonored.get()}`);
}

step('7. GREEN — the gate must honor these');
await run({ id: 'G1 ⚑ DELEGATED depth 1: narrowed capability, key the gate has NEVER seen, TRANSFER 100', want: 'GREEN', aimedAt: 'the whole claim', via: 'delegated', proof: d1Proof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });
say(`      ^ presented under vkHash ${attVk.hash} — the gate holds ${rootVk.hash}`);
await run({ id: 'G2 ⚑ DELEGATED depth 2: narrowed twice, TRANSFER 100 (exactly its ceiling)', want: 'GREEN', aimedAt: 'attenuation composes; one arity-1 slot serves every depth', via: 'delegated', proof: d2Proof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: GRAND_CEILING });
await run({ id: 'G3 DIRECT: the root\'s own capability, TRANSFER 100', want: 'GREEN', aimedAt: 'the arity-0 slot and the direct branch', via: 'direct', proof: rootProof, vk: rootVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });
await run({ id: 'G4 DIRECT: SET_FIELD — the root HOLDS this bit', want: 'GREEN', aimedAt: 'pairs with R1: the root may do what the delegate may not', via: 'direct', proof: rootProof, vk: rootVk, effectBit: EFFECT_SET_FIELD, amount: 1n });
await run({ id: 'G5 DELEGATED depth 1: EMIT_EVENT — depth 1 KEPT this bit, depth 2 dropped it', want: 'GREEN', aimedAt: 'pairs with R2: the same bit at two depths', via: 'delegated', proof: d1Proof, vk: attVk, effectBit: EFFECT_EMIT_EVENT, amount: 1n });

step('8. RED — the gate must refuse these, and each is aimed at ONE conjunct');
await run({ id: 'R1 ⚑ ATTENUATION: delegate exercises SET_FIELD, which the narrowing DROPPED', want: 'RED', aimedAt: 'is_effect_permitted / facet.rs:160 — pairs with G4', via: 'delegated', proof: d1Proof, vk: attVk, effectBit: EFFECT_SET_FIELD, amount: 1n });
await run({ id: 'R2 ⚑ ATTENUATION AT DEPTH 2: EMIT_EVENT, which the SECOND narrowing dropped', want: 'RED', aimedAt: 'the same conjunct one level deeper — pairs with G5', via: 'delegated', proof: d2Proof, vk: attVk, effectBit: EFFECT_EMIT_EVENT, amount: 1n });
await run({ id: 'R3 BUDGET: depth 2 transfers 101, one over its narrowed ceiling of 100', want: 'RED', aimedAt: 'FacetConstraint::MaxTransferAmount / facet.rs:355', via: 'delegated', proof: d2Proof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: GRAND_CEILING + 1n });
await run({ id: 'R4 BUDGET at the root: 1_000_001, one over ITS ceiling', want: 'RED', aimedAt: 'the same conjunct, showing the root is bounded too', via: 'direct', proof: rootProof, vk: rootVk, effectBit: EFFECT_TRANSFER, amount: ROOT_CEILING + 1n });
await run({ id: 'R5 FACET: root exercises MINT, a bit nobody in this chain holds', want: 'RED', aimedAt: 'is_effect_permitted, hit conjunct', via: 'direct', proof: rootProof, vk: rootVk, effectBit: 1n << 26n, amount: 1n });

// R6 — the bent key. This is the control that shows the IN-CIRCUIT path is strictly stronger than
// the chain's ingest: Mina's GraphQL door accepts a lying {data, hash} pair (MEASURED, see
// ForeignVerificationKey.ts §5); o1js's `assertEquals` at zkprogram.js:561 does not.
await run({ id: 'R6 ⚑ BENT KEY: the delegate\'s real bytes with hash+1 — the pair Mina\'s JSON ingest ACCEPTS', want: 'RED', aimedAt: 'o1js zkprogram.js:561 "Provided VerificationKey hash not correct"', via: 'delegated', proof: d1Proof, vk: new VerificationKey({ data: attVk.data, hash: attVk.hash.add(1) }), effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });
await run({ id: 'R7 WRONG KEY: the delegate\'s proof under the ROOT\'s key (both keys real and consistent)', want: 'RED', aimedAt: 'Pickles side-loaded verification itself', via: 'delegated', proof: d1Proof, vk: rootVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });

// R8 — the P2-1 audit fix. A zero mask IS a valid attenuation (0 & p == 0) so this capability is
// producible; it must then permit NOTHING. facet.rs:154-159 records that `Some(0)` used to read as
// "unrestricted", which made a maximally-faceted-looking capability unrestricted.
step('9. RED — the P2-1 deny-all rule (cell/src/facet.rs:154-166)');
// ⚑ THE CEILING IS KEPT AT THE PARENT'S. A mask-0 capability with a ceiling of 0 would be refused
// by the BUDGET conjunct as well, and a red that two conjuncts can explain isolates neither. This
// one leaves the budget wide open (1000, exercised at 1) so the ONLY thing that can refuse it is
// `Some(0) => false`.
const zeroProof = (await DreggAttenuate.attenuateDelegated(DreggDelegatedCapabilityProof.fromProof(d1Proof as any), attVk, Field(0n), UInt64.from(CHILD_CEILING))).proof;
say(`  a mask-0 narrowing PROVED (0 & parent == 0, so it IS a valid attenuation) with the parent's ceiling ${CHILD_CEILING} intact`);
say(`  authority=${zeroProof.publicOutput.authority.toString().slice(0, 12)}…  mask=0x00000000  ceiling=${zeroProof.publicOutput.maxTransfer}`);
await run({ id: 'R8 ⚑ ZERO MASK: a capability faceted to nothing must permit NOTHING', want: 'RED', aimedAt: 'the `Some(0) => false` conjunct ALONE, facet.rs:163 (the P2-1 fix); budget deliberately slack', via: 'delegated', proof: zeroProof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: 1n });

// ═════════════════════════════════════════════════════════════════════════════ the rogue narrowing
// ⚑ THE ATTACK AN EARLIER REVISION OF THE GATE WAS OPEN TO. `authority` is unforgeable, so a gate
// that pins only the root knows the chain DESCENDS from it — not that the descent NARROWED, because
// the program that computed the scope is the prover's choice. This is that program, compiled and
// PROVED, and everything printed below is read off its real public output.

step('9b. ⚑ THE ROGUE NARROWING — a real adversary program, and the pin that refuses it');
say('  DreggRogueAttenuate: verifies the root honestly, derives `authority` honestly, and simply');
say('  omits `is_facet_attenuation` and `is_at_least_as_tight`. Its output scope is whatever it likes.');
const rogueProof = (await DreggRogueAttenuate.forge(
  DreggRootCapabilityProof.fromProof(rootProof as any),
  rootVk,
  Field(EFFECT_ALL),
  UInt64.from((1n << 63n) - 1n),
)).proof;
const rc = rogueProof.publicOutput;
say(`  [${stamp()}] rogue proof PROVED  arity=${rogueProof.maxProofsVerified}  under vkHash ${rogueVk.hash}`);
say(`    authority   = ${rc.authority}`);
say(`    == the gate's rootAuthority : ${rc.authority.toString() === rootVk.hash.toString()}   <- conjunct 1a SATISFIED`);
say(`    subject     : hi/lo match the gate's : ${rc.subjectHi.toString() === SUBJECT_HI.toString() && rc.subjectLo.toString() === SUBJECT_LO.toString()}   <- conjunct 2 SATISFIED`);
say(`    effectMask  = 0x${BigInt(rc.effectMask.toString()).toString(16)}  (root held 0x${ROOT_MASK.toString(16)}) — AMPLIFIED, and no proof anywhere says otherwise`);
say(`    maxTransfer = ${rc.maxTransfer}  (root ceiling ${ROOT_CEILING}) — RAISED`);
say('  ⚑ SO EVERY OTHER CONJUNCT THE GATE CHECKS IS SATISFIED. Facet and budget would pass too,');
say('    because they are checked against the numbers this program wrote. The ONLY thing between');
say('    the gate and a total forgery of scope is the narrowing-rule pin.');
record.rogue = {
  vkHash: rogueVk.hash.toString(),
  authorityEqualsRoot: rc.authority.toString() === rootVk.hash.toString(),
  effectMask: `0x${BigInt(rc.effectMask.toString()).toString(16)}`,
  maxTransfer: rc.maxTransfer.toString(),
};
await run({ id: 'R11 ⚑ ROGUE NARROWING: EFFECT_ALL and a raised ceiling, honest ancestry', want: 'RED', aimedAt: 'vk.hash == attenuatorProgram — the narrowing-RULE pin, which is the only conjunct it fails', via: 'delegated', proof: rogueProof, vk: rogueVk, effectBit: EFFECT_SET_FIELD, amount: BigInt(TRANSFER_AMOUNT) });

// ═════════════════════════════════════════════════════════════════════════════ 10. revocation

step('10. REVOCATION — rotate the root, and watch the SAME exercises stop working');
say('  ⚑ this is the only revocation a bare vk-hash policy expresses: it revokes EVERYTHING at once.');
const chainBefore = gate.receiptChain.get().toString();
const honoredBefore = gate.turnsHonored.get().toString();
{
  const tx = await Mina.transaction(payer, async () => { await gate.rotateAuthority(Field(12345678901234567890n), attVk.hash); });
  await tx.prove();
  await tx.sign([payer.key, zkKey]).send();
}
say(`  [${stamp()}] rotated. rootAuthority = ${gate.rootAuthority.get()}`);
say(`  receiptChain survived the rotation unchanged: ${gate.receiptChain.get().toString() === chainBefore}`);
await run({ id: 'R9 AUTHORITY: the SAME delegated exercise as G1, after rotation', want: 'RED', aimedAt: 'cap.authority == rootAuthority', via: 'delegated', proof: d1Proof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });
await run({ id: 'R10 AUTHORITY: the SAME direct exercise as G3, after rotation', want: 'RED', aimedAt: 'the direct branch\'s vk.hash == rootAuthority conjunct', via: 'direct', proof: rootProof, vk: rootVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });
record.revocation = { chainSurvived: gate.receiptChain.get().toString() === chainBefore, turnsHonoredAtRotation: honoredBefore };

// ⚑ ROTATE BACK, and it is not tidiness. Stage 12 hands the gate a DREGG key; with the authority
// still rotated away, `cap.authority != rootAuthority` fires FIRST and the run would report a
// refusal that says nothing whatever about the dregg key. A red for the wrong reason measures
// nothing. (An earlier revision of this script did exactly that.)
{
  const tx = await Mina.transaction(payer, async () => { await gate.rotateAuthority(rootVk.hash, attVk.hash); });
  await tx.prove();
  await tx.sign([payer.key, zkKey]).send();
}
say(`  [${stamp()}] rotated BACK to ${gate.rootAuthority.get()} so stage 12 measures the KEY, not the rotation`);
await run({ id: 'G6 the delegated exercise works again after rotating back (the rotation was the cause)', want: 'GREEN', aimedAt: 'proves R9/R10 were about the authority and nothing else', via: 'delegated', proof: d1Proof, vk: attVk, effectBit: EFFECT_TRANSFER, amount: BigInt(TRANSFER_AMOUNT) });

// ═════════════════════════════════════════════════════════════════════════════ 11. the feature-flag pin

step('11. THE FEATURE-FLAG PIN — the second thing frozen at the verifier\'s compile time');
const flagMatrix: Array<{ circuit: string; flags: string; verdict: string; detail: string }> = [];
if (SKIP_FLAGS) {
  say('  --skip-flags: not measured this run');
} else {
  say('  o1js: "Only proofs that use the exact same composition of custom gates which were expected');
  say('  by Pickles can be verified using side loading." (proof.d.ts:141-142).');
  say('  ⚑ FOUR CELLS, not two. A one-sided probe would conclude the pin does not exist, or that it');
  say('    refuses everything. It does neither: it bites on the GATE TYPES a circuit emits.');
  const rootFlags = await FeatureFlags.fromZkProgram(DreggCapabilityRoot as any);
  const attFlags = await FeatureFlags.fromZkProgram(DreggAttenuate as any);
  const showFlags = (n: string, f: any) => say(`  ${n.padEnd(22)} ${Object.entries(f).filter(([, v]) => v !== false).map(([k, v]) => `${k}=${v}`).join(' ') || '(no flagged gate at all)'}`);
  showFlags('DreggCapabilityRoot', rootFlags);
  showFlags('DreggAttenuate', attFlags);
  record.circuitFlags = { root: rootFlags, attenuator: attFlags };

  for (const [circuit, proof, vk, MaybeCls, NoneCls] of [
    ['root (arity 0)', rootProof, rootVk, DreggRootCapabilityProof, DreggRootCapabilityProofAllNone],
    ['attenuator (arity 1)', d1Proof, attVk, DreggDelegatedCapabilityProof, DreggDelegatedCapabilityProofAllNone],
  ] as const) {
    for (const [label, Cls] of [['allMaybe', MaybeCls], ['allNone', NoneCls]] as const) {
      const probe = ZkProgram({
        name: `flag-probe-${circuit.split(' ')[0]}-${label}`,
        publicOutput: Field,
        methods: { go: { privateInputs: [Cls, VerificationKey], async method(p: any, v: VerificationKey) { p.verify(v); return { publicOutput: (p.publicOutput as DreggCapability).effectMask }; } } },
      });
      const t = Date.now();
      try {
        await probe.compile();
        await (probe as any).go((Cls as any).fromProof(proof as any), vk);
        flagMatrix.push({ circuit, flags: label, verdict: 'PROVED', detail: `${((Date.now() - t) / 1000).toFixed(1)}s` });
      } catch (e: any) {
        flagMatrix.push({ circuit, flags: label, verdict: 'REFUSED', detail: String(e?.message ?? e).split('\n').slice(0, 3).join(' / ') });
      }
      const r = flagMatrix[flagMatrix.length - 1];
      say(`  ${circuit.padEnd(22)} through featureFlags=${label.padEnd(9)} -> ${r.verdict.padEnd(8)} ${r.detail}`);
    }
  }
  const rootNone = flagMatrix.find((r) => r.circuit.startsWith('root') && r.flags === 'allNone');
  const attNone = flagMatrix.find((r) => r.circuit.startsWith('attenuator') && r.flags === 'allNone');
  const discriminates = rootNone?.verdict === 'PROVED' && attNone?.verdict === 'REFUSED';
  say(`  ⚑ MEASURED: allNone accepts the root (${rootNone?.verdict}) and ${attNone?.verdict === 'REFUSED' ? 'REFUSES' : 'ALSO ACCEPTS'} the attenuator.`);
  say('    `Gadgets.rangeCheck32` compiles to GENERIC gates and sets no flag; `Gadgets.and` emits');
  say('    `Xor16`, which does. So the pin is real and it bites on emitted GATE TYPES, not on');
  say('    "does this circuit use gadgets" — and a slot must be built for the exact composition.');
  if (!discriminates) say('  ⚠ the flag control did NOT move in both directions this run — do not cite the pin from it.');
  record.featureFlagPinDiscriminates = discriminates;
}
record.featureFlagPin = flagMatrix;

// ═════════════════════════════════════════════════════════════════════════════ 12. the dregg VK

step('12. THE DREGG VERIFICATION KEY — how far does it get into this same slot?');
say('  The Mina devnet holds a Side_loaded_verification_key DERIVED from Lean-emitted KimchiWrapMain');
say('  gates at B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm (devnet-foreign-vk-registration.json).');
say('  Its first two binprot bytes are `max_proofs_verified` and `actual_wrap_domain_size`, both');
say('  Pickles_base.Proofs_verified (N0|N1|N2) — i.e. EXACTLY the arity stage 2 showed is pinned.');
const headerOf = (label: string, data: string) => {
  const b = Buffer.from(data, 'base64');
  say(`    ${label.padEnd(36)} ${b.length} B   max_proofs_verified=N${b[0]}  actual_wrap_domain_size=N${b[1]}`);
  return b;
};
record.vkHeaders = {};
for (const [l, d] of [['o1js root capability VK', rootVk.data], ['o1js attenuator VK', attVk.data], ['o1js gate VK', gateVk.data]] as const) {
  const b = headerOf(l, d);
  record.vkHeaders[l] = { bytes: b.length, maxProofsVerified: b[0], actualWrapDomainSize: b[1] };
}

let dreggVkData: string | undefined;
if (WANT_DEVNET_VK) {
  const ENDPOINT = process.env.MINA_ENDPOINT ?? 'https://api.minascan.io/node/devnet/v1/graphql';
  say(`  fetching the registered key (READ ONLY, no transaction) from ${ENDPOINT}`);
  try {
    const q = `{ account(publicKey: "B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm") { verificationKey { verificationKey hash } } }`;
    const r = await fetch(ENDPOINT, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ query: q }) });
    const j: any = await r.json();
    dreggVkData = j?.data?.account?.verificationKey?.verificationKey;
    if (typeof dreggVkData === 'string') {
      const b = headerOf('DREGG KimchiWrapMain VK (devnet)', dreggVkData);
      const sha = createHash('sha256').update(b).digest('hex');
      say(`    sha256 ${sha}   on-chain hash ${j?.data?.account?.verificationKey?.hash}`);
      record.dreggVk = { bytes: b.length, maxProofsVerified: b[0], actualWrapDomainSize: b[1], sha256: sha, onChainHash: j?.data?.account?.verificationKey?.hash };
    } else {
      say(`    could not read a key off that account: ${JSON.stringify(j).slice(0, 300)}`);
    }
  } catch (e: any) {
    say(`    fetch failed (offline?): ${e?.message ?? e}`);
  }
} else {
  say('  (pass --devnet-vk to fetch the registered dregg key over GraphQL; read-only, no transaction)');
}

if (dreggVkData !== undefined && record.dreggVk !== undefined) {
  // ⚑ POINT THE GATE AT THE DREGG KEY FIRST, and this is not a workaround — it is candidate (b),
  // "a zkApp holding a dregg VK as an UPGRADEABLE side-loaded key", demonstrated on the real key.
  // The narrowing-rule pin is on-chain STATE, so the gate can be re-aimed at a foreign program
  // without redeploying and without moving its own verification key.
  //
  // ⚠ AND WITHOUT THIS THE MEASUREMENT IS WORTHLESS. With the pin still on the o1js attenuator, D1
  // stops at `vk.hash != attenuatorProgram` and reports nothing whatever about the dregg key — which
  // is exactly what the previous revision of this script did, one stanza after fixing the same
  // mistake for the authority conjunct.
  {
    const tx = await Mina.transaction(payer, async () => {
      await gate.rotateAuthority(rootVk.hash, Field(record.dreggVk.onChainHash));
    });
    await tx.prove();
    await tx.sign([payer.key, zkKey]).send();
  }
  say(`\n  [${stamp()}] gate re-aimed: attenuatorProgram = ${gate.attenuatorProgram.get()}`);
  say('  ⚑ that IS the upgradeable-side-loaded-key story, on the real dregg key: the narrowing rule');
  say('    is on-chain state, so the gate now names a Lean-derived program without a redeploy and');
  say('    without its own VK moving. The two COMPILE-TIME pins (arity, feature flags) do not move.');
  say('\n  Now hand it to the gate as the key for the exercise. Same slot, same method, real key,');
  say('  and its REAL on-chain hash — so the in-circuit data<->hash check (zkprogram.js:561) passes');
  say('  and the run reaches the side-loaded verification proper instead of stopping at a label.');
  say(`  ⚑ authority and narrowing-rule conjuncts both satisfied now, so neither can pre-empt this.`);
  await run({
    id: 'D1 the registered DREGG key, with its real hash, presented with the delegate\'s proof',
    want: 'RED',
    aimedAt: 'MEASUREMENT: where does a real dregg key stop in a real side-loaded slot?',
    via: 'delegated',
    proof: d1Proof,
    vk: new VerificationKey({ data: dreggVkData, hash: Field(record.dreggVk.onChainHash) }),
    effectBit: EFFECT_TRANSFER,
    amount: BigInt(TRANSFER_AMOUNT),
  });
  say('  ⚠ A MEASUREMENT, NOT A TEST. The proof is not a dregg proof, so a refusal was certain; what');
  say('    this reports is WHICH refusal — how far a dregg key gets. Getting past the data<->hash');
  say('    check to a `prevs_verified` / Pickles-verification failure means Mina PARSED the Lean-');
  say('    derived key, hashed it in-circuit, and admitted it into the slot; only the proof was');
  say('    foreign. A dregg PROOF for this slot does not exist — see the verdict.');
}

// ═════════════════════════════════════════════════════════════════════════════ 13. verdict

step('13. VERDICT');
const greens = results.filter((r) => r.want === 'GREEN');
const reds = results.filter((r) => r.want === 'RED' && !r.id.startsWith('D'));
const greensOk = greens.every((r) => r.got === 'ACCEPTED');
const redsOk = reds.every((r) => r.got === 'REFUSED');
const proverOk = proverRefusals.every((r) => r.ok);

say(`  GREEN cases : ${greens.filter((r) => r.got === 'ACCEPTED').length}/${greens.length} accepted`);
say(`  RED   cases : ${reds.filter((r) => r.got === 'REFUSED').length}/${reds.length} refused`);
say(`  prover-side : ${proverRefusals.filter((r) => r.ok).length}/${proverRefusals.length} refused`);
say(`  turnsHonored on chain: ${gate.turnsHonored.get()}   receiptChain ${gate.receiptChain.get()}`);

const CONTROLS_MOVED = greensOk && redsOk && proverOk;
record.results = results;
record.verdict = { greensOk, redsOk, proverOk, controlsMoved: CONTROLS_MOVED, turnsHonored: gate.turnsHonored.get().toString(), receiptChain: gate.receiptChain.get().toString() };
record.claim = CONTROLS_MOVED
  ? 'A Mina zkApp honored the exercise of a dregg capability narrowed TWICE without the issuer, under a verification key it had never seen, and refused the exercise each narrowing removed. What is verified is the ATTENUATION ALGEBRA (cell/src/facet.rs), not the dregg TURN — the turn is committed into the receipt chain and NOT verified.'
  : 'CONTROLS BROKEN — no claim.';
const OUT = path.join(HERE, '..', 'dregg-capability-gate-run.json');
writeFileSync(OUT, JSON.stringify(record, null, 2) + '\n');

say('');
if (CONTROLS_MOVED) {
  say('  DREGG-CAPABILITY-GATE: CONTROLS-MOVED-BOTH-WAYS');
  say('  A Mina zkApp honored the exercise of a dregg capability NARROWED TWICE without the issuer,');
  say('  under a verification key it had never seen, and refused the exercise each narrowing removed.');
} else {
  say('  DREGG-CAPABILITY-GATE: CONTROLS-BROKEN');
  say('  refusing to claim anything: a gate whose controls do not move in both directions means nothing.');
}
say('');
say('  ⚑ AT THE RESOLUTION IT HOLDS: what verified is the ATTENUATION ALGEBRA — a monotone chain of');
say('    narrowings from a named root, and an exercise inside the narrowest scope, over dregg\'s own');
say('    facet lattice. The dregg TURN is committed into the receipt and NOT verified');
say('    (DreggCapabilityGate.checkAndRecord step 5 names the missing line).');
say(`  record written to ${OUT}`);
say(`  total ${stamp()}`);
process.exit(CONTROLS_MOVED ? 0 : 1);
