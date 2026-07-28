// Emit a FRESH dregg-side Merkle root + authentication path, and cross-check it
// against the o1js twin before anything is deployed.
//
//   npm run devnet:emit-root
//
// ⚑ DIRECTION OF THE ARROW. The root and the path are produced by the DREGG-SIDE
// RUST HASHER (`circuit-prove/sketches/mina-pasta-hash-probe`, `mina-poseidon`
// over Pasta Fp) — Rust EMITS, the Mina circuit only VERIFIES. That ordering is
// the whole point: with a committed fixture root one could object that the o1js
// side is replaying a constant it produced itself (which is exactly the
// provenance caveat on `src/rust-gold-vectors.ts`). Here the leaves carry a
// deploy-time timestamp and a 128-bit random nonce, so the root did not and
// could not exist before this run.
//
// ⚑ WHAT THE LEAVES ARE, PLAINLY. They are a domain tag, the repo commit being
// deployed, a timestamp, and a nonce. They are NOT live dregg cell state —
// nothing in dregg emits a Mina-Poseidon root over real state today. So this
// demonstrates the two systems agreeing on a COMMITMENT SCHEME over freshly
// emitted data, not Mina verifying a dregg state root.

import { Field } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { compress, sparsePath } from '../src/DreggPoseidonAttestation.js';

export const ROOT_JSON = resolve(process.cwd(), 'devnet-root.json');

/** Depth of the attested tree — must equal `ATTEST_DEPTH`. */
export const DEPTH = 32;
/** The leaf the zkApp will be asked to open: the repo commit. */
export const ATTEST_INDEX = 1;

export type EmittedRoot = {
  emitter: string;
  emittedAt: string;
  gitCommit: string;
  depth: number;
  leafIndex: number;
  leafMeaning: string[];
  leaves: string[];
  leaf: string;
  siblings: string[];
  isRight: boolean[];
  root: string;
};

/** What the dregg-side probe's `merkle` subcommand prints. */
export type RustEmission = {
  depth: number;
  leafIndex: number;
  leaf: string;
  siblings: string[];
  isRight: boolean[];
  nodes: string[];
  root: string;
};

export function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml'))) {
    throw new Error(
      `the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR. ` +
        'Run this from bridge/mina-zkapp (npm run devnet:emit-root).',
    );
  }
  return d;
}

/** ASCII -> a single Pasta field element, big-endian. 20 bytes << 254 bits. */
function tagHex(s: string): string {
  return '0x' + Buffer.from(s, 'ascii').toString('hex');
}

/** The canonical field-element rendering both sides compare on. */
export const hex = (f: Field) => '0x' + f.toBigInt().toString(16).padStart(64, '0');

/**
 * The four leaves, and why each is there. Two of them (`Date.now()` and a
 * 128-bit nonce) make the emitted root non-precomputable, which is the whole
 * reason this beats a committed fixture.
 */
export function freshLeaves(dir: string): {
  leaves: string[];
  leafMeaning: string[];
  gitCommit: string;
} {
  // Which tree's HEAD the leaf names. Normally the probe's own directory, i.e.
  // this repository. `DREGG_ATTEST_GIT_DIR` exists because the gate's self-test
  // copies the probe crate into a scratch directory to inject faults, and a
  // copy is not a git repository — the leaf should still name the tree the copy
  // was taken from, which is what makes it the same measurement.
  const gitCommit = execFileSync('git', ['rev-parse', 'HEAD'], {
    cwd: process.env.DREGG_ATTEST_GIT_DIR ?? dir,
    encoding: 'utf8',
  }).trim();
  return {
    gitCommit,
    leaves: [
      tagHex('dregg/mina-attest/v1'), // domain separation
      '0x' + gitCommit, //               the repo commit being deployed
      String(Date.now()), //             freshness
      '0x' + randomBytes(16).toString('hex'), // unpredictability
    ],
    leafMeaning: [
      'domain tag "dregg/mina-attest/v1"',
      'git HEAD of the emitting tree',
      'emission timestamp (unix ms)',
      '128-bit random nonce',
    ],
  };
}

/** Run the dregg-side hasher's `merkle` subcommand. Rust EMITS; nothing here
 *  computes the root on the o1js side first. */
export function runProbeMerkle(
  dir: string,
  depth: number,
  leafIndex: number,
  leaves: string[],
): RustEmission {
  const out = execFileSync(
    'cargo',
    ['run', '--offline', '--quiet', '--', 'merkle', String(depth), String(leafIndex), ...leaves],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 24 },
  );
  return JSON.parse(out) as RustEmission;
}

/**
 * The cross-implementation agreement, elementwise. Rust/arkworks
 * `mina-poseidon` and o1js's OCaml-compiled-to-WASM sponge are independent
 * implementations; agreeing on the root, all `depth` sibling slots and every
 * `isRight` bit is a real check over data neither side had seen before.
 *
 * THROWS on the first divergence, naming the level — so a caller can also use
 * it as the negative polarity by feeding it a doctored emission.
 */
export function crossCheckEmission(
  leaves: string[],
  leafIndex: number,
  depth: number,
  rust: RustEmission,
): void {
  // `BigInt` parses both the `0x…` and the decimal literals the probe accepts.
  const o1 = sparsePath(leaves.map((l) => Field(BigInt(l))), leafIndex, depth);
  if (hex(o1.root) !== rust.root) {
    throw new Error(`ROOT DIVERGENCE: o1js ${hex(o1.root)} != rust ${rust.root}`);
  }
  for (let i = 0; i < depth; i++) {
    if (hex(o1.path.siblings[i]) !== rust.siblings[i]) {
      throw new Error(
        `SIBLING DIVERGENCE at level ${i}: o1js ${hex(o1.path.siblings[i])} != rust ${rust.siblings[i]}`,
      );
    }
    if (o1.path.isRight[i].toBoolean() !== rust.isRight[i]) {
      throw new Error(`isRight DIVERGENCE at level ${i}`);
    }
  }
  // The emitted path must actually fold to the emitted root under the SAME
  // `compress` the circuit calls — a path that does not reach its own root
  // cannot be emitted without this catching it.
  let cur = Field(BigInt(rust.leaf));
  for (let i = 0; i < depth; i++) {
    const sib = Field(BigInt(rust.siblings[i]));
    cur = rust.isRight[i] ? compress(sib, cur) : compress(cur, sib);
  }
  if (hex(cur) !== rust.root) {
    throw new Error('the emitted path does not fold to the emitted root');
  }
}

function main() {
  console.log('=== emit a fresh dregg-side Pasta root ===');
  const dir = probeDir();
  const { leaves, leafMeaning, gitCommit } = freshLeaves(dir);

  console.log(`  probe    : ${dir}`);
  console.log(`  commit   : ${gitCommit}`);
  console.log('  leaves   :');
  leaves.forEach((l, i) => console.log(`     [${i}] ${l}  (${leafMeaning[i]})`));

  // --- the dregg side EMITS -------------------------------------------------
  const rust = runProbeMerkle(dir, DEPTH, ATTEST_INDEX, leaves);
  console.log(`\n  rust root: ${rust.root}`);

  // --- the o1js side must REPRODUCE it, elementwise -------------------------
  // A divergence here stops the deployment before a single fee is spent.
  crossCheckEmission(leaves, ATTEST_INDEX, DEPTH, rust);
  console.log('  ✓ o1js reproduces the Rust root and all 32 siblings, bit-for-bit');
  console.log('  ✓ the emitted path folds to the emitted root');

  const record: EmittedRoot = {
    emitter: 'circuit-prove/sketches/mina-pasta-hash-probe (mina-poseidon, Pasta Fp)',
    emittedAt: new Date().toISOString(),
    gitCommit,
    depth: DEPTH,
    leafIndex: ATTEST_INDEX,
    leafMeaning,
    leaves,
    leaf: rust.leaf,
    siblings: rust.siblings,
    isRight: rust.isRight,
    root: rust.root,
  };
  writeFileSync(ROOT_JSON, JSON.stringify(record, null, 2) + '\n');
  console.log(`\n  wrote ${ROOT_JSON}`);
  console.log(`  root: ${rust.root}`);
  console.log(`  leaf: ${rust.leaf}  (the git commit, index ${ATTEST_INDEX})`);
}

// Only emit (and WRITE devnet-root.json) when this module is what was invoked.
// `probe-gate.ts` imports the helpers above; a bare `main()` here would have it
// silently overwrite the committed deployment record on every gate run.
if (process.argv[1]?.endsWith('devnet-emit-root.js')) main();
