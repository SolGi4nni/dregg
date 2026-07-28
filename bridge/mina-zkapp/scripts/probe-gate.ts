// The DREGG-SIDE (Rust) leg of the Mina attestation gate.
//
//   npm run probe        (= npm run build && node dist/scripts/probe-gate.js)
//
// WHY THIS EXISTS. `scripts/check-mina-attestation.sh` was written Node-only —
// no cargo, no Lean — and said so. The consequence, unstated at the time, is
// that the EMITTING side of the bridge ran in no gate at all: the Rust probe's
// own tests (`circuit-prove/sketches/mina-pasta-hash-probe`, five of them,
// including the depth-32 `sparse_path_folds_through_the_gold_depth2_root`) were
// reachable only by someone typing `cargo test` by hand, and the `merkle`
// subcommand that actually produces the deployed root — fresh leaves, a
// depth-32 sparse path, the elementwise cross-check against o1js — ran ONLY
// inside `npm run devnet:emit-root`, which needs devnet keys and is deliberately
// not gated. So the half of the bridge that PRODUCES the attested object could
// not go red. That is this repo's gating-defaults-to-silence class: nothing was
// broken, and nothing was watching either.
//
// This leg runs both, offline:
//
//   [P1] `cargo test --locked` in the probe crate. Fails, never skips: a
//        missing cargo is a gate failure, like a missing node in the JS leg.
//   [P2] the `merkle` subcommand end to end, on leaves that CANNOT have been
//        precomputed (domain tag + git HEAD + millisecond timestamp + 128-bit
//        nonce) — Rust emits, o1js must reproduce the root, all 32 siblings and
//        every isRight bit elementwise, and the emitted path must fold to the
//        emitted root. This is exactly what `devnet:emit-root` does before a
//        deployment, minus the network and minus writing devnet-root.json.
//   [P3] the polarities that keep [P2] from being vacuous: a doctored sibling,
//        a doctored root and a doctored isRight bit must each be CAUGHT, and
//        two emissions with different nonces must differ (an emitter that
//        returned a constant would sail through an agreement check).
//
// No network. ~15s warm, dominated by the first cargo build.

import { execFileSync } from 'node:child_process';
import {
  ATTEST_INDEX,
  DEPTH,
  crossCheckEmission,
  freshLeaves,
  probeDir,
  runProbeMerkle,
  type RustEmission,
} from './devnet-emit-root.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
function check(cond: boolean, good: string, bad: string) {
  if (cond) ok(good);
  else fail(bad);
}
const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';

/** Run the cross-check and report whether it REFUSED. Used for the polarities:
 *  a comparison that cannot fail is not a comparison. */
function refuses(leaves: string[], rust: RustEmission): string | null {
  try {
    crossCheckEmission(leaves, ATTEST_INDEX, DEPTH, rust);
    return null;
  } catch (e) {
    return e instanceof Error ? e.message : String(e);
  }
}

/** A structured copy with one field bent. */
function bend(rust: RustEmission, f: (r: RustEmission) => void): RustEmission {
  const copy = JSON.parse(JSON.stringify(rust)) as RustEmission;
  f(copy);
  return copy;
}

async function main() {
  console.log('=== dregg-side (Rust) emitting leg ===');
  const dir = probeDir();
  console.log(`    probe: ${dir}\n`);

  // -------------------------------------------------------------------------
  console.log('[P1] the probe crate’s own tests');
  let t = Date.now();
  try {
    const out = execFileSync('cargo', ['test', '--locked', '--quiet'], {
      cwd: dir,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
      maxBuffer: 1 << 24,
    });
    const passed = /(\d+) passed/.exec(out)?.[1];
    check(
      passed !== undefined && Number(passed) >= 5,
      `cargo test: ${passed ?? '?'} tests passed in ${secs(t)}`,
      `cargo test reported ${passed ?? 'no'} passing tests; expected >= 5 ` +
        '(a narrowed run is not a pass)',
    );
  } catch (e) {
    const err = e as { stdout?: string; stderr?: string; message?: string };
    console.error(err.stdout ?? '');
    console.error(err.stderr ?? '');
    fail(`cargo test failed in ${dir}: ${err.message ?? e}`);
  }

  // -------------------------------------------------------------------------
  console.log('\n[P2] the `merkle` subcommand, on leaves that cannot be precomputed');
  const { leaves, leafMeaning, gitCommit } = freshLeaves(dir);
  leaves.forEach((l, i) => console.log(`     [${i}] ${l}  (${leafMeaning[i]})`));

  t = Date.now();
  const rust = runProbeMerkle(dir, DEPTH, ATTEST_INDEX, leaves);
  console.log(`     rust root: ${rust.root}  (${secs(t)})`);

  check(
    rust.depth === DEPTH && rust.leafIndex === ATTEST_INDEX && rust.siblings.length === DEPTH,
    `the probe emitted a depth-${DEPTH} path for leaf index ${ATTEST_INDEX}`,
    `the probe emitted depth=${rust.depth} index=${rust.leafIndex} with ` +
      `${rust.siblings.length} siblings`,
  );
  check(
    BigInt(rust.leaf) === BigInt(leaves[ATTEST_INDEX]) &&
      BigInt(rust.leaf) === BigInt('0x' + gitCommit),
    'the opened leaf is the git HEAD of the emitting tree',
    `the opened leaf ${rust.leaf} is not the git commit 0x${gitCommit}`,
  );

  const divergence = refuses(leaves, rust);
  check(
    divergence === null,
    'o1js reproduces the Rust root, all 32 siblings and every isRight bit, and the ' +
      'path folds to its own root',
    `the emitting side and o1js disagree: ${divergence}`,
  );

  // -------------------------------------------------------------------------
  console.log('\n[P3] the cross-check is discriminating (it can say no)');
  check(
    refuses(leaves, bend(rust, (r) => (r.root = '0x' + (BigInt(r.root) + 1n).toString(16)))) !==
      null,
    'a doctored ROOT is caught',
    'a doctored root passed the cross-check (the comparison is vacuous)',
  );
  const level = 7;
  check(
    refuses(
      leaves,
      bend(
        rust,
        (r) => (r.siblings[level] = '0x' + (BigInt(r.siblings[level]) + 1n).toString(16)),
      ),
    ) !== null,
    `a doctored SIBLING at level ${level} is caught`,
    'a doctored sibling passed the cross-check (the comparison is vacuous)',
  );
  check(
    refuses(leaves, bend(rust, (r) => (r.isRight[0] = !r.isRight[0]))) !== null,
    'a doctored isRight BIT is caught',
    'a doctored isRight bit passed the cross-check (the comparison is vacuous)',
  );

  // An emitter that ignored its input would agree with an o1js side that also
  // ignored it. Two emissions differing only in the nonce must differ.
  const second = freshLeaves(dir);
  const rust2 = runProbeMerkle(dir, DEPTH, ATTEST_INDEX, second.leaves);
  check(
    rust2.root !== rust.root,
    'a second emission with a fresh nonce produces a DIFFERENT root',
    'two emissions with different leaves produced the same root (the emitter is constant)',
  );
  check(refuses(second.leaves, rust2) === null, 'and it cross-checks too', 'the second emission diverges');
  check(
    refuses(leaves, rust2) !== null,
    'and the first run’s leaves do NOT open under the second run’s root',
    'the second root accepted the first run’s leaves (the check ignores the leaves)',
  );
}

main()
  .then(() => {
    console.log(
      '\n=== PROBE PASS === (the dregg side EMITS; o1js reproduces it elementwise)\n',
    );
  })
  .catch((e) => {
    console.error(e instanceof Error ? e.message : e);
    console.error('\n=== PROBE FAILED ===\n');
    process.exit(1);
  });
