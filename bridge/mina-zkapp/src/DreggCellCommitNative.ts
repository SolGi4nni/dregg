import { Field, Provable, ZkProgram } from 'o1js';
import { RawGates, assertRawGatesAvailable } from './kimchi-raw-gates.js';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

// ---------------------------------------------------------------------------
// ROUTE B, WITH THE COMMITMENT BINDING — the 4 GROUP-4 hash sites.
//
// ⚑ SAY THE SUBSTRATE OUT LOUD. There is NO AIR, no gadget and no permutation
// authored in this file. Every constraint is read out of
// `src/generated/kimchi-cellcommit-b.json`, the verbatim output of
// `Dregg2.Circuit.Emit.KimchiCellCommit` — where the four `hash_4_to_1`
// sub-circuits are `KimchiPoseidon2.permGen` (a Lean `def`-generator folded over
// the imported round constants; 141 S-boxes, none spelled out) and the wiring
// between them is `def`-generated from the DEPLOYED site list. This module is a
// TRANSCRIBER: it walks the emitted instruction stream and calls
// `Gates.generic` / `Gates.rangeCheck0` with the columns and coefficients Lean
// produced, and it witnesses the vector Lean computed. It contains no dregg
// semantics and no witness algorithm of its own.
//
// ⚑ WHAT THIS ESTABLISHES, AND WHAT IT DOES NOT.
//
//   ESTABLISHES: this (pre, post) pair is a valid `incrementNonceA` transition
//   under dregg's semantics AND the post-state 13-tuple is the pre-image, under
//   the deployed GROUP-4 `hash_4_to_1` tree, of the felt in the `state_commit`
//   column — i.e. these are a real dregg CELL, not two bare tuples. The Lean
//   theorem over the very rows replayed here is
//   `KimchiCellCommit.routeB_forces_cell_transition`.
//
//   DOES NOT ESTABLISH: that dregg's chain CONTAINS this cell or this
//   transition. Route B is a cell-transition checker, not a membership checker.
//   A well-formed transition of a cell that never existed passes: invent a
//   13-tuple, hash it honestly, present the pair. Membership is route A's job
//   (`DreggProofVerify`), and B is not a cheaper substitute for it. The
//   commitment binding narrows nothing about that.
// ---------------------------------------------------------------------------

const __dirname_ = dirname(fileURLToPath(import.meta.url));

/** A generic sub-gate: `cl*w[l] + cr*w[r] + co*w[o] + cm*w[l]*w[r] + cc = 0`.
 *  Coefficients are DECIMAL STRINGS — the reduction's `p*2^(53i)` coefficients
 *  exceed 2^53 and a JSON number would silently round them. */
export type EmittedGen = {
  k: 'g';
  l: number;
  r: number;
  o: number;
  cl: string;
  cr: string;
  co: string;
  cm: string;
  cc: string;
};

/** A standalone 64-bit `RangeCheck0` row: `w[0]` is the checked value, `w[1..6]`
 *  the six 12-bit limbs, `w[7..14]` the eight 2-bit crumbs. */
export type EmittedRc0 = { k: 'r'; w: number[] };

export type EmittedOp = EmittedGen | EmittedRc0 | { k: 'z' };

export type CellCommitProgram = {
  air: string;
  source: string;
  firstFreshVar: number;
  ops: number;
  siteRows: number;
  commitRows: number;
  routeBRows: number;
  vars: number;
  cols: Record<string, number>;
  siteInCols: number[][];
  siteDigestCols: number[];
  honestCommit: string;
  ops_: EmittedOp[];
  witness: string[];
};

function artifactPath(name: string): string {
  let d = __dirname_;
  for (let i = 0; i < 8; i++) {
    try {
      readFileSync(resolve(d, 'package.json'));
      return resolve(d, `src/generated/${name}`);
    } catch {
      d = resolve(d, '..');
    }
  }
  throw new Error(`route-B: could not locate ${name} from the package root`);
}

export function loadCellCommit(): CellCommitProgram {
  const prog = JSON.parse(
    readFileSync(artifactPath('kimchi-cellcommit-b.json'), 'utf8')
  ) as CellCommitProgram;
  if (prog.ops_.length !== prog.ops) {
    throw new Error(`emitted artifact inconsistent: ops=${prog.ops} but ops_=${prog.ops_.length}`);
  }
  if (prog.witness.length !== prog.vars) {
    throw new Error(
      `emitted artifact inconsistent: vars=${prog.vars} but witness=${prog.witness.length}`
    );
  }
  return prog;
}

export const COMMIT = loadCellCommit();

const P = Field.ORDER;

/** A signed decimal coefficient as a field element. Emitted coefficients run to
 *  ~2^100 (the reduction's `p * 2^(53i)`), so this reduces rather than assuming
 *  smallness, and maps negatives to their additive inverse. */
export function coeff(c: string): bigint {
  const b = BigInt(c) % P;
  return b < 0n ? b + P : b;
}

// ===========================================================================
// 1. The TRANSCRIBER.
// ===========================================================================

/** Replay the emitted instruction stream inside the circuit. `vars` must already
 *  hold circuit variables for every index the stream mentions. */
export function replayCommit(prog: CellCommitProgram, vars: Field[]): void {
  assertRawGatesAvailable();
  for (const op of prog.ops_) {
    if (op.k === 'g') {
      RawGates.generic(
        {
          left: coeff(op.cl),
          right: coeff(op.cr),
          out: coeff(op.co),
          mul: coeff(op.cm),
          const: coeff(op.cc),
        },
        { left: vars[op.l], right: vars[op.r], out: vars[op.o] }
      );
    } else if (op.k === 'r') {
      const w = op.w;
      RawGates.rangeCheck0(
        vars[w[0]],
        [vars[w[1]], vars[w[2]], vars[w[3]], vars[w[4]], vars[w[5]], vars[w[6]]],
        [
          vars[w[7]],
          vars[w[8]],
          vars[w[9]],
          vars[w[10]],
          vars[w[11]],
          vars[w[12]],
          vars[w[13]],
          vars[w[14]],
        ],
        false
      );
    } else {
      RawGates.zero(vars[0], vars[0], vars[0]);
    }
  }
}

// ===========================================================================
// 2. The WITNESS — Lean's, verbatim, with a named mutation for the tampers.
// ===========================================================================

export type WitnessMutation = { var: number; value: bigint };

function fmod(x: bigint): bigint {
  const r = x % P;
  return r < 0n ? r + P : r;
}

/** The honest witness Lean computed, with zero or more single-variable
 *  substitutions. Nothing here recomputes a witness: a tamper is a NAMED
 *  substitution into Lean's own vector, so the only difference between the
 *  honest run and a tampered one is the value the prover asserts. */
export function witnessVector(prog: CellCommitProgram, muts: WitnessMutation[] = []): bigint[] {
  const w = prog.witness.map((s) => fmod(BigInt(s)));
  for (const m of muts) w[m.var] = fmod(m.value);
  return w;
}

/** Evaluate the emitted generic sub-gates at a witness and report which fail.
 *  This is the SEPARATION instrument: it is run over the ARITHMETIC emission and
 *  over the COMMITMENT emission independently, so a tamper can be shown to leave
 *  the arithmetic intact while breaking the binding. */
export function violatedGens(ops: EmittedOp[], w: bigint[]): number[] {
  const bad: number[] = [];
  const rd = (i: number): bigint => w[i] ?? 0n;
  ops.forEach((op, idx) => {
    if (op.k !== 'g') return;
    const body =
      BigInt(op.cl) * rd(op.l) +
      BigInt(op.cr) * rd(op.r) +
      BigInt(op.co) * rd(op.o) +
      BigInt(op.cm) * rd(op.l) * rd(op.r) +
      BigInt(op.cc);
    if (fmod(body) !== 0n) bad.push(idx);
  });
  return bad;
}

// ===========================================================================
// 3. The ZkProgram.
// ===========================================================================
//
// PUBLIC INPUT is ONE field element: the CLAIMED cell commitment. The circuit
// (a) replays the emitted GROUP-4 sub-circuits over the witnessed vector, which
// computes `hash_4_to_1`-of-`hash_4_to_1` of the after-state block and pins it
// into the `state_commit` column, and (b) asserts that column equals the claim.
//
// So a prover who presents a (pre, post) pair whose arithmetic is perfectly
// valid but whose claimed commitment is not the pre-image of `post` cannot
// satisfy the pin. That refusal is the whole point of this file, and
// `scripts/cellcommit-native.ts` exercises it against a real `prove()`.

let CURRENT: bigint[] = [];

/** Install the witness the next proof will use. */
export function useWitness(w: bigint[]): void {
  CURRENT = w;
}

const STATE_COMMIT_VAR = COMMIT.cols.stateCommit;

function witnessAndReplay(prog: CellCommitProgram): Field[] {
  const n = prog.vars;
  const vars = Provable.witness(Provable.Array(Field, n), () =>
    Array.from({ length: n }, (_, i) => Field(CURRENT[i] ?? 0n))
  );
  replayCommit(prog, vars);
  return vars;
}

/** Rows of the emitted commitment binding alone — the number
 *  `KimchiCellCommit.commitRowCount` predicts. */
export async function commitRows(): Promise<number> {
  useWitness(witnessVector(COMMIT));
  const cs = await Provable.constraintSystem(() => {
    witnessAndReplay(COMMIT);
  });
  return cs.rows;
}

export const DreggCellCommitNative = ZkProgram({
  name: 'dregg-cellcommit-native-b',
  publicInput: Field,
  methods: {
    check: {
      privateInputs: [],
      async method(claimedCommit: Field) {
        const vars = witnessAndReplay(COMMIT);
        // THE BINDING: the column the emitted GROUP-4 tree lands on IS the claim.
        vars[STATE_COMMIT_VAR].assertEquals(claimedCommit);
      },
    },
  },
});
