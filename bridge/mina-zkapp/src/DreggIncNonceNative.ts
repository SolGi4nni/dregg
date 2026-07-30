import { Field, Gadgets, Poseidon, Provable, Struct, ZkProgram } from 'o1js';
import { RawGates, assertRawGatesAvailable } from './kimchi-raw-gates.js';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

// ---------------------------------------------------------------------------
// ROUTE B — dregg's OWN SEMANTICS, checked natively by Mina.
//
// ⚑ SAY THE SUBSTRATE OUT LOUD. There is NO AIR authored in this file. Every
// constraint below is read out of
// `src/generated/kimchi-incnonce-b.json`, which is the verbatim output of
// `Dregg2.Circuit.Emit.KimchiEffectIncNonce.emitJson` — a Lean `def`-generator
// whose emitted list carries `kimchi_rows_force_heads` (semantics preservation
// at arbitrary CommRing, over the actual emitted object). This module is a
// TRANSCRIBER: it walks the emitted `Gen1` array and calls `Gates.generic` with
// the coefficients Lean produced. It contains no dregg semantics, no column
// meanings it invented, and no constraint anyone here wrote.
//
// ⚑ WHAT THIS ESTABLISHES, AND WHAT IT DOES NOT.
//
//   ESTABLISHES: this (pre, post) pair IS a valid `incrementNonceA` transition
//   under dregg's semantics — the economic block frozen, the nonce ticked —
//   with `CellIncNonceSpec` forced by a Lean theorem over the very rows this
//   file replays. No dregg proof is consumed, so nothing here inherits dregg's
//   FRI/STARK soundness floor.
//
//   DOES NOT ESTABLISH: that dregg's chain CONTAINS this transition. Route B is
//   a semantics checker, not a membership checker. A well-formed transition that
//   never happened passes this circuit. Membership is route A's job
//   (`DreggProofVerify`), and B is not a cheaper substitute for it.
//
// ⚑ THE GENERIC GATE IS THE `Gen1` SHAPE, EXACTLY. o1js's `Gates.generic`
// asserts `c_l*l + c_r*r + c_o*o + c_m*l*r + c_c === 0`
// (`kimchi/src/circuits/polynomials/generic.rs:84-100`), which is
// `KimchiLower.Gen1.body`. That coincidence is the whole reason the transcriber
// can be this thin, and it is why `KimchiTarget` transcribed that gate rather
// than inventing an encoding.
// ---------------------------------------------------------------------------

const __dirname_ = dirname(fileURLToPath(import.meta.url));

/** One emitted generic sub-gate: `cl*w[l] + cr*w[r] + co*w[o] + cm*w[l]*w[r] + cc = 0`. */
export type EmittedGen = {
  l: number;
  r: number;
  o: number;
  cl: number;
  cr: number;
  co: number;
  cm: number;
  cc: number;
};

export type EmittedProgram = {
  air: string;
  source: string;
  rowWidth: number;
  firstFreshVar: number;
  subGates: number;
  kimchiRows: number;
  cols: Record<string, number>;
  gens: EmittedGen[];
};

/** Resolve the emitted artifact from the package root, so the same path works
 *  whether this module runs from `src/` or from `dist/src/` (the convention
 *  `RootAirDag.artifactPath` already uses). */
function artifactPath(): string {
  let d = __dirname_;
  for (let i = 0; i < 8; i++) {
    try {
      readFileSync(resolve(d, 'package.json'));
      return resolve(d, 'src/generated/kimchi-incnonce-b.json');
    } catch {
      d = resolve(d, '..');
    }
  }
  throw new Error('route-B: could not locate the emitted Kimchi artifact from the package root');
}

export function loadEmitted(): EmittedProgram {
  const prog = JSON.parse(readFileSync(artifactPath(), 'utf8')) as EmittedProgram;
  if (prog.gens.length !== prog.subGates) {
    throw new Error(
      `emitted artifact is inconsistent: subGates=${prog.subGates} but gens=${prog.gens.length}`
    );
  }
  return prog;
}

export const EMITTED = loadEmitted();

const P = Field.ORDER;

/** A signed integer coefficient as a field element. The emitted coefficients are
 *  `±1` and small constants; negatives are the additive inverse, not an error. */
function coeff(c: number): bigint {
  const b = BigInt(c);
  return b < 0n ? P + b : b;
}

// ===========================================================================
// 1. The WITNESS SOLVER — driven by the emitted coefficients, nothing else.
// ===========================================================================
//
// A sub-gate is a DEFINITION of a fresh variable when it is the first gate to
// mention that variable in an output position; otherwise it is an ASSERTION.
// The lowering emits them in a topological order, so one forward pass suffices.
// Note this rule reads only `cl/cr/co/cm/cc` and the variable indices — it does
// not know which gate came from which dregg gate, and could not.

export type Witness = bigint[];

function fmod(x: bigint): bigint {
  const r = x % P;
  return r < 0n ? r + P : r;
}

/**
 * Extend a base assignment (the EffectVM row columns, `[0, firstFreshVar)`) to
 * the full witness the emitted program needs.
 *
 * Returns `{ w, violated }`: `violated` lists the sub-gates that do NOT vanish.
 * A tampered row produces a non-empty `violated` and the proof MUST fail — that
 * is the demonstration, not a caught exception.
 */
export function solveWitness(prog: EmittedProgram, base: bigint[]): {
  w: Witness;
  violated: number[];
} {
  let maxVar = prog.firstFreshVar - 1;
  for (const g of prog.gens) maxVar = Math.max(maxVar, g.l, g.r, g.o);
  const w: (bigint | undefined)[] = new Array(maxVar + 1).fill(undefined);
  for (let i = 0; i < prog.firstFreshVar; i++) w[i] = fmod(base[i] ?? 0n);

  const violated: number[] = [];
  const rd = (i: number): bigint => w[i] ?? 0n;

  prog.gens.forEach((g, idx) => {
    const fresh = (v: number) => v >= prog.firstFreshVar && w[v] === undefined;
    if (g.co !== 0 && fresh(g.o)) {
      // co*w[o] = -(cl*l + cr*r + cm*l*r + cc); every emitted `co` is -1.
      const rest =
        BigInt(g.cl) * rd(g.l) +
        BigInt(g.cr) * rd(g.r) +
        BigInt(g.cm) * rd(g.l) * rd(g.r) +
        BigInt(g.cc);
      if (g.co !== -1) {
        throw new Error(`unsupported output coefficient ${g.co} at sub-gate ${idx}`);
      }
      w[g.o] = fmod(rest);
      return;
    }
    if (g.cl !== 0 && g.cr === 0 && g.cm === 0 && fresh(g.l)) {
      // cl*w[l] + cc = 0; every emitted `cl` here is 1.
      if (g.cl !== 1) {
        throw new Error(`unsupported pin coefficient ${g.cl} at sub-gate ${idx}`);
      }
      w[g.l] = fmod(-BigInt(g.cc));
      return;
    }
    // An ASSERTION. Evaluate it; a nonzero body means this row is not a valid
    // dregg transition.
    const body =
      BigInt(g.cl) * rd(g.l) +
      BigInt(g.cr) * rd(g.r) +
      BigInt(g.co) * rd(g.o) +
      BigInt(g.cm) * rd(g.l) * rd(g.r) +
      BigInt(g.cc);
    if (fmod(body) !== 0n) violated.push(idx);
  });

  return { w: w.map((x) => x ?? 0n), violated };
}

// ===========================================================================
// 2. The TRANSCRIBER — emitted sub-gates into Kimchi generic gates.
// ===========================================================================

/** Replay the emitted program inside the circuit. `vars` must already hold the
 *  circuit variables for every index the program mentions. */
export function replayEmitted(prog: EmittedProgram, vars: Field[]): void {
  assertRawGatesAvailable();
  for (const g of prog.gens) {
    RawGates.generic(
      {
        left: coeff(g.cl),
        right: coeff(g.cr),
        out: coeff(g.co),
        mul: coeff(g.cm),
        const: coeff(g.cc),
      },
      { left: vars[g.l], right: vars[g.r], out: vars[g.o] }
    );
  }
}

/** Witness the whole variable vector and replay. This is the entire circuit
 *  body for the semantic core; §3 adds only the public binding. */
export function witnessAndReplay(prog: EmittedProgram, solve: () => Witness): Field[] {
  let maxVar = prog.firstFreshVar - 1;
  for (const g of prog.gens) maxVar = Math.max(maxVar, g.l, g.r, g.o);
  const n = maxVar + 1;
  const vars = Provable.witness(Provable.Array(Field, n), () => {
    const w = solve();
    return Array.from({ length: n }, (_, i) => Field(w[i] ?? 0n));
  });
  replayEmitted(prog, vars);
  return vars;
}

// ===========================================================================
// 3. The ZkProgram.
// ===========================================================================
//
// PUBLIC INPUT is ONE field element — `KimchiPartition`'s step-boundary
// contract shape — the Poseidon digest of the transition being claimed:
//
//     claim = Poseidon(pre[13] ++ post[13])
//
// The private witness is the full EffectVM row plus the lowering's
// intermediates. The circuit (a) re-derives the digest from the row's own
// state-block columns and pins it to the public input, so the claim names THIS
// row and not another, and (b) replays the emitted sub-gates, which is what
// forces `CellIncNonceSpec`.

/** The thirteen state-block offsets the emitted program constrains, in the order
 *  the digest absorbs them. Read from the emitted column map — not restated. */
const C = EMITTED.cols;

function blockCols(side: 'sb' | 'sa'): number[] {
  const base = side === 'sb' ? C.sbFieldBase : C.saFieldBase;
  return [
    side === 'sb' ? C.sbBalanceLo : C.saBalanceLo,
    side === 'sb' ? C.sbBalanceHi : C.saBalanceHi,
    side === 'sb' ? C.sbNonce : C.saNonce,
    ...Array.from({ length: 8 }, (_, i) => base + i),
    side === 'sb' ? C.sbCapRoot : C.saCapRoot,
    side === 'sb' ? C.sbReserved : C.saReserved,
  ];
}

export const PRE_COLS = blockCols('sb');
export const POST_COLS = blockCols('sa');

/** The full EffectVM row a caller supplies, as a sparse column map. */
export type RowSpec = { preBlock: bigint[]; postBlock: bigint[] };

/** Materialise the base (column) part of the assignment from a `RowSpec`. */
export function baseAssignment(prog: EmittedProgram, row: RowSpec): bigint[] {
  const base = new Array<bigint>(prog.firstFreshVar).fill(0n);
  PRE_COLS.forEach((c, i) => (base[c] = row.preBlock[i] ?? 0n));
  POST_COLS.forEach((c, i) => (base[c] = row.postBlock[i] ?? 0n));
  base[C.selIncrementNonce] = 1n;
  base[C.selNoop] = 0n;
  return base;
}

export function claimDigest(row: RowSpec): Field {
  return Poseidon.hash([
    ...row.preBlock.map((x) => Field(x)),
    ...row.postBlock.map((x) => Field(x)),
  ]);
}

export class IncNonceRow extends Struct({
  preBlock: Provable.Array(Field, 13),
  postBlock: Provable.Array(Field, 13),
}) {}

/** Rows of the SEMANTIC CORE alone — the transcribed sub-gates and nothing else.
 *  This is the number `KimchiEffectIncNonce.incNonceKimchiRows_length` predicts. */
export async function coreRows(): Promise<number> {
  const cs = await Provable.constraintSystem(() => {
    witnessAndReplay(EMITTED, () => new Array<bigint>(300).fill(0n));
  });
  return cs.rows;
}

export const DreggIncNonceNative = ZkProgram({
  name: 'dregg-incnonce-native-b',
  publicInput: Field,
  methods: {
    check: {
      privateInputs: [IncNonceRow],
      async method(claim: Field, row: IncNonceRow) {
        // (a) the claim names THIS row.
        Poseidon.hash([...row.preBlock, ...row.postBlock]).assertEquals(claim);

        // (b) the emitted program, replayed. `vars` is the whole assignment;
        // the state-block columns are wired to the row the claim just pinned.
        const vars = witnessAndReplay(EMITTED, () => {
          const base = new Array<bigint>(EMITTED.firstFreshVar).fill(0n);
          PRE_COLS.forEach((c, i) => (base[c] = row.preBlock[i].toBigInt()));
          POST_COLS.forEach((c, i) => (base[c] = row.postBlock[i].toBigInt()));
          base[C.selIncrementNonce] = 1n;
          base[C.selNoop] = 0n;
          return solveWitness(EMITTED, base).w;
        });

        PRE_COLS.forEach((c, i) => vars[c].assertEquals(row.preBlock[i]));
        POST_COLS.forEach((c, i) => vars[c].assertEquals(row.postBlock[i]));
        // `s_noop = 0` — the non-NoOp hypothesis `intent_to_cellSpec` carries.
        vars[C.selNoop].assertEquals(Field(0));

        // The canonicality envelope, DISCHARGED in-circuit rather than assumed.
        // `KimchiEffectIncNonce.KimchiRowCanon` bounds every state cell by
        // `2^32`, and `Gadgets.rangeCheck32` is exactly that bound — the Lean
        // constant was set to match this gadget, not the other way round. Note
        // it is a whole binade LOOSER than BabyBear canonicality and still ~2^222
        // under the Kimchi modulus, which is why the Kimchi-side forcing lemma
        // needs no overflow hypothesis where the BabyBear one does.
        for (const c of [...PRE_COLS, ...POST_COLS]) {
          Gadgets.rangeCheck32(vars[c]);
        }
      },
    },
  },
});
