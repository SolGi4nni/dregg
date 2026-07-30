import { Field, Provable } from 'o1js';
import { RawGates, assertRawGatesAvailable } from './kimchi-raw-gates.js';
import type { Rc0Limbs12, Rc0Limbs2 } from './kimchi-raw-gates.js';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

// ---------------------------------------------------------------------------
// THE DEPLOYED BabyBear Poseidon2-w16 PERMUTATION, TRANSCRIBED FROM LEAN.
//
// ⚑ SAY THE SUBSTRATE OUT LOUD. There is NO Poseidon2 in this file. Not a round
// constant, not the internal diagonal, not the `MDSMat4` circulant, not the
// round structure, not the bound chain, not the reduction schedule. Every
// constraint below is read out of `src/generated/kimchi-poseidon2-w16.json`,
// which is the verbatim output of
// `Dregg2.Circuit.Emit.KimchiPoseidon2.emitJson` — a Lean `def`-generator whose
// 141 S-boxes are a FOLD over imported round constants with none of them spelled
// out, and whose emitted rows carry `sbox_gens_force` (the S-box's forcing lemma
// at arbitrary `CommRing`, over the actual emitted sub-gates) and a `#guard`
// that its own witness satisfies every emitted row.
//
// This module is a TRANSCRIBER. It walks the emitted instruction array and calls
// `Gates.generic` / `Gates.rangeCheck0` with the coefficients and columns Lean
// produced. It could not compute a wrong permutation, because it does not know
// what a permutation is.
//
// ⚑ WHAT THIS REPLACES AND WHAT IT DOES NOT.
//
//   REPLACES: `Poseidon2BabyBearW16.provablePermBounded`'s ~230 lines of
//   hand-written in-circuit body — `add`/`scale`/`sub`/`mul`/`reduce`/`sbox`/
//   `mat4BB`/`mdsLightBB`/`externalRoundBB`/`internalRoundBB`/`quotientTimesP`/
//   `assertLt2p31` — with a 60-line loop over an emitted array.
//
//   DOES NOT REPLACE: the bigint reference (`permBigInt` and friends), which is
//   an OUT-OF-CIRCUIT twin the challengers and walk evaluators need at prove
//   time and which no gate list can supply; the KAT vectors, which are pins; or
//   `canonicalLane`/`reduceLane`, which are lane hygiene the Lean generator does
//   not yet emit. Those stay where they are and are named in the ladder.
//
// ⚑ AND IT IS NOT A DROP-IN AT THIS ROW COUNT. Lean emits 2,669 rows against
// o1js's measured 2,602 — the two range disciplines differ (see the artifact's
// own §6, and §5d on the 64-bit-vs-2^31 gap this transcription faithfully
// inherits). Swapping the call sites therefore moves ~15 of the 31 pinned
// figures in `recorded-constants.tsv` plus ~15 un-censused table rows, across
// tiers 0, 1 and 2. That is a measure-then-re-pin, not a flip.
// ---------------------------------------------------------------------------

const __dirname_ = dirname(fileURLToPath(import.meta.url));

/** One emitted generic sub-gate: `cl*w[l] + cr*w[r] + co*w[o] + cm*w[l]*w[r] + cc = 0`. */
export type EmittedGenOp = {
  k: 'g';
  l: number;
  r: number;
  o: number;
  cl: number;
  cr: number;
  co: number;
  cm: number;
  cc: number;
};

/** One emitted standalone 64-bit `RangeCheck0` row: fifteen columns in `rc0Places` order —
 *  the checked value, the two COPY columns (place `2^76`, `2^64`), the four 12-bit PLOOKUP
 *  columns (`2^52 .. 2^16`), and the eight 2-bit crumbs (`2^14 .. 2^0`). */
export type EmittedRcOp = { k: 'r'; w: number[] };

/** A companion `Zero` row. Not emitted by the permutation; handled so the transcriber is
 *  total over `KOp` rather than silently dropping a shape it did not expect. */
export type EmittedZeroOp = { k: 'z' };

export type EmittedOp = EmittedGenOp | EmittedRcOp | EmittedZeroOp;

export type EmittedPerm = {
  air: string;
  source: string;
  width: number;
  modulus: string | number;
  zeroVar: number;
  nVars: number;
  subGates: number;
  kimchiRows: number;
  inputVars: number[];
  outputVars: number[];
  /** The tracked bound on each output lane. ⚑ These are NOT `< 2^31`: the last thing a
   *  permutation runs is the ADD-ONLY external layer with fan-in 35. Carried in the artifact
   *  so a caller chaining permutations cannot forget to re-bound. */
  outputBounds: string[];
  honestInput: number[];
  honestOutput: string[];
  /** The generator's own witness at `honestInput`. The solver below reads only the emitted
   *  coefficients, so it is an INDEPENDENT implementation; agreeing with this vector is what
   *  keeps it from being a third opinion about the same circuit. */
  honestVals: string[];
  prog: EmittedOp[];
};

/** The place values of a `RangeCheck0` row's twelve limbs and two copy columns, MSB first —
 *  `KimchiTarget.rc0Places`, columns 1..14. The value is `sum 2^place * w[col]`. */
const RC0_PLACES: number[] = [76, 64, 52, 40, 28, 16, 14, 12, 10, 8, 6, 4, 2, 0];

function artifactPath(): string {
  let d = __dirname_;
  for (let i = 0; i < 8; i++) {
    try {
      readFileSync(resolve(d, 'package.json'));
      return resolve(d, 'src/generated/kimchi-poseidon2-w16.json');
    } catch {
      d = resolve(d, '..');
    }
  }
  throw new Error(
    'poseidon2-native: could not locate the emitted Kimchi artifact from the package root'
  );
}

let _emitted: EmittedPerm | undefined;

/**
 * Load the emitted artifact, once.
 *
 * ⚑ LAZY ON PURPOSE, AND IT IS A REFUSAL RATHER THAN A FALLBACK. Route B loads
 * at module scope because its artifact is committed; this one is regenerated by
 * `lake env lean --run EmitKimchiPoseidon2.lean`, so a module-scope load would
 * make importing this file fail the tier-0 typecheck on a tree that has not run
 * the emitter yet. Importing is free; ASKING for the permutation without the
 * artifact throws, naming the command that produces it.
 */
export function loadEmittedPerm(): EmittedPerm {
  if (_emitted !== undefined) return _emitted;
  let raw: string;
  try {
    raw = readFileSync(artifactPath(), 'utf8');
  } catch {
    throw new Error(
      `poseidon2-native: the emitted artifact is missing at ${artifactPath()}. ` +
        'Regenerate it with `lake env lean --run EmitKimchiPoseidon2.lean` from `metatheory/`. ' +
        'This is a REFUSAL: there is no hand-written permutation to fall back to, and that is ' +
        'the point of the module.'
    );
  }
  const prog = JSON.parse(raw) as EmittedPerm;
  if (prog.prog.length !== prog.subGates) {
    throw new Error(
      `poseidon2-native: artifact inconsistent — subGates=${prog.subGates} but prog=${prog.prog.length}`
    );
  }
  if (prog.inputVars.length !== prog.width || prog.outputVars.length !== prog.width) {
    throw new Error(
      `poseidon2-native: artifact inconsistent — width=${prog.width} but ` +
        `${prog.inputVars.length} input / ${prog.outputVars.length} output lanes`
    );
  }
  _emitted = prog;
  return prog;
}

const N = Field.ORDER;

/** A signed integer coefficient as a field element. Emitted coefficients are round constants,
 *  powers of two, modulus multiples and `+-1`; a negative is the additive inverse, not an error. */
function coeff(c: number | string): bigint {
  const b = BigInt(c);
  return b < 0n ? ((b % N) + N) % N : b % N;
}

function fmod(x: bigint): bigint {
  const r = x % N;
  return r < 0n ? r + N : r;
}

// ===========================================================================
// 1. The WITNESS SOLVER — driven by the emitted instructions, nothing else.
// ===========================================================================
//
// The generator emits in topological order, so one forward pass suffices. Note
// the rules below read only coefficients, variable indices and `rc0` column
// lists: nothing here knows which instruction came from which round, and could
// not. A `.rc0` op is a DEFINITION of its twelve limb columns (their values are
// the checked value's base-2 decomposition at `RC0_PLACES`) and an ASSERTION
// about the checked value itself.

export type Witness = bigint[];

export function solveWitness(
  prog: EmittedPerm,
  inputLanes: bigint[]
): { w: Witness; violated: number[] } {
  const w: (bigint | undefined)[] = new Array(prog.nVars).fill(undefined);
  prog.inputVars.forEach((v, i) => (w[v] = fmod(inputLanes[i] ?? 0n)));

  const violated: number[] = [];
  const rd = (i: number): bigint => w[i] ?? 0n;
  const fresh = (v: number) => w[v] === undefined;

  prog.prog.forEach((op, idx) => {
    if (op.k === 'z') return;

    if (op.k === 'r') {
      // The checked value must already be known; its limbs are what this row defines.
      const v = rd(op.w[0]);
      for (let c = 1; c < op.w.length; c++) {
        const col = op.w[c];
        const place = BigInt(RC0_PLACES[c - 1]);
        const width = RC0_PLACES[c - 1] >= 16 ? 12n : 2n;
        const limb = (v >> place) & ((1n << width) - 1n);
        if (fresh(col)) w[col] = limb;
        else if (w[col] !== limb) {
          // A shared column (the pinned zero) disagreeing with the decomposition means the
          // checked value does not fit the row — an out-of-range lane, not a solver bug.
          violated.push(idx);
        }
      }
      return;
    }

    if (op.co !== 0 && fresh(op.o)) {
      // co*w[o] = -(cl*l + cr*r + cm*l*r + cc); every emitted `co` is -1.
      if (op.co !== -1) throw new Error(`poseidon2-native: unsupported co=${op.co} at op ${idx}`);
      w[op.o] = fmod(
        BigInt(op.cl) * rd(op.l) +
          BigInt(op.cr) * rd(op.r) +
          BigInt(op.cm) * rd(op.l) * rd(op.r) +
          BigInt(op.cc)
      );
      return;
    }
    if (op.cl !== 0 && op.cr === 0 && op.cm === 0 && op.co === 0 && fresh(op.l)) {
      if (op.cl !== 1) throw new Error(`poseidon2-native: unsupported cl=${op.cl} at op ${idx}`);
      w[op.l] = fmod(-BigInt(op.cc));
      return;
    }

    const body =
      BigInt(op.cl) * rd(op.l) +
      BigInt(op.cr) * rd(op.r) +
      BigInt(op.co) * rd(op.o) +
      BigInt(op.cm) * rd(op.l) * rd(op.r) +
      BigInt(op.cc);
    if (fmod(body) !== 0n) violated.push(idx);
  });

  return { w: w.map((x) => x ?? 0n), violated };
}

/**
 * **The witness weld.** Rebuild the honest witness from Lean's own KAT input and check it
 * against Lean's own `honestVals`, value for value.
 *
 * The failure mode this guards is LIVENESS, not soundness: a wrong witness makes an honest
 * permutation unprovable, it cannot make a wrong one provable — the emitted rows are the
 * authority either way. But an unprovable honest instance is exactly how a route gets quietly
 * written off as too expensive.
 */
export function checkWitnessWeld(prog: EmittedPerm): {
  checked: number;
  mismatches: string[];
} {
  const { w, violated } = solveWitness(prog, prog.honestInput.map(BigInt));
  const mismatches: string[] = [];
  if (violated.length > 0) {
    mismatches.push(
      `Lean's own KAT witness VIOLATES instructions [${violated.slice(0, 8)}] under the TS solver`
    );
  }
  prog.honestVals.forEach((v, i) => {
    const want = fmod(BigInt(v));
    if (w[i] !== want) mismatches.push(`w[${i}] = ${w[i]}, Lean says ${want}`);
  });
  return { checked: prog.honestVals.length, mismatches };
}

// ===========================================================================
// 2. The TRANSCRIBER — emitted instructions into Kimchi gates.
// ===========================================================================

/** Replay the emitted program inside the circuit. `vars` must hold a circuit variable for
 *  every index the program mentions. ONE emitted instruction becomes ONE gate call, which is
 *  what makes the emitted row count and `getRows()` comparable at all. */
export function replayEmitted(prog: EmittedPerm, vars: Field[]): void {
  assertRawGatesAvailable();
  for (const op of prog.prog) {
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
      const cols = op.w.map((i) => vars[i]);
      RawGates.rangeCheck0(
        cols[0],
        cols.slice(1, 7) as Rc0Limbs12,
        cols.slice(7, 15) as Rc0Limbs2,
        false
      );
    } else {
      RawGates.zero(vars[0], vars[0], vars[0]);
    }
  }
}

/**
 * **The deployed BabyBear Poseidon2-w16 permutation, as Lean emitted it.**
 *
 * Drop-in for `Poseidon2BabyBearW16.provablePermBounded` at the type level. The caller's
 * sixteen lanes are SPLICED into the variable vector rather than witnessed-and-equated, so a
 * lane that is already a circuit variable costs nothing to wire and the measured row count is
 * the emitted one plus whatever sealing the caller's own expressions needed.
 *
 * Returns the sixteen output lanes. Their tracked bounds are `prog.outputBounds` and they are
 * NOT `< 2^31`; use `reduceLane` before re-feeding and `canonicalLane` before comparing.
 */
export function provablePermNative(input: Field[]): Field[] {
  const prog = loadEmittedPerm();
  if (input.length !== prog.width) {
    throw new Error(`poseidon2-native: expected ${prog.width} lanes, got ${input.length}`);
  }
  const vars = Provable.witness(Provable.Array(Field, prog.nVars), () => {
    const { w } = solveWitness(
      prog,
      input.map((x) => x.toBigInt())
    );
    return Array.from({ length: prog.nVars }, (_, i) => Field(w[i] ?? 0n));
  });
  prog.inputVars.forEach((v, i) => (vars[v] = input[i]));
  replayEmitted(prog, vars);
  return prog.outputVars.map((v) => vars[v]);
}

/** `compress` — the deployed `TruncatedPermutation<., 2, 8, 16>`, on the emitted permutation. */
export function provableCompressNative(a: Field[], b: Field[]): Field[] {
  return provablePermNative([...a, ...b]).slice(0, 8);
}

/** The tracked bound the emitted permutation leaves on each output lane. */
export function nativeOutputBounds(): bigint[] {
  return loadEmittedPerm().outputBounds.map(BigInt);
}

/** Rows of the transcribed permutation ALONE — the number the artifact's `kimchiRows`
 *  predicts, and the one the Lean `#guard permRowCount` pins. */
export async function nativeRows(): Promise<number> {
  const prog = loadEmittedPerm();
  const cs = await Provable.constraintSystem(() => {
    const lanes = Provable.witness(Provable.Array(Field, prog.width), () =>
      prog.honestInput.map((x) => Field(BigInt(x)))
    );
    provablePermNative(lanes);
  });
  return cs.rows;
}
