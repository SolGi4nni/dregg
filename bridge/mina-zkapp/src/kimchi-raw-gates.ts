import type { Field } from 'o1js';
import { existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';

// ---------------------------------------------------------------------------
// A DEEP IMPORT INTO o1js, AND THE REASON FOR IT.
//
// o1js's package `exports` map publishes only the top-level index, and `Gates`
// is not on it — `Gadgets` is, but `Gadgets` has no raw generic gate. The route-B
// transcriber needs the RAW gate for one reason: FIDELITY OF MEASUREMENT.
//
// The supported alternative is to write `cl*l + cr*r + ... === 0` with `Field`
// arithmetic and let o1js's own lowering pick the gates. That would also work,
// and it would also be correct — but then the emitted row count is o1js's
// compiler's decision, not the Lean lowering's, and `incNonceKimchiRows_length`
// (27) would be compared against a number produced by a different compiler. One
// emitted `Gen1` must become exactly one `Snarky.gates.generic` call for the
// comparison to mean anything.
//
// This is a NAMED SEAM: `Gates.generic` is o1js-internal API and can move
// between releases. It is pinned at o1js 2.15.0
// (`dist/node/lib/provable/gates.js`), the resolver below FAILS LOUDLY rather
// than falling back, and `assertRawGatesAvailable` is called before any
// measurement so a missing internal surfaces as a refusal and never as a
// silently different circuit.
// ---------------------------------------------------------------------------

export type GenericCoefficients = {
  left: bigint;
  right: bigint;
  out: bigint;
  mul: bigint;
  const: bigint;
};

export type GenericInputs = { left: Field; right: Field; out: Field };

type RawGates = {
  generic: (c: GenericCoefficients, i: GenericInputs) => void;
};

const O1JS_GATES_REL = 'node_modules/o1js/dist/node/lib/provable/gates.js';

function findGatesModule(): string {
  let dir = dirname(fileURLToPath(import.meta.url));
  for (let i = 0; i < 12; i++) {
    const cand = resolve(dir, O1JS_GATES_REL);
    if (existsSync(cand)) return cand;
    const up = dirname(dir);
    if (up === dir) break;
    dir = up;
  }
  throw new Error(
    `route-B transcriber: could not locate o1js internal ${O1JS_GATES_REL}. ` +
      `This is the named seam in kimchi-raw-gates.ts; it is a REFUSAL, not a fallback.`
  );
}

const gatesModule = (await import(pathToFileURL(findGatesModule()).href)) as {
  Gates?: RawGates;
};

if (typeof gatesModule.Gates?.generic !== 'function') {
  throw new Error(
    'route-B transcriber: o1js internal gates module has no `Gates.generic`. ' +
      'The pin is o1js 2.15.0; refusing rather than emitting a different circuit.'
  );
}

export const RawGates: RawGates = gatesModule.Gates;

export function assertRawGatesAvailable(): void {
  if (typeof RawGates.generic !== 'function') {
    throw new Error('route-B transcriber: raw generic gate unavailable');
  }
}
