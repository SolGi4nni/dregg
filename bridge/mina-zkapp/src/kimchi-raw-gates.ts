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

/** The six 12-bit plookup/copy limbs of a `RangeCheck0` row (columns 1..6). */
export type Rc0Limbs12 = [Field, Field, Field, Field, Field, Field];
/** The eight 2-bit crumbs of a `RangeCheck0` row (columns 7..14). */
export type Rc0Limbs2 = [Field, Field, Field, Field, Field, Field, Field, Field];

type RawGates = {
  generic: (c: GenericCoefficients, i: GenericInputs) => void;
  /** `range_check/gadget.rs:63-69` — one standalone row, `isCompact = false`. The
   *  GROUP-4 commitment emission needs this because a range check is not a generic
   *  sub-gate: `RangeCheck0` is its own gate with its own ten bodies, and
   *  `KimchiTarget.rc0Bodies` transcribes exactly those. */
  rangeCheck0: (
    x: Field,
    xLimbs12: Rc0Limbs12,
    xLimbs2: Rc0Limbs2,
    isCompact: boolean
  ) => void;
  zero: (a: Field, b: Field, c: Field) => void;
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

const resolved = gatesModule.Gates;
if (resolved === undefined) {
  throw new Error(
    'route-B transcriber: o1js internal gates module exports no `Gates`. ' +
      'The pin is o1js 2.15.0; refusing rather than emitting a different circuit.'
  );
}
for (const name of ['generic', 'rangeCheck0', 'zero'] as const) {
  if (typeof resolved[name] !== 'function') {
    throw new Error(
      `route-B transcriber: o1js internal gates module has no \`Gates.${name}\`. ` +
        'The pin is o1js 2.15.0; refusing rather than emitting a different circuit.'
    );
  }
}

export const RawGates: RawGates = resolved;

export function assertRawGatesAvailable(): void {
  for (const name of ['generic', 'rangeCheck0', 'zero'] as const) {
    if (typeof RawGates[name] !== 'function') {
      throw new Error(`route-B transcriber: raw ${name} gate unavailable`);
    }
  }
}
