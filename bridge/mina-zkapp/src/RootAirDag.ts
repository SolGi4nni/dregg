import { Field, Provable } from 'o1js';
import { canonicalLane, reduceLane } from './Poseidon2BabyBearW16.js';
import { BbExt, EXT_D, EXT_W, extAdd, extMul, extSub } from './FriQueryStep.js';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

// ---------------------------------------------------------------------------
// THE ROOT'S OWN AIR — `C_i` for all 1,093 constraints of dregg's seven root
// tables, as a DAG this circuit interprets.
//
// ⚑ WHAT THIS CLOSES, AND IT IS THE LAST NAMED GAP ON THIS SIDE.
//
// §3.19 built one Kimchi circuit that DECIDES a real dregg STARK proof, and
// named exactly one thing as still the fixture's: `DreggProofVerify`'s
// `constraints` argument, a 3-column AIR with FOUR constraints. Every figure
// downstream of that is a FLOOR because of it — the 2.75e7-row projection, and
// §3.21's 591-step schedule over that projection. §3.17 counted the real number
// (`N = 1,093`) and §3.18 built the DAG source language that makes it affordable
// (2,433 multiplies against 1,529,889 flat, 629x). Neither ever reached the
// o1js side. This module is the reach.
//
// ⚑ SAY THE SUBSTRATE OUT LOUD, because three objects are involved and only one
// of them is proved:
//
//   * the AIRs are p3's (`plonky3-recursion@0a4a554`), not ours and not
//     re-authored here;
//   * the NUMBERING is `to_dag`/`to_dag_full`'s, a Rust extractor, and it is a
//     SEAM — checked differentially against p3's own evaluation over all 901
//     base constraints (`dag_extractor_agrees_with_p3_evaluation`) and all 192
//     extension ones (`ext_dag_agrees_with_p3_evaluation`), which is a
//     confession, not a proof;
//   * the LOWERING of a node list to Kimchi rows is proved in Lean, at an
//     arbitrary `CommRing` (`Dregg2.Circuit.Emit.KimchiDag.dagGens_forces`,
//     `dagFold_forces`, `dagDenote_unfold`) — and this file is NOT that
//     lowering. It is a THIRD implementation, a TypeScript walker, and nothing
//     proves it faithful to either of the other two.
//
// What ties this walker to the other two is `checkKat` below: at pseudorandom
// EXTENSION-valued assignments it must reproduce, per table, the alpha-folded
// accumulator the Rust side computed from the same node list. That is the same
// shape of confession the extractor makes, one rung out, and it is named as one
// rather than dressed up.
//
// ⚑ THE FOLD IS p3's, SEEDED WITH ZERO. `recursion/src/traits/air.rs:152-163`
// starts `acc = 0` and pays `N` folds of `acc = acc*alpha + C`, base
// constraints first in emission order and then the extension ones. §3.17
// records that `AirEval.ts`'s `foldConstraints` seeds with `constraints[0]` and
// pays `N-1` — a different accumulator by one factor of alpha. `foldRootsP3`
// below is p3's, and the two are not interchangeable.
// ---------------------------------------------------------------------------

export const P = 2013265921n;
const LANE_MAX = (1n << 31n) - 1n;

// ===========================================================================
// 1. The artifact.
// ===========================================================================

export type DagKat = { seed: string; alpha: number[]; acc: number[] };

export type DagTable = {
  name: string;
  /** How many of `roots` are BASE constraints; the rest are LogUp. The split is
   *  carried because the fold order is base-then-ext and a permuted list is a
   *  different accumulator. */
  nBase: number;
  nExt: number;
  /** Column labels, indexed by the number a `var` node carries. */
  cols: string[];
  /** Extension column labels, indexed by the number an `evar` node carries. */
  extCols: string[];
  /** `[kind, ...operands]`; see `KIND`. Children are always strictly below the
   *  node's own index — the `dagWf` invariant the Lean theorem takes as a
   *  hypothesis, re-checked here by `assertWf`. */
  nodes: number[][];
  roots: number[];
  kat: DagKat[];
};

export type RootAirDag = {
  kind: string;
  generator: string;
  p: number;
  extDegree: number;
  katTrials: number;
  kindCodes: Record<string, number>;
  totals: {
    nodes: number;
    muls: number;
    base: number;
    ext: number;
    n: number;
    kinds: Record<string, number>;
  };
  tables: DagTable[];
};

export const KIND = {
  var: 0,
  cst: 1,
  add: 2,
  sub: 3,
  neg: 4,
  mul: 5,
  evar: 6,
  ecst: 7,
} as const;

/** Resolve the emitted artifact from the package root, so the same path works
 *  whether this module runs from `src/` or from `dist/src/`. */
function artifactPath(): string {
  let d = dirname(fileURLToPath(import.meta.url));
  for (let i = 0; i < 8; i++) {
    try {
      readFileSync(resolve(d, 'package.json'));
      return resolve(d, 'src/generated/root-air-dag.json');
    } catch {
      d = resolve(d, '..');
    }
  }
  throw new Error('cannot locate the mina-zkapp package root from ' + import.meta.url);
}

let CACHE: RootAirDag | undefined;

/**
 * The emitted root AIR. ⚑ A MISSING ARTIFACT IS A FAILURE, NOT A SKIP — the
 * whole point of this module is that the fixture's four constraints stop
 * standing in for the root's 1,093, and a module that silently fell back to
 * something smaller would restore exactly the defect it exists to remove.
 */
export function rootAirDag(): RootAirDag {
  if (CACHE) return CACHE;
  const path = artifactPath();
  let raw: string;
  try {
    raw = readFileSync(path, 'utf8');
  } catch (e) {
    throw new Error(
      `the root AIR artifact is missing at ${path} — regenerate it with\n` +
        `  DREGG_AIR_DAG_JSON=${path} cargo test -p dregg-circuit-prove \\\n` +
        `    --test root_air_constraint_census -- --nocapture emit_root_air_dag_json\n` +
        `(${(e as Error).message})`,
    );
  }
  const d = JSON.parse(raw) as RootAirDag;
  if (d.kind !== 'dregg-root-air-dag')
    throw new Error(`${path} is not a root-AIR artifact (kind=${d.kind})`);
  if (BigInt(d.p) !== P) throw new Error(`the artifact's field is ${d.p}, not BabyBear`);
  if (d.extDegree !== EXT_D) throw new Error(`the artifact's extension degree is ${d.extDegree}`);
  for (const [k, v] of Object.entries(KIND))
    if (d.kindCodes[k] !== v)
      throw new Error(`kind code drift: the artifact calls ${v} '${k}'? got ${d.kindCodes[k]}`);
  for (const t of d.tables) assertWf(t);
  CACHE = d;
  return d;
}

/**
 * ⚑ `dagWf` IS A HYPOTHESIS, NOT A LEMMA — `KimchiDag` says so and the same
 * applies here, harder. Every child index must be strictly below its parent's.
 * An out-of-order list reads a node that has not been computed yet; in Lean the
 * forcing theorem is simply FALSE for it, and here it would read `undefined` and
 * throw somewhere unhelpful. Checked once, at load.
 */
export function assertWf(t: DagTable) {
  for (let i = 0; i < t.nodes.length; i++) {
    const n = t.nodes[i];
    const bad = (c: number) => c >= i;
    switch (n[0]) {
      case KIND.var:
        if (n[1] >= t.cols.length) throw new Error(`${t.name}: var ${n[1]} out of range`);
        break;
      case KIND.evar:
        if (n[1] >= t.extCols.length) throw new Error(`${t.name}: evar ${n[1]} out of range`);
        break;
      case KIND.cst:
      case KIND.ecst:
        break;
      case KIND.neg:
        if (bad(n[1])) throw new Error(`${t.name}: node ${i} reads ${n[1]} — not sorted`);
        break;
      case KIND.add:
      case KIND.sub:
      case KIND.mul:
        if (bad(n[1]) || bad(n[2]))
          throw new Error(`${t.name}: node ${i} reads ${n[1]}/${n[2]} — not sorted`);
        break;
      default:
        throw new Error(`${t.name}: node ${i} has unknown kind ${n[0]}`);
    }
  }
  for (const r of t.roots)
    if (r >= t.nodes.length) throw new Error(`${t.name}: root ${r} out of range`);
  if (t.roots.length !== t.nBase + t.nExt)
    throw new Error(`${t.name}: ${t.roots.length} roots against nBase+nExt=${t.nBase + t.nExt}`);
}

// ===========================================================================
// 2. The out-of-circuit twin — bigint limbs.
// ===========================================================================

const md = (x: bigint) => ((x % P) + P) % P;
const eAdd = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
const eSub = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x - b[i]));
const eNeg = (a: bigint[]) => a.map((x) => md(-x));
function eMul(a: bigint[], b: bigint[]): bigint[] {
  const acc = Array(2 * EXT_D - 1).fill(0n) as bigint[];
  for (let i = 0; i < EXT_D; i++)
    for (let j = 0; j < EXT_D; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
  return Array.from({ length: EXT_D }, (_, i) =>
    i + EXT_D < 2 * EXT_D - 1 ? md(acc[i] + EXT_W * acc[i + EXT_D]) : acc[i],
  );
}

/** Evaluate one table's DAG at bigint assignments; returns the ROOT values in
 *  `roots` order (base first, then extension — p3's fold order). */
export function evalDagBigInt(t: DagTable, base: bigint[][], ext: bigint[][]): bigint[][] {
  const v: bigint[][] = new Array(t.nodes.length);
  for (let i = 0; i < t.nodes.length; i++) {
    const n = t.nodes[i];
    switch (n[0]) {
      case KIND.var:
        v[i] = base[n[1]];
        break;
      case KIND.cst:
        v[i] = [md(BigInt(n[1])), 0n, 0n, 0n];
        break;
      case KIND.add:
        v[i] = eAdd(v[n[1]], v[n[2]]);
        break;
      case KIND.sub:
        v[i] = eSub(v[n[1]], v[n[2]]);
        break;
      case KIND.neg:
        v[i] = eNeg(v[n[1]]);
        break;
      case KIND.mul:
        v[i] = eMul(v[n[1]], v[n[2]]);
        break;
      case KIND.evar:
        v[i] = ext[n[1]];
        break;
      case KIND.ecst:
        v[i] = [md(BigInt(n[1])), md(BigInt(n[2])), md(BigInt(n[3])), md(BigInt(n[4]))];
        break;
      default:
        throw new Error(`unknown kind ${n[0]}`);
    }
  }
  return t.roots.map((r) => v[r]);
}

/** p3's accumulator: `acc = 0`, then `acc = acc*alpha + C_i` over the roots IN
 *  ORDER. ⚑ NOT `AirEval.ts`'s `foldConstraints`, which seeds with `C_0`. */
export function foldRootsP3BigInt(alpha: bigint[], roots: bigint[][]): bigint[] {
  let acc = [0n, 0n, 0n, 0n];
  for (const c of roots) acc = eAdd(eMul(acc, alpha), c);
  return acc;
}

// ===========================================================================
// 3. The KAT's assignment stream — the SPEC, reimplemented.
// ===========================================================================

const MASK64 = (1n << 64n) - 1n;

/** The emitter's LCG (`root_air_constraint_census.rs::lcg`), bit for bit. */
export class Lcg {
  constructor(private s: bigint) {}
  next(): bigint {
    this.s = (this.s * 6364136223846793005n + 1442695040888963407n) & MASK64;
    return (this.s >> 33n) % P;
  }
  nextExt(): bigint[] {
    return [this.next(), this.next(), this.next(), this.next()];
  }
}

/** The stream the artifact specifies: `alpha`, then every base column in index
 *  order, then every extension column. */
export function katAssignment(
  t: DagTable,
  k: DagKat,
): { alpha: bigint[]; base: bigint[][]; ext: bigint[][] } {
  const g = new Lcg(BigInt(k.seed));
  const alpha = g.nextExt();
  const base = Array.from({ length: t.cols.length }, () => g.nextExt());
  const ext = Array.from({ length: t.extCols.length }, () => g.nextExt());
  return { alpha, base, ext };
}

/**
 * ⚑ **THE ONLY THING JOINING THIS WALKER TO p3 AND TO LEAN.** For every table
 * and every trial, re-derive the assignment from the recorded seed, walk the
 * DAG here, fold it p3's way, and require the accumulator to equal the one the
 * Rust side computed from the same node list. Every mismatch is reported, not
 * just the first, because "one table is wrong" and "the walker is wrong" are
 * different diagnoses.
 *
 * ⚑ AND IT MUST BE ABLE TO GO RED. A KAT over an artifact whose expected values
 * this file also produced would be a tautology; these come from
 * `Dag::eval_ef` + `fold_roots` in Rust, from p3's own AIRs, and the alpha-fold
 * is order-sensitive, so a single mis-numbered child moves it.
 */
export function checkKat(d: RootAirDag = rootAirDag()): { checked: number; failures: string[] } {
  const failures: string[] = [];
  let checked = 0;
  for (const t of d.tables) {
    for (const k of t.kat) {
      const { alpha, base, ext } = katAssignment(t, k);
      const wantAlpha = k.alpha.map((x) => BigInt(x));
      if (alpha.some((x, i) => x !== wantAlpha[i]))
        failures.push(
          `${t.name} @ ${k.seed}: the LCG stream diverged at alpha — ` +
            `got [${alpha}], artifact says [${wantAlpha}]`,
        );
      const acc = foldRootsP3BigInt(alpha, evalDagBigInt(t, base, ext));
      const want = k.acc.map((x) => BigInt(x));
      if (acc.some((x, i) => x !== want[i]))
        failures.push(
          `${t.name} @ ${k.seed}: accumulator [${acc}] against the artifact's [${want}]`,
        );
      checked++;
    }
  }
  return { checked, failures };
}

// ===========================================================================
// 4. The IN-CIRCUIT evaluator.
// ===========================================================================

/**
 * How a DAG node becomes o1js operations.
 *
 * `strict` is the Lean lowering's own shape: ONE operation per node, which is
 * what `dagGens_forces` is a theorem about (one `Gen1` per node, node `k` to
 * variable `nv + k`). It is the number this file ratchets, because it is the
 * one an emitted-rows claim can point at a proved lowering for.
 *
 * The two elisions below are REAL and are measured as a delta rather than
 * assumed:
 *
 *  * `elideVarCopies` — a `var` node is a copy of an input, and
 *    `KimchiDag` §11.2 already names it elidable. 1,282 of the root's 10,417
 *    nodes are copies.
 *  * `constScale` — `mul` with a `cst` operand is a scale by a base-field
 *    CONSTANT, which is 4 coefficient multiplies rather than the 16-multiply
 *    schoolbook plus the `W`-fold. 377 nodes are constants and they are heavily
 *    shared.
 *
 * ⚑ NEITHER ELISION MAY CHANGE THE DENOTATION, and that is checked, not argued:
 * `evalDagInCircuit` is run under both settings inside `Provable.runAndCheck`
 * against the same KAT the out-of-circuit walker reproduces.
 */
export type DagEvalOpts = {
  elideVarCopies?: boolean;
  constScale?: boolean;
};

/** Scale an extension element by a base-field CONSTANT — 4 multiplies by a
 *  compile-time coefficient, against `extMul`'s 16 plus the `W`-fold. */
function extScaleConstLocal(a: BbExt, c: bigint): BbExt {
  const k = md(c);
  if (k === 0n) return BbExt.zero();
  if (k === 1n) return a;
  return new BbExt({
    limbs: a.limbs.map((x) => reduceLane(x.mul(Field(k)), LANE_MAX * k)),
  });
}

/** An extension CONSTANT as a `BbExt` of literals — no rows. */
function extConst(limbs: bigint[]): BbExt {
  return BbExt.from(limbs.map((x) => md(x)));
}

/**
 * Walk one table's DAG in circuit and return its ROOT values, in p3's fold
 * order. `base[c]` is the opened value of column `c` at `zeta`; `ext[c]` is the
 * opened value of extension column `c`.
 */
export function evalDagInCircuit(
  t: DagTable,
  base: BbExt[],
  ext: BbExt[],
  opts: DagEvalOpts = {},
): BbExt[] {
  if (base.length !== t.cols.length)
    throw new Error(`${t.name}: ${base.length} base columns supplied, ${t.cols.length} wanted`);
  if (ext.length !== t.extCols.length)
    throw new Error(`${t.name}: ${ext.length} ext columns supplied, ${t.extCols.length} wanted`);
  const v: BbExt[] = new Array(t.nodes.length);
  // Which nodes are compile-time constants, so `constScale` can see them. A
  // `cst` node's VALUE, not its variable.
  const cst: (bigint | undefined)[] = new Array(t.nodes.length);
  for (let i = 0; i < t.nodes.length; i++) {
    const n = t.nodes[i];
    switch (n[0]) {
      case KIND.var:
        // A copy. `strict` still emits it, because that is the object the
        // lowering theorem talks about.
        v[i] = opts.elideVarCopies ? base[n[1]] : copyExt(base[n[1]]);
        break;
      case KIND.evar:
        v[i] = opts.elideVarCopies ? ext[n[1]] : copyExt(ext[n[1]]);
        break;
      case KIND.cst:
        cst[i] = md(BigInt(n[1]));
        v[i] = extConst([cst[i]!, 0n, 0n, 0n]);
        break;
      case KIND.ecst:
        v[i] = extConst([BigInt(n[1]), BigInt(n[2]), BigInt(n[3]), BigInt(n[4])]);
        break;
      case KIND.add:
        v[i] = extAdd(v[n[1]], v[n[2]]);
        break;
      case KIND.sub:
        v[i] = extSub(v[n[1]], v[n[2]]);
        break;
      case KIND.neg:
        v[i] = extSub(BbExt.zero(), v[n[1]]);
        break;
      case KIND.mul: {
        const cl = opts.constScale ? cst[n[1]] : undefined;
        const cr = opts.constScale ? cst[n[2]] : undefined;
        if (cl !== undefined) v[i] = extScaleConstLocal(v[n[2]], cl);
        else if (cr !== undefined) v[i] = extScaleConstLocal(v[n[1]], cr);
        else v[i] = extMul(v[n[1]], v[n[2]]);
        break;
      }
      default:
        throw new Error(`${t.name}: unknown kind ${n[0]} at node ${i}`);
    }
  }
  return t.roots.map((r) => v[r]);
}

/** One reduction per lane — the `Gen1` a `var` node lowers to. Kept so `strict`
 *  emits exactly one operation per node and the row count is a statement about
 *  the object `dagGens_forces` describes. */
function copyExt(a: BbExt): BbExt {
  return new BbExt({ limbs: a.limbs.map((x) => reduceLane(x, LANE_MAX)) });
}

/** p3's accumulator, in circuit: `acc = 0`, `acc = acc*alpha + C_i`, in order. */
export function foldRootsP3(alpha: BbExt, roots: BbExt[]): BbExt {
  let acc = BbExt.zero();
  for (const c of roots) acc = extAdd(extMul(acc, alpha), c);
  return acc;
}

/**
 * The WHOLE root: every table's DAG walked and every one of the 1,093
 * constraints folded into ONE accumulator, base-then-ext within a table and
 * tables in the root's own instance order.
 *
 * ⚑ THIS IS NOT THE BATCH-STARK SHAPE AND SAYS SO. `verify_batch` folds each
 * INSTANCE's constraints against that instance's own opened values and compares
 * each against that instance's own `quotient(zeta) * Z_H(zeta)`; one
 * accumulator over all seven is the ARITHMETIC at the root's real size, not the
 * per-instance comparison. What it is for is the row count: the AIR term in
 * §3.19's projection is the fixture's four constraints, and this is the object
 * that replaces it.
 */
export function evalRootAir(
  d: RootAirDag,
  cols: { base: BbExt[]; ext: BbExt[] }[],
  alpha: BbExt,
  opts: DagEvalOpts = {},
): BbExt {
  if (cols.length !== d.tables.length)
    throw new Error(`${cols.length} column sets for ${d.tables.length} tables`);
  const all: BbExt[] = [];
  d.tables.forEach((t, i) => all.push(...evalDagInCircuit(t, cols[i].base, cols[i].ext, opts)));
  return foldRootsP3(alpha, all);
}

/** The root's total opened-column census, as the DAG numbers it: base columns
 *  (main + preprocessed + selectors + public) and extension columns
 *  (permutation + challenges) per table. */
export function rootColumnShape(d: RootAirDag = rootAirDag()) {
  const per = d.tables.map((t) => ({ name: t.name, base: t.cols.length, ext: t.extCols.length }));
  return {
    per,
    base: per.reduce((a, x) => a + x.base, 0),
    ext: per.reduce((a, x) => a + x.ext, 0),
  };
}

/** Witness a whole table's columns — what a measurement or a chained step does
 *  when the opened values come in as private input. Range-checked, because a
 *  re-witnessed lane is unconstrained until it is. */
export function witnessTableColumns(t: DagTable, seed: bigint): { base: BbExt[]; ext: BbExt[] } {
  const g = new Lcg(seed);
  const mk = (n: number) =>
    Array.from({ length: n }, () => {
      const l = g.nextExt();
      const e = Provable.witness(BbExt, () => BbExt.from(l));
      for (const x of e.limbs) canonicalLane(x, LANE_MAX);
      return e;
    });
  return { base: mk(t.cols.length), ext: mk(t.extCols.length) };
}
