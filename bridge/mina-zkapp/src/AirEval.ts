import { Field, Provable } from 'o1js';
import { P, canonicalLane, reduceLane } from './Poseidon2BabyBearW16.js';
import {
  BbExt,
  EXT_D,
  assertExtInRange,
  extAdd,
  extMul,
  extOfBase,
  extPowPow2,
  extSub,
} from './FriQueryStep.js';
import { extInverse, extOne, ROOT_TABLES } from './DeepQuotient.js';

// ---------------------------------------------------------------------------
// RUNG 7 — THE AIR CONSTRAINT EVALUATION AT ZETA.
//
// ⚑ WHAT THIS IS AND, MORE IMPORTANTLY, WHAT IT IS NOT.
//
// The FRI walk (rungs 1-5) authenticates a value; the DEEP quotient (rung 6)
// ties that value to the CLAIMED out-of-domain evaluations `f(zeta)`. Neither
// says the claimed evaluations satisfy dregg's constraint system. Without this
// rung a verifier certifies that some low-degree function takes some values at
// zeta — a true statement about an arbitrary polynomial.
//
// The object that closes it is `VerifierData::verify_constraints_with_lookups`
// (`p3-batch-stark/src/verifier/data.rs:49-102`):
//
//     accumulator = sum_i alpha^i * C_i(trace_local, trace_next, prep, ...)
//     accumulator * inv_vanishing(zeta)  ==  quotient(zeta)
//
// with `quotient(zeta)` recomposed from the opened chunks by Lagrange over the
// chunk domains (`p3-uni-stark/src/verifier.rs:59-96`).
//
// ⚑ THIS MODULE BUILDS THE PROTOCOL ARITHMETIC AROUND `C_i`, NOT `C_i`.
// The selectors, the alpha-folding accumulator, the chunk recomposition and the
// closing equality are all here and all MEASURED. The constraints THEMSELVES —
// dregg's 7 AIRs — are not, and their COUNT is the one quantity in this whole
// document that nobody has taken. So the price is reported as an explicit linear
// function `A + N*h` with `A` and `h` measured and `N` named as uncounted,
// rather than as a number with an invented `N` inside it.
//
// ⚑ AND THE ROOT'S TABLE SET IS THE 7-TABLE ONE. `degree_bits = [9,9,15,14,15]`
// is the BN254 SHRINK proof (§1.2), not the root; quoting it here would
// under-count the AIR side by more than an order of magnitude. The root is
// `Const, Public, Alu, poseidon2-W16, poseidon2-W24, recompose, expose_claim` at
// 940 main / 175 preprocessed columns (§1.3).
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

/** `LagrangeSelectors` at an out-of-domain point
 *  (`p3-commit/src/domain.rs:262-271`). */
export type Selectors = {
  isFirstRow: BbExt;
  isLastRow: BbExt;
  isTransition: BbExt;
  invVanishing: BbExt;
};

/**
 * `Z_H(point)` for `H` the coset `shift * <g>` of size `2^logSize`:
 *
 *     Z_H(p) = (p * shift^{-1})^{2^logSize} - 1
 *
 * `shiftInv` is a COMPILE-TIME base constant (the domain's shift is fixed by the
 * protocol, not by the proof), so the scale is free and the whole cost is the
 * `logSize` extension SQUARINGS. That is the term that makes the AIR side scale
 * with `degree_bits` — and `degree_bits` for the root is itself uncounted
 * (§3.14). This module prices the ACCUMULATOR shape: `min_trace_height = 2^16`
 * floors every table to `logSize = 16` (§1.2, `accumulator.rs:236,242-248`).
 */
export function vanishingAtPoint(point: BbExt, logSize: number, shiftInv: bigint): BbExt {
  const unshifted =
    shiftInv === 1n
      ? point
      : new BbExt({
          limbs: point.limbs.map((x) => reduceLane(x.mul(Field(shiftInv)), LANE_MAX * LANE_MAX)),
        });
  const pow = extPowPow2(unshifted, logSize);
  return extSub(pow, extOne());
}

/**
 * `selectors_at_point`, in circuit. Three extension inverses and `logSize`
 * squarings; `isTransition` is a subtraction.
 *
 * ⚑ `is_first_row` and `is_last_row` are DIVISIONS, and p3 takes them with `/`,
 * which panics on a zero denominator. In circuit the same thing is a witnessed
 * inverse with a multiplicative check, so `zeta` landing exactly on the first or
 * last row of the domain makes the statement UNSATISFIABLE instead of wrong —
 * which is the correct reading of a verifier that would have panicked.
 */
export function selectorsAtPoint(
  zeta: BbExt,
  logSize: number,
  shiftInv: bigint,
  subgroupGenInv: bigint,
): Selectors {
  const unshifted =
    shiftInv === 1n
      ? zeta
      : new BbExt({
          limbs: zeta.limbs.map((x) => reduceLane(x.mul(Field(shiftInv)), LANE_MAX * LANE_MAX)),
        });
  const zH = extSub(extPowPow2(unshifted, logSize), extOne());
  const isTransition = extSub(unshifted, extOfBase(Field(subgroupGenInv)));
  return {
    isFirstRow: extMul(zH, extInverse(extSub(unshifted, extOne()))),
    isLastRow: extMul(zH, extInverse(isTransition)),
    isTransition,
    invVanishing: extInverse(zH),
  };
}

/**
 * `VerifierConstraintFolder`'s accumulator: `acc <- acc*alpha + C` per
 * constraint (`p3-uni-stark/src/folder.rs`, `assert_zero`).
 *
 * The COST OF `C` ITSELF IS NOT HERE. This is the folding, which every
 * constraint pays regardless of its shape, and it is the unit the AIR side's
 * price is linear in.
 */
export function foldConstraints(alpha: BbExt, constraints: BbExt[]): BbExt {
  if (constraints.length === 0) return BbExt.zero();
  let acc = constraints[0];
  for (let i = 1; i < constraints.length; i++) acc = extAdd(extMul(acc, alpha), constraints[i]);
  return acc;
}

/**
 * `recompose_quotient_from_chunks` (`p3-uni-stark/src/verifier.rs:59-96`).
 *
 * `zps[i] = prod_{j != i} Z_{D_j}(zeta) * Z_{D_j}(first_point(D_i))^{-1}`.
 *
 * ⚑ THE SECOND FACTOR IS A COMPILE-TIME CONSTANT. `first_point(D_i)` and every
 * chunk domain's shift are protocol data, so `Z_{D_j}(first_point(D_i))^{-1}` is
 * a base-field constant a circuit folds in for free. Only `Z_{D_j}(zeta)` is
 * live, and there are `n_chunks` of them, each `logChunkSize` squarings. Missing
 * that would triple the measured cost and is exactly the kind of thing a row
 * count with no referent gets wrong.
 *
 * `chunks[c]` is the chunk's opened value as `D` extension elements; p3
 * reassembles it with `from_ext_basis_coefficients`, i.e. `sum_k chunks[c][k] *
 * X^k` over the extension's own basis — four multiplications by the CONSTANT
 * `X^k`, which for a binomial extension is a lane rotation with a `W`-fold.
 */
export function recomposeQuotient(opts: {
  zeta: BbExt;
  chunks: BbExt[][];
  logChunkSize: number;
  chunkShiftInvs: bigint[];
  /** `Z_{D_j}(first_point(D_i))^{-1}`, base constants, indexed `[i][j]`. */
  lagrangeConsts: bigint[][];
}): BbExt {
  const { zeta, chunks, logChunkSize, chunkShiftInvs, lagrangeConsts } = opts;
  const n = chunks.length;
  const zAtZeta = chunkShiftInvs.map((s) => vanishingAtPoint(zeta, logChunkSize, s));
  let acc = BbExt.zero();
  for (let i = 0; i < n; i++) {
    let zp: BbExt | null = null;
    for (let j = 0; j < n; j++) {
      if (j === i) continue;
      const term = extScaleConst(zAtZeta[j], lagrangeConsts[i][j]);
      zp = zp === null ? term : extMul(zp, term);
    }
    const value = fromExtBasisCoefficients(chunks[i]);
    acc = extAdd(acc, zp === null ? value : extMul(zp, value));
  }
  return acc;
}

/** Scale by a COMPILE-TIME base constant — no witness, no range check. */
export function extScaleConst(a: BbExt, c: bigint): BbExt {
  if (c === 1n) return a;
  return new BbExt({
    limbs: a.limbs.map((x) => reduceLane(x.mul(Field(c % P)), LANE_MAX * P)),
  });
}

/**
 * `Challenge::from_ext_basis_coefficients(ch)` = `sum_k ch[k] * X^k`.
 *
 * `X^k` is the k-th basis element, so multiplying by it is a SHIFT of the
 * coefficient vector with the overflow folded back by `W = 11` — no general
 * extension multiply is needed, which is why this term is nearly free and why
 * counting it as `D` extension multiplies would be wrong.
 */
export function fromExtBasisCoefficients(ch: BbExt[]): BbExt {
  const W = 11n;
  const out: Field[] = [Field(0), Field(0), Field(0), Field(0)];
  const bound: bigint[] = [0n, 0n, 0n, 0n];
  for (let k = 0; k < ch.length; k++)
    for (let i = 0; i < EXT_D; i++) {
      // `ch[k][i] * X^{k+i}`; indices at or past D wrap to `i+k-D` scaled by W.
      const d = k + i;
      const slot = d < EXT_D ? d : d - EXT_D;
      const scale = d < EXT_D ? 1n : W;
      out[slot] = out[slot].add(scale === 1n ? ch[k].limbs[i] : ch[k].limbs[i].mul(Field(W)));
      bound[slot] += scale * LANE_MAX;
    }
  return new BbExt({ limbs: out.map((x, i) => reduceLane(x, bound[i])) });
}

/**
 * **The Rung-7 statement, for ONE instance.** The closing equality of a
 * batch-STARK verifier:
 *
 *     accumulator * inv_vanishing(zeta) == quotient(zeta)
 *
 * with `quotient(zeta)` recomposed from the opened chunks. Everything except the
 * constraints' own evaluation is here.
 */
export function assertQuotientConsistency(opts: {
  zeta: BbExt;
  alpha: BbExt;
  constraints: BbExt[];
  logSize: number;
  shiftInv: bigint;
  subgroupGenInv: bigint;
  chunks: BbExt[][];
  logChunkSize: number;
  chunkShiftInvs: bigint[];
  lagrangeConsts: bigint[][];
}) {
  const sels = selectorsAtPoint(opts.zeta, opts.logSize, opts.shiftInv, opts.subgroupGenInv);
  const acc = foldConstraints(opts.alpha, opts.constraints);
  const quotient = recomposeQuotient({
    zeta: opts.zeta,
    chunks: opts.chunks,
    logChunkSize: opts.logChunkSize,
    chunkShiftInvs: opts.chunkShiftInvs,
    lagrangeConsts: opts.lagrangeConsts,
  });
  const lhs = extMul(acc, sels.invVanishing);
  for (let j = 0; j < EXT_D; j++)
    canonicalLane(lhs.limbs[j], LANE_MAX).assertEquals(canonicalLane(quotient.limbs[j], LANE_MAX));
  // The selectors are returned into the constraint evaluation in a real
  // verifier; sealing them here keeps the measured circuit from folding them
  // away as dead.
  sels.isFirstRow.limbs.forEach((x) => x.seal());
  sels.isLastRow.limbs.forEach((x) => x.seal());
  sels.isTransition.limbs.forEach((x) => x.seal());
}

// ===========================================================================
// The root's shape, for measurement.
// ===========================================================================

/**
 * The accumulator shape's uniform log trace height.
 *
 * `Accumulator::finalize` floors every table to `min_trace_height = 2^16`
 * (`circuit-prove/src/accumulator.rs:236,242-248`), which is the shape
 * `MINA-VERIFIES-DREGG-FRI-SIZE.md` prices throughout and the one the Lean
 * ledger pins. `prove_chain_core_rotated` uses natural heights instead — max
 * ~2^15 — and the AIR side differs by one squaring per instance between them.
 */
export const ROOT_LOG_TRACE_HEIGHT = 16;
/** `n_chunks = 2` — §1.3, from `constraint_degree = 3`. */
export const ROOT_N_CHUNKS = 2;

/** A witnessed instance of the given shape — for `getRows()`. */
export function witnessInstanceShape(numConstraints: number) {
  const wit = <T>(f: () => T, t: any) => Provable.witness(t, f);
  return {
    zeta: wit(() => BbExt.from([3n, 1n, 0n, 0n]), BbExt),
    alpha: wit(() => BbExt.from([5n, 0n, 1n, 0n]), BbExt),
    constraints: Array.from({ length: numConstraints }, () => wit(() => BbExt.zero(), BbExt)),
    chunks: Array.from({ length: ROOT_N_CHUNKS }, () =>
      Array.from({ length: EXT_D }, () => wit(() => BbExt.zero(), BbExt)),
    ),
  };
}

/**
 * The Lagrange constants for `n` chunk domains, as p3 computes them.
 *
 * These are protocol constants — `Z_{D_j}(first_point(D_i))^{-1}` — and the
 * circuit folds them in for free. Their VALUES do not change the row count, so
 * distinct non-zero placeholders are used and the fact that they are constants
 * is what is being measured.
 */
export function placeholderLagrangeConsts(n: number): bigint[][] {
  return Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => BigInt(7 + 13 * i + 29 * j) % P),
  );
}

/** The root's per-instance constraint counts are UNCOUNTED. This records the
 *  column census they would be compared against, so a reader can see what a
 *  given constraints-per-column ratio implies. */
export function rootColumnCensus() {
  const main = ROOT_TABLES.reduce((a, t) => a + t.main, 0);
  const prep = ROOT_TABLES.reduce((a, t) => a + t.prep, 0);
  return { tables: ROOT_TABLES.length, main, prep, total: main + prep };
}

/** Sanity: the range plumbing this module leans on is live. */
export function assertExtWitnessed(e: BbExt) {
  assertExtInRange(e);
}
