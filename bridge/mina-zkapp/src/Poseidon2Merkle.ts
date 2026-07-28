import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import {
  P,
  assertLaneLt2p31,
  canonicalLane,
  permBigInt,
  permOutputBound,
  provablePermBounded,
  reduceLane,
} from './Poseidon2BabyBearW16.js';

// ---------------------------------------------------------------------------
// RUNG 1 — the Poseidon2-w16-BabyBear MERKLE PATH, as an o1js/Kimchi circuit.
//
// WHY THIS IS THE FIRST RUNG. `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` prices a
// Mina-side verifier of dregg's FRI-STARK and finds the dominant cost is not
// the FRI logic, the AIR, or the S-boxes: it is Merkle openings under the MMCS,
// which is `TruncatedPermutation<Perm, 2, 8, 16>` — EXACTLY ONE width-16
// permutation per node, at a measured 2,600.5 rows each. A depth-`d` opening is
// therefore `d` permutations plus whatever the composition costs, and "whatever
// the composition costs" was the unmeasured term.
//
// ⚑ WHAT THE ONE-PERMUTATION MEASUREMENT COULD NOT SEE. `provablePermBounded`
// returns lanes bounded by ~2^36 (the closing external layer's 35x fan-in), and
// every witnessed sibling lane arrives UNCONSTRAINED. A chain therefore pays,
// per node, 8 witnessed-lane range checks and 8 lane reductions that a single
// permutation never pays. Those are not overhead to be optimised away later;
// without the range checks the bound tracking in `Poseidon2BabyBearW16.ts` is a
// claim about numbers nothing forces to be small, i.e. the circuit is unsound.
//
// THE REFERENT is the DEPLOYED Rust, not a transcription of it:
// `circuit-prove/sketches/mina-pasta-hash-probe`'s `p2merkle` subcommand calls
// `p3_baby_bear::default_babybear_poseidon2_16`, `p3_symmetric::
// TruncatedPermutation<.,2,8,16>` and `p3_symmetric::PaddingFreeSponge<.,16,8,8>`
// at the same `82cfad73` rev the workspace pins, and this module must reproduce
// its output elementwise on inputs it cannot have precomputed.
// ---------------------------------------------------------------------------

export const WIDTH = 16;
export const RATE = 8;
export const DIGEST_ELEMS = 8;

/** The deployed root's input-phase tree height: `|D^0| = 2^22`
 *  (`WRAP_LOG_CEIL = 16` x `log_blowup = 6`, MINA-VERIFIES-DREGG-FRI-SIZE §1.2).
 *  `cap_height = 0`, so paths are never truncated: a full 22 levels. */
export const DEPLOYED_INPUT_PHASE_DEPTH = 22;

/** Commit-phase layer count for the deployed root: `(22 - 6) / 1`. */
export const DEPLOYED_COMMIT_LAYERS = 16;

// ===========================================================================
// 1. Out-of-circuit twins. These call `permBigInt` — the same reference the
//    Lean-pinned KAT validates — so a divergence between them and the circuit
//    is a real disagreement, not a re-implementation gap.
// ===========================================================================

/** `compress(l, r)` = `perm(l || r)[..8]`, the deployed node compression. */
export function compressBigInt(l: bigint[], r: bigint[]): bigint[] {
  return permBigInt([...l, ...r]).slice(0, DIGEST_ELEMS);
}

/**
 * `PaddingFreeSponge<Perm, 16, 8, 8>` over a fixed-width row: OVERWRITE-absorb
 * `RATE` elements at a time, permute after each full block, and permute once
 * more for a partial trailing block — but NOT when the row length is an exact
 * multiple of `RATE` (p3 `sponge.rs:180-200` breaks at `i == 0` without
 * permuting). `ceil(w / 8)` permutations, and zero for an empty row.
 */
export function spongeBigInt(row: bigint[]): bigint[] {
  let state = Array(WIDTH).fill(0n) as bigint[];
  let i = 0;
  while (i < row.length) {
    const n = Math.min(RATE, row.length - i);
    for (let j = 0; j < n; j++) state[j] = row[i + j] % P;
    state = permBigInt(state);
    i += n;
  }
  return state.slice(0, DIGEST_ELEMS);
}

/** The digest of an all-zero subtree of height `h`, `h` in `0..=depth`. */
export function zeroAtBigInt(depth: number): bigint[][] {
  const z: bigint[][] = [Array(DIGEST_ELEMS).fill(0n)];
  for (let h = 1; h <= depth; h++) z.push(compressBigInt(z[h - 1], z[h - 1]));
  return z;
}

/** Fold a leaf digest up an authentication path, returning every node. */
export function foldPathBigInt(
  leaf: bigint[],
  siblings: bigint[][],
  isRight: boolean[],
): bigint[][] {
  const nodes: bigint[][] = [];
  let cur = leaf;
  for (let h = 0; h < siblings.length; h++) {
    cur = isRight[h] ? compressBigInt(siblings[h], cur) : compressBigInt(cur, siblings[h]);
    nodes.push(cur);
  }
  return nodes;
}

/** The o1js twin of the Rust emitter's `sparse_path`. */
export function sparsePathBigInt(
  leaves: bigint[][],
  leafIndex: number,
  depth: number,
): { siblings: bigint[][]; isRight: boolean[]; nodes: bigint[][]; root: bigint[] } {
  const z = zeroAtBigInt(depth);
  let level = leaves.slice();
  let index = leafIndex;
  const siblings: bigint[][] = [];
  const isRight: boolean[] = [];
  for (let h = 0; h < depth; h++) {
    const sib = index ^ 1;
    siblings.push(sib < level.length ? level[sib] : z[h]);
    isRight.push(index % 2 === 1);
    const next: bigint[][] = [];
    for (let i = 0; i < level.length; i += 2)
      next.push(compressBigInt(level[i], i + 1 < level.length ? level[i + 1] : z[h]));
    level = next;
    index >>= 1;
  }
  const nodes = foldPathBigInt(leaves[leafIndex], siblings, isRight);
  return { siblings, isRight, nodes, root: nodes[depth - 1] };
}

// ===========================================================================
// 2. The in-circuit objects.
// ===========================================================================

/** An MMCS digest: 8 BabyBear lanes, each a native Pasta `Field`. */
export class BbDigest extends Struct({
  limbs: Provable.Array(Field, DIGEST_ELEMS),
}) {
  static from(v: bigint[] | Field[]): BbDigest {
    return new BbDigest({ limbs: v.map((x) => (typeof x === 'bigint' ? Field(x) : x)) });
  }
  static zero(): BbDigest {
    return BbDigest.from(Array(DIGEST_ELEMS).fill(0n));
  }
  toBigInts(): bigint[] {
    return this.limbs.map((x) => x.toBigInt() % P);
  }
}

/** Range-check every lane of a WITNESSED digest to `< 2^31`. Mandatory before
 *  the digest enters the bound chain — see the header. */
export function assertDigestInRange(d: BbDigest) {
  for (const l of d.limbs) assertLaneLt2p31(l);
}

/** `compress(l, r)` in circuit, leaving lanes `< 2^31` so the result can be
 *  fed straight back in. Inputs must already be `< 2^31`. */
export function compressBB(l: BbDigest, r: BbDigest): BbDigest {
  const out = provablePermBounded([...l.limbs, ...r.limbs], (1n << 31n) - 1n).slice(
    0,
    DIGEST_ELEMS,
  );
  const bound = permOutputBound((1n << 31n) - 1n);
  return new BbDigest({ limbs: out.map((x) => reduceLane(x, bound)) });
}

/** The `PaddingFreeSponge` leaf hash in circuit, for a compile-time row width.
 *  Row lanes must already be range-checked. */
export function spongeBB(row: Field[]): BbDigest {
  const bound = permOutputBound((1n << 31n) - 1n);
  let state: Field[] = Array(WIDTH).fill(Field(0));
  let stateMax = 0n;
  let i = 0;
  while (i < row.length) {
    const n = Math.min(RATE, row.length - i);
    // Absorb is OVERWRITE, so the absorbed lanes are the witness's bound and
    // only the untouched capacity carries the previous permutation's.
    const lanes = state.map((v, j) => (j < n ? row[i + j] : reduceLane(v, stateMax)));
    state = provablePermBounded(lanes, (1n << 31n) - 1n);
    stateMax = bound;
    i += n;
  }
  return new BbDigest({ limbs: state.slice(0, DIGEST_ELEMS).map((x) => reduceLane(x, stateMax)) });
}

/** Canonicalise a digest (`< p` per lane) — for comparison against a value the
 *  Rust side emitted, or against a public input. */
export function canonicalDigest(d: BbDigest): BbDigest {
  return new BbDigest({ limbs: d.limbs.map((x) => canonicalLane(x, (1n << 31n) - 1n)) });
}

/** Conditional swap: returns `(left, right)` for this level, where `isRight`
 *  says the CURRENT node is the right child. */
export function condSwap(cur: BbDigest, sib: BbDigest, isRight: Bool): [BbDigest, BbDigest] {
  const left: Field[] = [];
  const right: Field[] = [];
  for (let j = 0; j < DIGEST_ELEMS; j++) {
    left.push(Provable.if(isRight, sib.limbs[j], cur.limbs[j]));
    right.push(Provable.if(isRight, cur.limbs[j], sib.limbs[j]));
  }
  return [new BbDigest({ limbs: left }), new BbDigest({ limbs: right })];
}

/**
 * **The Rung-1 statement.** Fold `leaf` up `depth` levels of `siblings` under
 * the deployed compression and return the root, canonical.
 *
 * Every witnessed lane is range-checked here rather than by the caller: a
 * verification routine that trusts its inputs to be small is the shape of an
 * unsound circuit that measures fine.
 */
export function foldOpening(
  leaf: BbDigest,
  siblings: BbDigest[],
  isRight: Bool[],
): BbDigest {
  assertDigestInRange(leaf);
  let cur = leaf;
  for (let h = 0; h < siblings.length; h++) {
    assertDigestInRange(siblings[h]);
    const [l, r] = condSwap(cur, siblings[h], isRight[h]);
    cur = compressBB(l, r);
  }
  return canonicalDigest(cur);
}

// ===========================================================================
// 3. The ZkProgram.
// ===========================================================================

/**
 * A `ZkProgram` that verifies a depth-`depth` BabyBear-Poseidon2 MMCS opening.
 *
 *   publicInput  = the MMCS root (8 canonical BabyBear lanes)
 *   publicOutput = the opened leaf digest, canonical — a proof-carrying claim
 *                  about WHAT was opened, not merely that something was
 *
 * The depth is baked in (`Provable.Array` needs a static length), so this is a
 * factory. `DEPLOYED_INPUT_PHASE_DEPTH` is the one that prices the real root.
 */
export function makePoseidon2MerkleProgram(depth: number) {
  return ZkProgram({
    name: `dregg-poseidon2-merkle-d${depth}`,
    publicInput: BbDigest,
    publicOutput: BbDigest,
    methods: {
      proveOpening: {
        privateInputs: [
          BbDigest, //                          the opened leaf digest
          Provable.Array(BbDigest, depth), //   siblings, bottom-up
          Provable.Array(Bool, depth), //       currentIsRightChild per level
        ],
        async method(root: BbDigest, leaf: BbDigest, siblings: BbDigest[], isRight: Bool[]) {
          const got = foldOpening(leaf, siblings, isRight);
          for (let j = 0; j < DIGEST_ELEMS; j++) got.limbs[j].assertEquals(root.limbs[j]);
          return { publicOutput: canonicalDigest(leaf) };
        },
      },
    },
  });
}

/**
 * A `ZkProgram` that hashes a fixed-width row with the deployed leaf sponge and
 * then verifies the resulting digest's opening. This is the shape of a FRI
 * INPUT-phase opening: the verifier never sees the leaf digest, it sees the
 * opened ROW and must hash it itself.
 */
export function makePoseidon2LeafOpeningProgram(depth: number, rowWidth: number) {
  return ZkProgram({
    name: `dregg-poseidon2-leaf-opening-d${depth}-w${rowWidth}`,
    publicInput: BbDigest,
    publicOutput: BbDigest,
    methods: {
      proveRowOpening: {
        privateInputs: [
          Provable.Array(Field, rowWidth), //   the opened row
          Provable.Array(BbDigest, depth),
          Provable.Array(Bool, depth),
        ],
        async method(root: BbDigest, row: Field[], siblings: BbDigest[], isRight: Bool[]) {
          for (const v of row) assertLaneLt2p31(v);
          const leaf = spongeBB(row);
          const got = foldOpening(leaf, siblings, isRight);
          for (let j = 0; j < DIGEST_ELEMS; j++) got.limbs[j].assertEquals(root.limbs[j]);
          return { publicOutput: canonicalDigest(leaf) };
        },
      },
    },
  });
}
