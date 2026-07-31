import { Bool, Field, Poseidon, Provable, Struct, ZkProgram } from 'o1js';
import {
  BbDigest,
  assertDigestInRange,
  foldOpening,
  spongeBB,
  compressBigInt,
  spongeBigInt,
} from './Poseidon2Merkle.js';
import {
  P as BB_P,
  assertLaneLt2p31,
  canonicalLane,
  permBigInt,
  permOutputBound,
  provablePermBounded,
} from './Poseidon2BabyBearW16.js';

// ---------------------------------------------------------------------------
// A DREGG CELL, READ OUT OF THE ANCHORED ROOT — the rung that makes the Mina
// side SEMANTIC rather than a Merkle-membership checker.
//
// ⚑ SAY THE SUBSTRATE OUT LOUD. Two things are borrowed and neither is
// authored here:
//
//   * the PERMUTATION is `Poseidon2BabyBearW16.provablePermBounded`, the
//     w16 Poseidon2 already in this package, whose round constants and bound
//     chain are pinned against the Rust prover (`poseidon2-native-rows`,
//     `rust-gold-vectors`). No permutation, no S-box and no MDS is written
//     below.
//   * the COMMITMENT SHAPE is `Dregg2.Circuit.Emit.KimchiCellCommit.cellCommitOf`
//     — a Lean `def`:
//
//         cellCommit = H4[ H4[bal_lo, bal_hi, nonce, field_0]
//                        , H4[field_1, field_2, field_3, field_4]
//                        , H4[field_5, field_6, field_7, cap_root]
//                        , state_record_digest ]
//
//     with `H4 x = canonical (perm [x0,x1,x2,x3, 4, 0…0])[0]` — the arity
//     domain tag at position 4, capacity zero (`circuit/src/poseidon2.rs:349-362`).
//     `cellCommitOf` is what the DEPLOYED descriptor's four GROUP-4 hash sites
//     bind into the `state_commit` column, and `babybear_forces_cellCommit` is
//     the Lean theorem that says so. This module transcribes that tree; it does
//     not decide what a dregg cell is.
//
// ⚑ WHAT CHANGES, IN ONE SENTENCE. `actOnAttestedLeaf` publishes a FIELD
// ELEMENT — "leaf L is in root R" — and a field element has no meaning; the
// contract cannot tell a balance from a nonce from a nonce-tick's padding. This
// program publishes `{stateCommit, balanceLo, balanceHi, nonce, capRoot}`, each
// one a NAMED column of dregg's EffectVM state block, and the circuit forces
// them to be the pre-image of the committed cell. A contract can then require a
// BALANCE, which is a statement about what dregg did.
//
// ⚑ WHAT IT DOES NOT ESTABLISH, at the resolution measured rather than as a
// caveat paragraph. Three things, and the first is the largest open sin in the
// tree:
//
//   1. NOT that the anchored root is dregg's. `DreggAttestedGate.setDreggRoot`
//      is gated on `placeholderAuth`, a signature by a relay key held in state.
//      The proof obligation beside it (`DreggAnchorStatement`) is a SHAPE
//      constraint — "the anchored value is the Mina image of an MMCS root
//      somebody can open" — and anyone can build a Merkle tree. So this rung
//      reads a cell out of WHATEVER root the relay anchored. It closes the
//      distance from "a leaf" to "a cell's balance"; it closes NOTHING of the
//      distance from "an anchored root" to "dregg's state root".
//   2. NOT that the cell is AUTHORIZED. Authorization is off-AIR in the
//      deployed registry — a turn proof establishes no ownership — so the
//      balance this reads is a committed number, not a number some key was
//      entitled to move.
//   3. NOT that the transition into this state was legal. That is route B
//      (`DreggCellCommitNative`, `routeB_forces_cell_transition`), which proves
//      an `incrementNonceA` step AND the commitment binding but no membership.
//      This is the other half: membership AND the field decode, no transition.
//      Composing them is a real rung and it is not this one.
// ---------------------------------------------------------------------------

/** The lanes of one EffectVM cell state block that `cellCommitOf` absorbs, in
 *  the order it absorbs them. Thirteen: the two balance limbs, the nonce, the
 *  eight generic fields, the cap root, and the state-record digest. */
export const CELL_ROW_LANES = 13;

/** Index of each named lane in the row. These names are `CellState`'s
 *  (`Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState`) and the offsets
 *  are `cellCommitOf`'s absorb positions. */
export const CELL = {
  balanceLo: 0,
  balanceHi: 1,
  nonce: 2,
  field0: 3,
  field1: 4,
  field2: 5,
  field3: 6,
  field4: 7,
  field5: 8,
  field6: 9,
  field7: 10,
  capRoot: 11,
  recordDigest: 12,
} as const;

const LANE_MAX = (1n << 31n) - 1n;

/** `H4` out of circuit — the arity-4 domain tag at position 4, capacity zero,
 *  output lane 0 reduced canonically. */
export function hash4to1BigInt(xs: bigint[]): bigint {
  if (xs.length !== 4) throw new Error(`hash4to1 takes 4 lanes, got ${xs.length}`);
  const state = [...xs, 4n, ...Array(11).fill(0n)];
  return permBigInt(state)[0] % BB_P;
}

/** `H4` in circuit. The four inputs must already be `< 2^31`. */
export function hash4to1(xs: Field[]): Field {
  const state = [...xs, Field(4), ...Array(11).fill(Field(0))];
  const out = provablePermBounded(state, LANE_MAX);
  return canonicalLane(out[0], permOutputBound(LANE_MAX));
}

/** `cellCommitOf` out of circuit, over a 13-lane row. */
export function cellCommitOfBigInt(row: bigint[]): bigint {
  if (row.length !== CELL_ROW_LANES)
    throw new Error(`cellCommitOf takes ${CELL_ROW_LANES} lanes, got ${row.length}`);
  const i1 = hash4to1BigInt([row[0], row[1], row[2], row[3]]);
  const i2 = hash4to1BigInt([row[4], row[5], row[6], row[7]]);
  const i3 = hash4to1BigInt([row[8], row[9], row[10], row[11]]);
  return hash4to1BigInt([i1, i2, i3, row[12]]);
}

/** `cellCommitOf` in circuit. Lanes must already be range-checked. */
export function cellCommitOfCircuit(row: Field[]): Field {
  const i1 = hash4to1([row[0], row[1], row[2], row[3]]);
  const i2 = hash4to1([row[4], row[5], row[6], row[7]]);
  const i3 = hash4to1([row[8], row[9], row[10], row[11]]);
  return hash4to1([i1, i2, i3, row[12]]);
}

/**
 * **The FACT.** What a Mina contract learns about dregg, with names on it.
 *
 * `stateCommit` is the felt the deployed descriptor publishes in the
 * `state_commit` column; the other four are the columns it is the image of. A
 * contract that reads `balanceLo` is reading the same number the AIR froze.
 */
export class DreggCellFact extends Struct({
  stateCommit: Field,
  balanceLo: Field,
  balanceHi: Field,
  nonce: Field,
  capRoot: Field,
}) {
  /** One field element committing to the whole fact, for a `@state` slot. */
  digest(): Field {
    return Poseidon.hash([
      this.stateCommit,
      this.balanceLo,
      this.balanceHi,
      this.nonce,
      this.capRoot,
    ]);
  }
}

/**
 * Build the cell-fact program at a given BabyBear MMCS depth and Pasta anchor
 * depth. Both are compile-time because `Provable.Array` needs a static length;
 * `pastaDepth` is passed in rather than imported so this module does not depend
 * on `DreggPoseidonAttestation`, which depends on it.
 *
 * ```
 * publicInput  = the anchored Pasta root (DreggAttestedGate.dreggRoot)
 * publicOutput = DreggCellFact — five NAMED dregg columns
 * ```
 *
 * Three joins, in three different hashes, and each one is what makes the next
 * meaningful:
 *
 *   1. the 13-lane row is absorbed by the deployed `PaddingFreeSponge` to an
 *      MMCS leaf digest, and that digest is opened `depth` levels of
 *      `compressBB` to a root `R_bb`;
 *   2. `vouch = Poseidon(R_bb)` is folded up `pastaDepth` levels of
 *      Mina-Poseidon as **leaf 0** — left child at every level, so the vouch's
 *      POSITION is structural and the prover has no direction to choose — and
 *      must equal the anchored root. This is byte-for-byte the join
 *      `DreggAnchorStatement.proveAnchorShape` makes, which is why an anchor
 *      set through `setDreggRoot` is openable by this program at all;
 *   3. `stateCommit` is recomputed from the SAME row by `cellCommitOf`, so the
 *      published fact and the committed cell cannot come apart: a prover who
 *      wants a different balance must exhibit a different row, which changes
 *      the leaf digest, which breaks (1).
 */
export function makeDreggCellFactProgram(depth: number, pastaDepth: number) {
  return ZkProgram({
    name: `dregg-cell-fact-d${depth}-p${pastaDepth}`,
    publicInput: Field,
    publicOutput: DreggCellFact,
    methods: {
      proveCellFact: {
        privateInputs: [
          Provable.Array(Field, CELL_ROW_LANES), // the cell's 13 committed lanes
          Provable.Array(BbDigest, depth), //      BabyBear MMCS siblings, bottom-up
          Provable.Array(Bool, depth), //          MMCS path directions
          Provable.Array(Field, pastaDepth), //    Pasta siblings for slot 0
        ],
        async method(
          anchored: Field,
          row: Field[],
          bbSiblings: BbDigest[],
          bbIsRight: Bool[],
          pastaSiblings: Field[],
        ) {
          // ⚑ EVERY WITNESSED LANE IS BOUNDED *AND CANONICAL* HERE, and the
          // second half is not hygiene — it was a live hole, caught by this
          // module's own tamper leg on the first run.
          //
          // `assertLaneLt2p31` alone admits `p + x` for any `x < 2^31 - p`
          // (BabyBear's `p` is 2013265921 and the bound is 2147483647, so there
          // are 134,217,727 aliasing lanes). The permutation reduces mod `p`, so
          // `p + 100` and `100` give the SAME leaf, the SAME root and the SAME
          // anchored value — while the published `balanceLo` is the RAW lane.
          // A prover could therefore open a cell holding 100 and publish a
          // balance of 2,013,266,021, and `actOnCellFact`'s floor check would
          // pass for a floor of two billion. Measured: ACCEPTED before this
          // line existed.
          //
          // `canonicalLane` returns the representative `< p`; asserting it
          // EQUALS the witness REFUSES the alias instead of silently
          // normalising it, which is the fail-closed half — a normalising
          // circuit would publish a number the caller did not witness.
          const canon = row.map((v) => {
            assertLaneLt2p31(v);
            const c = canonicalLane(v, LANE_MAX);
            c.assertEquals(v);
            return c;
          });

          // (1) the row IS the committed leaf, opened to an MMCS root.
          const leaf = spongeBB(canon);
          assertDigestInRange(leaf);
          const bbRoot = foldOpening(leaf, bbSiblings, bbIsRight);

          // (2) the same join `DreggAnchorStatement` makes, at the same slot.
          const vouch = Poseidon.hash(bbRoot.limbs);
          let cur = vouch;
          for (let i = 0; i < pastaDepth; i++) cur = Poseidon.hash([cur, pastaSiblings[i]]);
          cur.assertEquals(anchored);

          // (3) the fact, recomputed from the row rather than witnessed.
          const stateCommit = cellCommitOfCircuit(canon);

          return {
            publicOutput: new DreggCellFact({
              stateCommit,
              balanceLo: canon[CELL.balanceLo],
              balanceHi: canon[CELL.balanceHi],
              nonce: canon[CELL.nonce],
              capRoot: canon[CELL.capRoot],
            }),
          };
        },
      },
    },
  });
}

/** The out-of-circuit twin of (1)+(2): build the anchored root a prover would
 *  have to open against, from a cell row and the sibling material.
 *
 *  ⚑ It calls `Poseidon2Merkle`'s OWN bigint twins (`spongeBigInt`,
 *  `compressBigInt`) — the ones `poseidon2-merkle-rows` pins against the
 *  in-circuit bodies — plus the same `Poseidon.hash`. It is the honest prover,
 *  and the tamper controls use it to build the material a dishonest one would
 *  have. */
export function anchorForCellRow(
  row: bigint[],
  bbSiblings: bigint[][],
  bbIsRight: boolean[],
  pastaSiblings: bigint[],
): { leaf: bigint[]; bbRoot: bigint[]; vouch: Field; anchored: Field } {
  const leaf = spongeBigInt(row).map((x) => x % BB_P);
  let cur = leaf;
  for (let h = 0; h < bbSiblings.length; h++) {
    const [l, r] = bbIsRight[h] ? [bbSiblings[h], cur] : [cur, bbSiblings[h]];
    cur = compressBigInt(l, r).map((x) => x % BB_P);
  }
  const bbRoot = cur;
  const vouch = Poseidon.hash(bbRoot.map((x) => Field(x)));
  let acc = vouch;
  for (let i = 0; i < pastaSiblings.length; i++)
    acc = Poseidon.hash([acc, Field(pastaSiblings[i])]);
  return { leaf, bbRoot, vouch, anchored: acc };
}
