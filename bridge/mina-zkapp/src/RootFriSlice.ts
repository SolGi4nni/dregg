import {
  Bool,
  DynamicProof,
  FeatureFlags,
  Field,
  Poseidon,
  Provable,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import {
  P,
  assertLaneLt2p31,
  canonicalLane,
  permBigInt,
  permOutputBound,
  provablePermBounded,
  reduceLane,
} from './Poseidon2BabyBearW16.js';
import { BbDigest } from './Poseidon2Merkle.js';
import { babyBearSuite } from './HashSuites.js';
import type { MerkleSuite } from './HashSuiteType.js';
import {
  BbExt,
  EXT_D,
  assertExtInRange,
  cosetPointFromBits,
  evalFinalPoly,
  extAdd,
  extAddBigInt,
  extMul,
  extMulBigInt,
  extOfBase,
  extSub,
  extSubBigInt,
  finalEvalPointFromBits,
  foldRowArity2,
  foldRowArity2BigInt,
  nextCosetPoint,
} from './FriQueryStep.js';
import { assertLowBitsSplit, assertLowBitsZero } from './FriChallenger.js';
import {
  deepQueryPoint,
  deepQueryPointBigInt,
  extInverse,
  extInvBigInt,
  extSubBase,
} from './DeepQuotient.js';
import { dagDigestOfChunkDigests, digestOfLanes, stepBoundary, airTerminalSeal } from './RootAirChain.js';
import {
  CHAL_RATE,
  CHAL_WIDTH,
  airColumnIndex,
  dagTableName,
  EXT_LANES,
  FriLaneTable,
  FriPlan,
  FriShape,
  LANES_PER_DIGEST,
  OpenedPlan,
  RealRootFri,
  Segment,
  SegmentedWalk,
  WalkHash,
  assertWalkHashMatchesSuite,
  segmentReads,
} from './RootFriWalk.js';

// ---------------------------------------------------------------------------
// THE BRAID — the FRI walk as side-loaded slices whose FIRST link is the AIR
// chain's terminal seal.
//
// ⚑ WHAT THE JOIN IS, IN ONE SENTENCE. Slice 0 of this chain takes AIR slice 6's
// proof as a `DynamicProof`, pins its verification key hash to a compile-time
// constant, re-derives `dagDigest` from the AIR chain's OWN chunked column
// commitment, recomputes `airTerminalSeal(dagDigest, digest(acc), 7)` and asserts
// it IS that proof's public output — and then reads the DEEP quotient's `f(z)`
// out of those same chunks. So the FRI walk authenticates the numbers the AIR
// chain folded, rather than numbers of its own.
//
// ⚑ WHAT IT ESTABLISHES AND WHAT IT DOES NOT, SAID HERE SO IT IS NOT INFERRED.
// The AIR half proves: at the opened values under `dagDigest`, every one of the
// root's 1,093 constraints folds to `acc`, and `acc` is the α-weighted sum of
// p3's seven per-instance accumulators. The FRI half proves: those opened values
// open, under the commitments the transcript absorbed, at the query indices that
// transcript derived, and the resulting DEEP quotients fold through sixteen
// layers onto the committed final polynomial. Together they say the closing
// equalities hold **at values dregg committed to**. They do NOT say the
// committed function is low-degree — that is the FRI soundness argument itself,
// and it is exactly as undischarged here as it is everywhere else in this tree.
// Nor do they bind the challenger state the FRI transcript is entered at to the
// batch-STARK's own observes: that state is a committed WITNESS here, §3.14's
// residual 1, and it is the largest thing between this chain and a verifier.
//
// ⚑ THE VK PIN IS LOAD-BEARING AND IS THE SAME OBLIGATION §3.27 PAID. o1js:
// a `DynamicProof` circuit "makes no assertions about the verificationKey used
// on its own", so `prev.verify(vk)` is satisfied by ANY program's proof paired
// with that program's own key. `vk.hash.assertEquals(Field(pinned))` is what
// puts the identity back, and slice 0's pin is what makes this ONE chain with
// the AIR half rather than two chains that happen to agree on a number.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;
const md = (x: bigint) => ((x % P) + P) % P;

/** `e · X^j` in `BinomialExtensionField<BabyBear,4>` — a limb rotation with the
 *  binomial `W = 11` on the limbs that wrap past degree 3. Three additions a
 *  column rather than a general extension multiply. */
export function extShift(e: BbExt, j: number): BbExt {
  if (j === 0) return e;
  const out: Field[] = [];
  for (let i = 0; i < EXT_D; i++)
    out.push(
      i >= j
        ? e.limbs[i - j]
        : reduceLane(e.limbs[i - j + EXT_D].mul(Field(11n)), 11n * LANE_MAX),
    );
  return new BbExt({ limbs: out });
}

/** The AIR chain's slice count — the step index this chain continues from. */
export const AIR_SLICES = 7;
/** The AIR chain's chunking, which this chain must reproduce EXACTLY or it
 *  computes a different `dagDigest` and the seal never matches. */
export const AIR_CHUNK_EXT = 64;
export const AIR_CHUNK_LANES = AIR_CHUNK_EXT * EXT_LANES;

// ===========================================================================
// 1. The lane tables, as values.
// ===========================================================================

/** The FRI-side lane table, filled from the dumped proof. */
export function friLaneValues(
  real: RealRootFri,
  shape: FriShape,
  ft: FriLaneTable,
  op: OpenedPlan,
): bigint[] {
  const v = new Array<bigint>(ft.nLanes).fill(0n);
  const put = (at: number, xs: readonly (number | string | bigint)[]) =>
    xs.forEach((x, i) => (v[at + i] = BigInt(x as any)));
  //  ⚑ A CARRIED WALK COMMITS THE CHALLENGES AND NOT THE STATE THAT WOULD HAVE
  //  PRODUCED THEM; a deriving one commits the state. Exactly one of the two
  //  regions exists in any table, so this is not a choice about what to fill.
  if (ft.carried === null) put(ft.chalState, real.challengerStateBeforeFriAlpha.sponge);
  else {
    put(ft.carried.friAlpha, real.friAlpha);
    real.betas.forEach((b, r) => put(ft.carried!.betas[r], b));
    real.queries.forEach((q, qi) => (v[ft.carried!.qidx[qi]] = BigInt(q.index)));
  }
  real.commits.forEach((c, r) => put(ft.commit[r], c));
  real.inputRounds.forEach((r, i) => put(ft.inputCommit[i], r.commit));
  real.finalPoly.forEach((c, i) => put(ft.finalPoly[i], c));
  v[ft.powWitness] = BigInt(real.queryPowWitness);
  real.inputRounds.forEach((r, ri) =>
    r.matrices.forEach((m, mi) => m.points.forEach((p, pi) => put(ft.z[ri][mi][pi], p))),
  );
  //  f(z): only the ones the AIR does not hold.
  for (const e of real.openedEvals) {
    const cols = op.refs[e.round][e.matrix][e.pointIndex];
    e.values.forEach((val, c) => {
      const r = cols[c];
      if (r.where === 'fri') put(r.at, val);
    });
  }
  //  f(x): every opened row of every query.
  real.queries.forEach((q, qi) =>
    q.inputBatches.forEach((b, ri) =>
      b.rows.forEach((row, mi) => put(ft.fx[qi][ri][mi], row)),
    ),
  );
  return v;
}

/** The AIR chain's column assignment, as lanes, padded to whole chunks. */
export function airLaneValues(base: bigint[][], ext: bigint[][]): bigint[] {
  const all = [...base, ...ext];
  const nChunks = Math.ceil(all.length / AIR_CHUNK_EXT);
  while (all.length < nChunks * AIR_CHUNK_EXT) all.push([0n, 0n, 0n, 0n]);
  return all.flat();
}

// ===========================================================================
// 2. The chunked commitment — the SAME shape `RootAirChain.sliceCommitment`
//    builds, over a lane table rather than an extension one.
// ===========================================================================

/**
 * ⚑ THE SECOND BLOCKER, CLOSED — and the note it replaces is kept because the
 * shape it names is the one a future hash will hit again.
 *
 * `chunkedCommitment` used to put `canonicalLane(l, 2^31 − 1)` on EVERY lane it
 * commits, and the boundary on every carried slot. That is right for the
 * deployed walk, whose lane table is BabyBear lanes end to end. It is NOT right
 * for a Pasta-hashed one: there the four round commitments, the sixteen
 * commit-phase commitments and the challenger state are NATIVE PASTA ELEMENTS
 * sharing a lane space with BabyBear opened values, and canonicalising a
 * 255-bit digest to `< p_BabyBear` refuses every honest proof.
 *
 * So the lane table is no longer homogeneous: `FriLaneTable.kinds` and
 * `SlotLayout.kinds` say, per entry, whether a range check means anything, and
 * both are functions of `WalkHash.digestKind`. `kinds` is a REQUIRED argument
 * here rather than an optional one, because a default would silently
 * canonicalise a native digest at exactly the call site this comment is about.
 *
 * ⚠ AND OMITTING THE CHECK IS NOT A SAVING BEING TAKEN. A native lane needs no
 * bound because the field IS the domain; a BabyBear lane still gets its check,
 * at both hashes, because the leaf sponge's packing argument rests on it
 * (`PastaMmcs.packSlot`: eight lanes at radix `2^31` are injective only if each
 * is `< 2^31`).
 */
export function chunkedCommitment(
  nChunks: number,
  chunkLanes: number,
  readsChunks: number[],
  readLanes: Field[],
  otherDigests: Field[],
  /** The KIND of each lane of `readLanes`, in the same order — `1` native, `0`
   *  BabyBear. */
  kinds: Uint8Array,
): Field {
  if (kinds.length < readLanes.length)
    throw new Error(
      `chunkedCommitment was given ${readLanes.length} lanes and ${kinds.length} lane kinds — a ` +
        'commitment whose kinds it does not know is one that cannot range-check correctly',
    );
  readLanes.forEach((l, i) => {
    if (kinds[i] === 0) canonicalLane(l, LANE_MAX);
  });
  const computed: Field[] = [];
  for (let c = 0; c < readsChunks.length; c++)
    computed.push(digestOfLanes(readLanes.slice(c * chunkLanes, (c + 1) * chunkLanes)));
  const digests: Field[] = [];
  let ci = 0;
  let oi = 0;
  for (let c = 0; c < nChunks; c++)
    digests.push(readsChunks.includes(c) ? computed[ci++] : otherDigests[oi++]);
  return dagDigestOfChunkDigests(digests);
}

/** The lane kinds a slice's READ region has, in the order `chunkedCommitment`
 *  receives them: the loaded chunks, concatenated, in index order. */
export function readLaneKinds(
  kinds: Uint8Array,
  readsChunks: number[],
  chunkLanes: number,
): Uint8Array {
  const out = new Uint8Array(readsChunks.length * chunkLanes);
  readsChunks.forEach((c, i) => {
    for (let j = 0; j < chunkLanes; j++) out[i * chunkLanes + j] = kinds[c * chunkLanes + j] ?? 0;
  });
  return out;
}

/** Every lane a BabyBear lane — the AIR chain's assignment, at either hash. */
export const babyBearKinds = (n: number) => new Uint8Array(n);

export function chunkDigestsBigInt(lanes: bigint[], nChunks: number, chunkLanes: number): Field[] {
  const out: Field[] = [];
  for (let c = 0; c < nChunks; c++)
    out.push(digestOfLanes(lanes.slice(c * chunkLanes, (c + 1) * chunkLanes).map((x) => Field(x))));
  return out;
}

// ===========================================================================
// 3. The out-of-circuit twin.
// ===========================================================================

export type TwinState = Map<number, bigint>;

/** A value the walk produced that p3's own verifier also produced, so the two
 *  can be compared. ⚑ This is the instrument a slice run cannot be: the first
 *  assertion against a committed Merkle root is ~12 slices in and the fold chain
 *  ~30, so a wrong convention would compile and prove cleanly for as far as any
 *  affordable run reaches. */
export type TwinCheck = {
  kind: 'inputRoot' | 'ro' | 'fold' | 'final' | 'commitRoot' | 'preSealZeta' | 'preSealChal';
  q: number;
  round?: number;
  h?: number;
  i?: number;
  got: bigint[];
  /** For the preamble seal and `commitRoot`: the committed value `got` must equal. */
  want?: bigint[];
};

export type WalkTwin = {
  /** Slot values at every segment boundary, restricted to `liveIn[k]`. */
  carry: bigint[][];
  /** The self-authenticating data each segment consumes, as lanes. */
  aux: bigint[][];
  /** The final slot state — where the derived challenges live. */
  at: TwinState;
  checks: TwinCheck[];
};

const extOf = (st: TwinState, ids: number[]) => ids.map((i) => st.get(i) ?? 0n);
const setExt = (st: TwinState, ids: number[], v: bigint[]) => ids.forEach((id, i) => st.set(id, v[i]));

/** The 22 index bits of a canonical query-index lane. */
const bitsOfBigInt = (v: bigint, n: number) =>
  Array.from({ length: n }, (_, i) => ((v >> BigInt(i)) & 1n) === 1n);

/**
 * **THE TWIN.** The whole walk, out of circuit, in the same order and by the
 * same functions the circuit calls — `permBigInt`, `compressBigInt`,
 * `extMulBigInt`, `foldRowArity2BigInt`, `deepQueryPointBigInt`. It exists for
 * two reasons: to supply each slice its carry, and so a process that compiled
 * NOTHING can check every public field the chain emits.
 */
export function walkTwin(
  w: SegmentedWalk,
  shape: FriShape,
  ft: FriLaneTable,
  op: OpenedPlan,
  friLanes: bigint[],
  airLanes: bigint[],
  real: RealRootFri,
  /** ⚑ THE HASH, AS THE SUITE ITSELF. Defaulted to the deployed one so every
   *  existing caller is unchanged; taken as the SUITE rather than a name so the
   *  twin calls the same `compressBigInt`/`spongeStream` the circuit's suite
   *  calls and the pair cannot drift into two hashes. */
  suite: MerkleSuite<any> = babyBearSuite,
): WalkTwin {
  assertWalkHashMatchesSuite(w.hash, suite as any);
  const D = w.hash.digestLanes;
  const SS = suite.spongeStream;
  const S = w.slots;
  const K = shape.knobs;
  const lgmh = K.logGlobalMaxHeight;
  const st: TwinState = new Map();
  const carry: bigint[][] = new Array(w.segs.length + 1);
  const aux: bigint[][] = new Array(w.segs.length);
  const checks: TwinCheck[] = [];
  const rollAt = (r: number) => shape.heights.indexOf(lgmh - 1 - r) > 0;
  const fzOf = (round: number, mat: number, pt: number, c: number): bigint[] => {
    const r = op.refs[round][mat][pt][c];
    return r.where === 'air'
      ? airLanes.slice(r.at * EXT_LANES, (r.at + 1) * EXT_LANES)
      : friLanes.slice(r.at, r.at + EXT_LANES);
  };
  const idxBits = (q: number) => bitsOfBigInt(st.get(S.qidx[q])!, K.indexBits);

  for (let k = 0; k < w.segs.length; k++) {
    carry[k] = w.liveIn[k].map((s) => st.get(s) ?? 0n);
    const s = w.segs[k];
    const a: bigint[] = [];
    switch (s.t) {
      case 'duplex': {
        //  ⚑ `entry` REPLACED `k === 0`. With the preamble bound, segment 0 is
        //  the preamble's first duplex and starts from the all-zero sponge; the
        //  FRI transcript's first segment then carries. A positional test would
        //  have pointed the FRI transcript back at the witnessed state and every
        //  challenge downstream would still have matched p3 — because it IS the
        //  right number, just not derived.
        //  ⚑ THIS ARM IS THE `DuplexChallenger`, AND ONLY IT. `CHAL_WIDTH` is
        //  that challenger's state width, not "the walk's" — a hash whose
        //  transcript is `carried` emits no `duplex` segment at all, and a
        //  future `implemented` hash with a different state width would read
        //  the wrong lanes here silently. So the agreement is asserted rather
        //  than assumed.
        if (w.hash.chalStateLanes !== CHAL_WIDTH)
          throw new Error(
            `a \`duplex\` segment under hash '${w.hash.name}', whose challenger state is ` +
              `${w.hash.chalStateLanes} lanes — this arm executes \`DuplexChallenger\` at ` +
              `${CHAL_WIDTH}. A hash with a different challenger needs its own emitter and executor.`,
          );
        const state =
          s.entry === 'chalState'
            ? friLanes.slice(ft.chalState, ft.chalState + CHAL_WIDTH)
            : s.entry === 'zero'
              ? new Array<bigint>(CHAL_WIDTH).fill(0n)
              : S.chal.map((i) => st.get(i)!);
        const lanes = state.slice();
        s.absorbs.forEach((ab, i) => {
          lanes[i] =
            ab.src === 'commit'
              ? friLanes[ft.commit[ab.layer] + ab.lane]
              : ab.src === 'finalPoly'
                ? friLanes[ft.finalPoly[ab.i] + ab.lane]
                : ab.src === 'pow'
                  ? friLanes[ft.powWitness]
                  : ab.src === 'arity'
                    ? BigInt(K.maxLogArity)
                    : ab.src === 'shape'
                      ? BigInt(ab.v)
                      : ab.src === 'roundCommit'
                        ? friLanes[ft.inputCommit[ab.round] + ab.lane]
                        : ab.src === 'publicValue'
                          ? airLanes[ab.at * EXT_LANES]
                          : ab.src === 'cumSum'
                            ? airLanes[ab.at * EXT_LANES + ab.lane]
                            : fzOf(ab.round, ab.mat, ab.point, ab.col)[ab.lane];
        });
        const out = s.perm ? permBigInt(lanes) : state;
        S.chal.forEach((id, i) => st.set(id, out[i]));
        const buf = out.slice(0, CHAL_RATE);
        for (const smp of s.samples) {
          const v = md(buf.pop()!);
          if (smp.dst === 'alpha') st.set(S.alpha[smp.lane], v);
          else if (smp.dst === 'beta') st.set(S.beta[smp.layer][smp.lane], v);
          //  ⚑ `sample_bits(k)` is the LOW k bits of the sample, not the sample.
          else if (smp.dst === 'qidx')
            st.set(S.qidx[smp.query], v & ((1n << BigInt(K.indexBits)) - 1n));
          else if (smp.dst === 'permChal') st.set(S.permChal[smp.i][smp.lane], v);
          else if (smp.dst === 'airAlpha') st.set(S.airAlpha[smp.lane], v);
          else if (smp.dst === 'zeta') st.set(S.zetaS[smp.lane], v);
        }
        break;
      }
      case 'chalCarry': {
        //  ⚑ READ, NOT DERIVED — the whole content of §3.14 residual 1, in nine
        //  lines. The circuit twin below imposes the index bound; the twin only
        //  has to place the same values in the same slots.
        const c = ft.carried!;
        setExt(st, S.alpha, friLanes.slice(c.friAlpha, c.friAlpha + EXT_LANES));
        c.betas.forEach((b, r) => setExt(st, S.beta[r], friLanes.slice(b, b + EXT_LANES)));
        c.qidx.forEach((lane, q) => st.set(S.qidx[q], friLanes[lane]));
        break;
      }
      case 'inBlock': {
        const [lo, hi] = ft.blockLanes(s.q, s.round, s.height, s.block);
        const row = friLanes.slice(lo, hi);
        const prev = s.first ? SS.initBigInt() : S.sponge.map((i) => st.get(i)!);
        const out = SS.absorbBigInt(prev, row);
        if (s.last) {
          const d = SS.finishBigInt(out);
          const hi2 = shape.heights.indexOf(s.height);
          setExt(st, s.seeds ? S.cur : S.inj[hi2], d);
        } else S.sponge.forEach((id, i) => st.set(id, out[i]));
        break;
      }
      case 'inLevel': {
        const round = shape.rounds[s.round];
        const top = Math.max(...round.matrices.map((m) => m.logHeight));
        const bits = idxBits(s.q);
        const dir = bits[lgmh - top + s.level];
        const sib = real.queries[s.q].inputBatches[s.round].path[s.level].map((x) => BigInt(x));
        a.push(...sib);
        const cur = extOf(st, S.cur);
        let nxt = dir ? suite.compressBigInt(sib, cur) : suite.compressBigInt(cur, sib);
        if (s.inject !== null)
          nxt = suite.compressBigInt(nxt, extOf(st, S.inj[shape.heights.indexOf(s.inject)]));
        setExt(st, S.cur, nxt);
        break;
      }
      case 'inRoot':
        checks.push({ kind: 'inputRoot', q: s.q, round: s.round, got: extOf(st, S.cur) });
        break;
      case 'deep': {
        if (s.mat < 0) {
          const hi = s.point;
          const v = extOf(st, S.dacc[hi]);
          setExt(st, hi === 0 ? S.folded : S.ro[hi], v);
          checks.push({ kind: 'ro', q: s.q, h: shape.heights[hi], i: hi, got: v });
          break;
        }
        const m = shape.rounds[s.round].matrices[s.mat];
        const hi = shape.heights.indexOf(m.logHeight);
        const base = ft.fx[s.q][s.round][s.mat];
        let h = extOf(st, S.dh);
        for (let c = s.to - 1; c >= s.from; c--) {
          const d = extSubBigInt(fzOf(s.round, s.mat, s.point, c), [friLanes[base + c], 0n, 0n, 0n]);
          h = c === s.to - 1 && s.open ? d : extAddBigInt(extMulBigInt(h, extOf(st, S.alpha)), d);
        }
        if (!s.close) {
          setExt(st, S.dh, h);
          break;
        }
        const x = deepQueryPointBigInt(st.get(S.qidx[s.q])!, m.logHeight, lgmh);
        const z = friLanes.slice(ft.z[s.round][s.mat][s.point], ft.z[s.round][s.mat][s.point] + EXT_LANES);
        const qinv = extInvBigInt(extSubBigInt(z, [x, 0n, 0n, 0n]));
        const pow = extOf(st, S.dpow[hi]);
        setExt(
          st,
          S.dacc[hi],
          extAddBigInt(extOf(st, S.dacc[hi]), extMulBigInt(extMulBigInt(pow, qinv), h)),
        );
        let ap = [1n, 0n, 0n, 0n];
        for (let i = 0; i < m.width; i++) ap = extMulBigInt(ap, extOf(st, S.alpha));
        setExt(st, S.dpow[hi], extMulBigInt(pow, ap));
        break;
      }
      case 'cpLeaf': {
        const bits = idxBits(s.q);
        const sib = real.queries[s.q].commitPhase[s.r].sibling.map((x) => BigInt(x));
        a.push(...sib);
        const folded = extOf(st, S.folded);
        const even = bits[s.r] ? sib : folded;
        const odd = bits[s.r] ? folded : sib;
        //  ⚑ THE COMMIT-PHASE LEAF IS `sponge([even, odd])`, EIGHT LANES, and
        //  it goes through the suite's own sponge rather than a hand-written
        //  permutation. Under the deployed hash that is one 16-wide block with
        //  eight zero lanes of padding; under Pasta it is one packed slot. A
        //  hard-coded `perm([even, odd, 0^8])` is the BabyBear spelling of the
        //  first and no spelling at all of the second.
        setExt(st, S.cur, suite.spongeBigInt([...even, ...odd]));
        let x: bigint;
        if (s.r === 0) {
          //  `g_{L+1} ^ reverse_bits_len(index >> 1, L)` at L = lgmh - 1.
          let idx = 0n;
          for (let i = 1; i < lgmh; i++) if (bits[i]) idx |= 1n << BigInt(i - 1);
          const L = lgmh - 1;
          let rev = 0n;
          for (let i = 0; i < L; i++) if ((idx >> BigInt(i)) & 1n) rev |= 1n << BigInt(L - 1 - i);
          let acc = 1n;
          let b = twoAdic(L + 1);
          let e = rev;
          while (e > 0n) {
            if (e & 1n) acc = md(acc * b);
            b = md(b * b);
            e >>= 1n;
          }
          x = acc;
        } else x = st.get(S.x)!;
        const nf = foldRowArity2BigInt(x, extOf(st, S.beta[s.r]), even, odd);
        setExt(st, S.folded, nf);
        const sq = md(x * x);
        st.set(S.x, s.r + 1 < lgmh && bits[s.r + 1] ? md(P - sq) : sq);
        break;
      }
      case 'cpLevel': {
        const bits = idxBits(s.q);
        const dir = bits[s.r + 1 + s.level];
        const sib = real.queries[s.q].commitPhase[s.r].path[s.level].map((x) => BigInt(x));
        a.push(...sib);
        const cur = extOf(st, S.cur);
        setExt(st, S.cur, dir ? suite.compressBigInt(sib, cur) : suite.compressBigInt(cur, sib));
        break;
      }
      case 'cpRoot':
        //  ⚑ THE COMMIT-PHASE ROOT BINDING — the circuit asserts it (`runSegments`
        //  `cpRoot`: `cur == laneFri(ft.commit[r])`) but the twin only ever pushed the
        //  `fold` cross-check here, so the reconstructed Merkle root was never compared
        //  against the committed one out of circuit. Without it a bent commit-phase
        //  sibling that still folds correctly, or a bent commit root, is invisible to a
        //  twin-only verdict. `got` is the reconstructed root, `want` the committed one.
        checks.push({
          kind: 'commitRoot',
          q: s.q,
          i: s.r,
          got: extOf(st, S.cur),
          want: real.commits[s.r].map((x) => BigInt(x)),
        });
        if (!rollAt(s.r)) checks.push({ kind: 'fold', q: s.q, i: s.r, got: extOf(st, S.folded) });
        break;
      case 'cpFold': {
        const beta = extOf(st, S.beta[s.r]);
        setExt(
          st,
          S.folded,
          extAddBigInt(
            extOf(st, S.folded),
            extMulBigInt(extMulBigInt(beta, beta), extOf(st, S.ro[s.rollIn])),
          ),
        );
        checks.push({ kind: 'fold', q: s.q, i: s.r, got: extOf(st, S.folded) });
        break;
      }
      case 'permBind':
        break;
      case 'deepInit':
        shape.heights.forEach((_, hi) => {
          setExt(st, S.dacc[hi], [0n, 0n, 0n, 0n]);
          setExt(st, S.dpow[hi], [1n, 0n, 0n, 0n]);
        });
        break;
      case 'final':
        checks.push({ kind: 'final', q: s.q, got: extOf(st, S.folded) });
        break;
      case 'preSeal': {
        //  The twin RECORDS both sides rather than asserting, so a divergence
        //  localises here instead of dying inside a circuit thirty slices on.
        s.zetaAt.forEach((lane, i) =>
          checks.push({
            kind: 'preSealZeta',
            q: i,
            got: extOf(st, S.zetaS),
            want: friLanes.slice(lane, lane + EXT_LANES),
          }),
        );
        s.chalAt.forEach((c, i) =>
          checks.push({
            kind: 'preSealChal',
            q: i,
            got: extOf(st, S.permChal[c.chal]),
            want: airLanes.slice(c.at * EXT_LANES, (c.at + 1) * EXT_LANES),
          }),
        );
        break;
      }
    }
    aux[k] = a;
  }
  carry[w.segs.length] = w.liveIn[w.segs.length].map((s) => st.get(s) ?? 0n);
  return { carry, aux, at: st, checks };
}

function twoAdic(k: number): bigint {
  let e = (P - 1n) / (1n << BigInt(k));
  let b = 31n;
  let r = 1n;
  while (e > 0n) {
    if (e & 1n) r = md(r * b);
    b = md(b * b);
    e >>= 1n;
  }
  return r;
}

/** How many aux lanes a segment consumes — a compile-time fact, so a slice's
 *  private-input shape is fixed before any witness exists. */
export function auxLanes(s: Segment, hash: WalkHash): number {
  if (s.t === 'inLevel') return hash.digestLanes;
  if (s.t === 'cpLevel') return hash.digestLanes;
  if (s.t === 'cpLeaf') return EXT_LANES;
  return 0;
}

// ===========================================================================
// 4. The in-circuit interpreter.
// ===========================================================================

type Sto = Map<number, Field>;

export type SliceIo = {
  airLanes: Field[];
  airOther: Field[];
  friLanes: Field[];
  friOther: Field[];
  aux: Field[];
};

/**
 * Run segments `[from, to)` in circuit, threading the slot state.
 *
 * Everything this reads is either carried (and therefore under the previous
 * boundary's digest), committed (and therefore under `dagDigest` or
 * `friDigest`), or self-authenticating (a Merkle sibling, pinned by the opening
 * it feeds). There is no fourth category, which is the property the braid rests
 * on.
 */
export function runSegments(
  w: SegmentedWalk,
  shape: FriShape,
  ft: FriLaneTable,
  op: OpenedPlan,
  plan: FriPlan,
  si: number,
  sto: Sto,
  io: SliceIo,
  /** ⚑ THE HASH THE SEGMENTS ARE RUN AT — the thing this executor hard-coded.
   *  Defaulted to the deployed suite so every existing caller is unchanged, and
   *  checked against the walk's own shape so an executor and a lane table can
   *  never be at two different hashes. */
  suite: MerkleSuite<any> = babyBearSuite,
) {
  assertWalkHashMatchesSuite(w.hash, suite as any);
  //  ⚑ EMIT WHATEVER GATE THIS SUITE'S RANGE CHECKS NEED TO EXIST AT ALL, ONCE
  //  PER BODY. Absent for BabyBear. Present for Pasta, and load-bearing: a slice
  //  that happens to hold only Merkle levels has no BabyBear arithmetic in it,
  //  so kimchi never installs the 12-bit table, and the slice compiles,
  //  analyses, passes `runAndCheck` and dies inside `prove()`. See
  //  `PastaMmcs.assertPastaLookupTable`.
  suite.anchorLookupTable?.();
  const D = w.hash.digestLanes;
  const SS = suite.spongeStream;
  const Dig = suite.Digest;
  const S = w.slots;
  const K = shape.knobs;
  const lgmh = K.logGlobalMaxHeight;
  const sl = plan.slices[si];
  const CL = plan.chunkSize;

  const laneAir = (g: number): Field => {
    const c = Math.floor(g / CL);
    const at = sl.readsAirChunks.indexOf(c);
    if (at < 0) throw new Error(`slice ${si} reads AIR lane ${g} in chunk ${c}, which it did not load`);
    return io.airLanes[at * CL + (g - c * CL)];
  };
  const laneFri = (g: number): Field => {
    const c = Math.floor(g / CL);
    const at = sl.readsFriChunks.indexOf(c);
    if (at < 0) throw new Error(`slice ${si} reads FRI lane ${g} in chunk ${c}, which it did not load`);
    return io.friLanes[at * CL + (g - c * CL)];
  };
  const extAir = (e: number) =>
    new BbExt({ limbs: Array.from({ length: EXT_LANES }, (_, i) => laneAir(e * EXT_LANES + i)) });
  const extFri = (g: number) =>
    new BbExt({ limbs: Array.from({ length: EXT_LANES }, (_, i) => laneFri(g + i)) });
  const fzOf = (round: number, mat: number, pt: number, c: number): BbExt => {
    const r = op.refs[round][mat][pt][c];
    return r.where === 'air' ? extAir(r.at) : extFri(r.at);
  };
  const get = (ids: number[]) => new BbExt({ limbs: ids.map((i) => sto.get(i)!) });
  const put = (ids: number[], v: BbExt) => ids.forEach((id, i) => sto.set(id, v.limbs[i]));
  const getD = (ids: number[]) => new Dig({ limbs: ids.map((i) => sto.get(i)!) });
  const putD = (ids: number[], d: { limbs: Field[] }) =>
    ids.forEach((id, i) => sto.set(id, d.limbs[i]));

  /** The 22 index bits of a carried, canonical query-index lane. The split is
   *  FORCED (`assertLowBitsSplit`), so re-splitting a carried index in a later
   *  slice is the same constraint the challenger imposed when it drew it. */
  const bitsMemo = new Map<number, Bool[]>();
  const idxBits = (q: number): Bool[] => {
    const hit = bitsMemo.get(q);
    if (hit) return hit;
    const c = sto.get(S.qidx[q])!;
    const bits = Provable.witness(Provable.Array(Bool, K.indexBits), () => {
      const v = c.toBigInt();
      return Array.from({ length: K.indexBits }, (_, i) => Bool(((v >> BigInt(i)) & 1n) === 1n));
    });
    const hi = Provable.witness(Field, () => Field(c.toBigInt() >> BigInt(K.indexBits)));
    assertLowBitsSplit(c, bits, hi, K.indexBits);
    bitsMemo.set(q, bits);
    return bits;
  };

  let auxAt = 0;
  const takeAux = (n: number): Field[] => {
    const out = io.aux.slice(auxAt, auxAt + n);
    auxAt += n;
    return out;
  };

  for (let k = sl.from; k < sl.to; k++) {
    const s = w.segs[k];
    switch (s.t) {
      case 'duplex': {
        //  ⚑ `entry` REPLACED `k === 0` — see the twin's note. `zero` is a
        //  CONSTANT `Field(0)` per lane, which is the whole point: the derived
        //  chain starts from a literal nobody can choose.
        //  ⚑ THE SAME AGREEMENT THE TWIN ASSERTS, for the same reason.
        if (w.hash.chalStateLanes !== CHAL_WIDTH)
          throw new Error(
            `a \`duplex\` segment under hash '${w.hash.name}', whose challenger state is ` +
              `${w.hash.chalStateLanes} lanes — this arm executes \`DuplexChallenger\` at ${CHAL_WIDTH}.`,
          );
        const state =
          s.entry === 'chalState'
            ? Array.from({ length: CHAL_WIDTH }, (_, i) => laneFri(ft.chalState + i))
            : s.entry === 'zero'
              ? Array.from({ length: CHAL_WIDTH }, () => Field(0))
              : S.chal.map((i) => sto.get(i)!);
        const lanes = state.slice();
        s.absorbs.forEach((ab, i) => {
          lanes[i] =
            ab.src === 'commit'
              ? laneFri(ft.commit[ab.layer] + ab.lane)
              : ab.src === 'finalPoly'
                ? laneFri(ft.finalPoly[ab.i] + ab.lane)
                : ab.src === 'pow'
                  ? laneFri(ft.powWitness)
                  : ab.src === 'arity'
                    ? Field(K.maxLogArity) //  a protocol constant, not proof data
                    : //  ⚑ A LITERAL. The instance count, the degree bits, the
                      //  widths and the chunk counts are the batch's SHAPE; a
                      //  prover cannot reach them, so they are not witnessed.
                      ab.src === 'shape'
                      ? Field(ab.v)
                      : //  The same `inputCommit` lanes `inRoot` closes against.
                        ab.src === 'roundCommit'
                        ? laneFri(ft.inputCommit[ab.round] + ab.lane)
                        : //  A public value is a BASE element: lane `4·at` alone.
                          ab.src === 'publicValue'
                          ? laneAir(ab.at * EXT_LANES)
                          : ab.src === 'cumSum'
                            ? laneAir(ab.at * EXT_LANES + ab.lane)
                            : fzOf(ab.round, ab.mat, ab.point, ab.col).limbs[ab.lane];
        });
        const bound = permOutputBound(LANE_MAX);
        //  ⚑ `perm === false` is the ENTERING state: no permutation, the output
        //  buffer is already full. See `segmentWalk`'s header.
        const out = s.perm
          ? provablePermBounded(lanes, LANE_MAX).map((x) => reduceLane(x, bound))
          : lanes.map((x) => canonicalLane(x, LANE_MAX));
        S.chal.forEach((id, i) => sto.set(id, out[i]));
        const buf = out.slice(0, CHAL_RATE);
        for (const smp of s.samples) {
          const v = canonicalLane(buf.pop()!, LANE_MAX);
          if (smp.dst === 'alpha') sto.set(S.alpha[smp.lane], v);
          else if (smp.dst === 'beta') sto.set(S.beta[smp.layer][smp.lane], v);
          else if (smp.dst === 'qidx') {
            //  ⚑ `sample_bits(k)` returns the LOW k BITS of a canonical sample,
            //  and the split is the whole of what makes an index unchooseable:
            //  without the bound on the high part, `hi = (c − lo)·2^-k` always
            //  exists over Pasta and a prover derives whatever index it likes
            //  out of a perfectly correct sponge. What is CARRIED onward is the
            //  recomposition of the forced low bits, so a later slice that
            //  re-splits it is imposing the same constraint again.
            const bits = Provable.witness(Provable.Array(Bool, K.indexBits), () => {
              const x = v.toBigInt();
              return Array.from({ length: K.indexBits }, (_, i) => Bool(((x >> BigInt(i)) & 1n) === 1n));
            });
            const hiB = Provable.witness(Field, () => Field(v.toBigInt() >> BigInt(K.indexBits)));
            assertLowBitsSplit(v, bits, hiB, K.indexBits);
            let acc = Field(0);
            for (let i = 0; i < K.indexBits; i++) acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
            sto.set(S.qidx[smp.query], acc);
            bitsMemo.set(smp.query, bits);
          } else if (smp.dst === 'permChal') sto.set(S.permChal[smp.i][smp.lane], v);
          else if (smp.dst === 'airAlpha') sto.set(S.airAlpha[smp.lane], v);
          else if (smp.dst === 'zeta') sto.set(S.zetaS[smp.lane], v);
          else {
            //  ⚑ `check_witness(16, w)`: the witness was ABSORBED above and the
            //  next sample's low 16 bits must be zero. Getting this wrong does
            //  not fail loudly — it shifts every one of the 19 query indices.
            //  ⚑ AND THIS ARM WAS A BARE `else` UNTIL THE PREAMBLE LANDED. Three
            //  new sample kinds would have fallen into it and been range-checked
            //  as PoW samples — α_stark and ζ refused for having non-zero low
            //  bits, which reads as a transcript bug and is a dispatch bug.
            if (smp.dst !== 'pow') throw new Error(`unhandled sample destination ${(smp as any).dst}`);
            const hi = Provable.witness(Field, () => Field(v.toBigInt() >> BigInt(K.queryPowBits)));
            assertLowBitsZero(v, hi, K.queryPowBits);
          }
        }
        break;
      }
      case 'chalCarry': {
        //  ⚑ THE CARRIED TRANSCRIPT. α and the βs are committed BabyBear lanes
        //  and `chunkedCommitment` has already canonicalised them, so the only
        //  work here is the QUERY INDEX bound: the derived path carries a
        //  recomposition of `indexBits` forced bits, and a carried lane has to
        //  be forced into the same shape or a prover reads a 2^31-sized index
        //  out of a perfectly honest commitment. Witness the bits, recompose,
        //  assert equality — and memo them, because every later `idxBits` in
        //  this slice is then the same forced split.
        const c = ft.carried!;
        for (let i = 0; i < EXT_LANES; i++) sto.set(S.alpha[i], laneFri(c.friAlpha + i));
        c.betas.forEach((b, r) => {
          for (let i = 0; i < EXT_LANES; i++) sto.set(S.beta[r][i], laneFri(b + i));
        });
        c.qidx.forEach((lane, q) => {
          const v = laneFri(lane);
          const bits = Provable.witness(Provable.Array(Bool, K.indexBits), () => {
            const x = v.toBigInt();
            return Array.from({ length: K.indexBits }, (_, i) => Bool(((x >> BigInt(i)) & 1n) === 1n));
          });
          let acc = Field(0);
          for (let i = 0; i < K.indexBits; i++) acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
          acc.assertEquals(v);
          sto.set(S.qidx[q], acc);
          bitsMemo.set(q, bits);
        });
        break;
      }
      case 'inBlock': {
        const [lo, hiL] = ft.blockLanes(s.q, s.round, s.height, s.block);
        const row = Array.from({ length: hiL - lo }, (_, i) => laneFri(lo + i));
        //  ⚑ THE LANES ARE ALREADY CANONICAL. Every one is read out of a
        //  committed chunk and `chunkedCommitment` has put `canonicalLane` on
        //  it, which is why `lanesAlreadyChecked` is TRUE here and is a claim
        //  about the call site rather than an optimisation.
        const prev = s.first ? SS.init() : S.sponge.map((i) => sto.get(i)!);
        const out = SS.absorb(prev, row, true);
        if (s.last)
          putD(s.seeds ? S.cur : S.inj[shape.heights.indexOf(s.height)], SS.finish(out));
        else S.sponge.forEach((id, i) => sto.set(id, out[i]));
        break;
      }
      case 'inLevel': {
        const round = shape.rounds[s.round];
        const top = Math.max(...round.matrices.map((m) => m.logHeight));
        const dir = idxBits(s.q)[lgmh - top + s.level];
        const sib = new Dig({ limbs: takeAux(D) });
        suite.assertInRange(sib);
        const [l, r] = suite.condSwap(getD(S.cur), sib, dir);
        let cur = suite.compress(l, r);
        //  ⚑ `MerkleTreeMmcs::verify_batch` over MIXED HEIGHTS: after the
        //  compress, a matrix whose height equals the level's padded height has
        //  its own row digest compressed in. Four of them per input round here,
        //  and a flat depth-22 path would be a different tree.
        if (s.inject !== null)
          cur = suite.compress(cur, getD(S.inj[shape.heights.indexOf(s.inject)]));
        putD(S.cur, cur);
        break;
      }
      case 'inRoot': {
        const cur = suite.canonical(getD(S.cur));
        for (let j = 0; j < D; j++)
          cur.limbs[j].assertEquals(laneFri(ft.inputCommit[s.round] + j));
        break;
      }
      case 'deep': {
        if (s.mat < 0) {
          const hi = s.point; //  the height index, carried on the closing segment
          put(hi === 0 ? S.folded : S.ro[hi], get(S.dacc[hi]));
          break;
        }
        const m = shape.rounds[s.round].matrices[s.mat];
        const hi = shape.heights.indexOf(m.logHeight);
        const alpha = get(S.alpha);
        const base = ft.fx[s.q][s.round][s.mat];
        let h = get(S.dh);
        for (let c = s.to - 1; c >= s.from; c--) {
          const fx = laneFri(base + c);
          assertLaneLt2p31(fx);
          const d = extSubBase(fzOf(s.round, s.mat, s.point, c), fx);
          h = c === s.to - 1 && s.open ? d : extAdd(extMul(h, alpha), d);
        }
        if (!s.close) {
          put(S.dh, h);
          break;
        }
        const x = deepQueryPoint(idxBits(s.q), m.logHeight, lgmh);
        const z = extFri(ft.z[s.round][s.mat][s.point]);
        assertExtInRange(z);
        const qinv = extInverse(extSub(z, extOfBase(x)));
        const pow = get(S.dpow[hi]);
        put(S.dacc[hi], extAdd(get(S.dacc[hi]), extMul(extMul(pow, qinv), h)));
        let ap: BbExt | null = null;
        let b = alpha;
        let n = m.width;
        while (n > 0) {
          if (n & 1) ap = ap === null ? b : extMul(ap, b);
          n >>= 1;
          if (n > 0) b = extMul(b, b);
        }
        put(S.dpow[hi], extMul(pow, ap!));
        break;
      }
      case 'cpLeaf': {
        const bits = idxBits(s.q);
        const sib = new BbExt({ limbs: takeAux(EXT_LANES) });
        assertExtInRange(sib);
        const folded = get(S.folded);
        const even: Field[] = [];
        const odd: Field[] = [];
        for (let i = 0; i < EXT_D; i++) {
          even.push(Provable.if(bits[s.r], sib.limbs[i], folded.limbs[i]));
          odd.push(Provable.if(bits[s.r], folded.limbs[i], sib.limbs[i]));
        }
        //  ⚑ `sponge([even, odd])` THROUGH THE SUITE'S STREAM, not a
        //  hand-written `perm([even, odd, 0^8])` and NOT the one-shot `sponge`.
        //  The eight zero lanes were the deployed sponge's padding of a
        //  one-block absorb; the suite's own leaf hash is the thing that is true
        //  at both hashes. `assertExtInRange` has already bounded the four
        //  sibling lanes and the four folded ones, so the lanes are checked.
        //
        //  ⚠ AND IT IS `spongeStream`, NOT `sponge`, FOR A MEASURED REASON. The
        //  one-shot BabyBear form reduces only the eight lanes it returns; the
        //  streaming form reduces all sixteen, because its state crosses a cut.
        //  This segment's inline predecessor reduced sixteen. Reaching for
        //  `sponge` here would have dropped 8 `reduceLane`s on each of the 304
        //  commit-phase leaves — a real EMITTED-row change that no tier-0 figure
        //  could see, because the model prices a leaf at `P.perm` either way.
        putD(S.cur, SS.finish(SS.absorb(SS.init(), [...even, ...odd], true)));
        const x = s.r === 0 ? cosetPointFromBits(bits.slice(1), lgmh - 1) : sto.get(S.x)!;
        put(
          S.folded,
          foldRowArity2(x, get(S.beta[s.r]), new BbExt({ limbs: even }), new BbExt({ limbs: odd })),
        );
        //  ⚑ the descent bit is the NEXT index bit, not the slot bit.
        sto.set(S.x, nextCosetPoint(x, s.r + 1 < lgmh ? bits[s.r + 1] : Bool(false)));
        break;
      }
      case 'cpLevel': {
        const dir = idxBits(s.q)[s.r + 1 + s.level];
        const sib = new Dig({ limbs: takeAux(D) });
        suite.assertInRange(sib);
        const [l, r] = suite.condSwap(getD(S.cur), sib, dir);
        putD(S.cur, suite.compress(l, r));
        break;
      }
      case 'cpRoot': {
        const cur = suite.canonical(getD(S.cur));
        for (let j = 0; j < D; j++)
          cur.limbs[j].assertEquals(laneFri(ft.commit[s.r] + j));
        break;
      }
      case 'cpFold': {
        const beta = get(S.beta[s.r]);
        put(S.folded, extAdd(get(S.folded), extMul(extMul(beta, beta), get(S.ro[s.rollIn]))));
        break;
      }
      case 'permBind': {
        //  ⚑ `perm[p][k] = Σ_j f_{4k+j}(ζ)·X^j`. Multiplying by `X^j` is a limb
        //  rotation with the binomial `W = 11` applied to the wrapped limbs, not
        //  a general extension multiply — so the bridge costs three additions a
        //  column and not three multiplies.
        const pi = shape.rounds.findIndex((r) => r.name === 'permutation');
        const m = shape.rounds[pi].matrices[s.mat];
        const cols = op.refs[pi][s.mat][s.point];
        const t = dagTableName(m.name);
        const airIx = airColumnIndex();
        for (let k = s.from; k < s.to; k++) {
          const e = airIx.byLabel.get(`${t}|perm[${s.point}][${k}]`)!;
          let acc = BbExt.zero();
          for (let j = 0; j < EXT_LANES; j++) {
            const f = extFri(cols[k * EXT_LANES + j].at);
            assertExtInRange(f);
            acc = extAdd(acc, extShift(f, j));
          }
          const want = extAir(e);
          for (let l = 0; l < EXT_D; l++)
            canonicalLane(acc.limbs[l], LANE_MAX).assertEquals(canonicalLane(want.limbs[l], LANE_MAX));
        }
        break;
      }
      case 'deepInit': {
        shape.heights.forEach((_, hi) => {
          put(S.dacc[hi], BbExt.zero());
          put(S.dpow[hi], BbExt.from([1n, 0n, 0n, 0n]));
        });
        break;
      }
      case 'final': {
        const bits = idxBits(s.q);
        const xF = finalEvalPointFromBits(bits.slice(K.layers), lgmh);
        const coeffs = ft.finalPoly.map((o) => extFri(o));
        for (const c of coeffs) assertExtInRange(c);
        const want = evalFinalPoly(coeffs, xF);
        const got = get(S.folded);
        for (let j = 0; j < EXT_D; j++)
          canonicalLane(got.limbs[j], LANE_MAX).assertEquals(canonicalLane(want.limbs[j], LANE_MAX));
        break;
      }
      case 'preSeal': {
        //  ⚑ THE PREAMBLE'S TEETH. Everything above this line computes; this
        //  line refuses. `ζ` derived from the batch's own commitments, public
        //  values, cumulative sums and 2,630 opened values must BE the point the
        //  proof says every matrix was opened at, and the LogUp challenges the
        //  preamble drew must BE the ones the AIR chain folded with.
        if (!s.armed) break;
        const z = get(S.zetaS);
        for (const lane of s.zetaAt) {
          const committed = extFri(lane);
          for (let j = 0; j < EXT_D; j++)
            canonicalLane(z.limbs[j], LANE_MAX).assertEquals(canonicalLane(committed.limbs[j], LANE_MAX));
        }
        for (const c of s.chalAt) {
          const drew = get(S.permChal[c.chal]);
          const used = extAir(c.at);
          for (let j = 0; j < EXT_D; j++)
            canonicalLane(drew.limbs[j], LANE_MAX).assertEquals(canonicalLane(used.limbs[j], LANE_MAX));
        }
        break;
      }
    }
  }
  if (auxAt !== io.aux.length)
    throw new Error(`slice ${si} was given ${io.aux.length} aux lanes and consumed ${auxAt}`);
}

// ===========================================================================
// 5. The slice program.
// ===========================================================================

let sideloadedClasses = 0;

/** ⚑ ONE side-loaded class per process, for §3.27's reason: `DynamicProof.tag()`
 *  names itself off a process-global counter, so a second class in one process
 *  gets an identifier that depends on creation ORDER — and an identifier that
 *  depends on order is one that differs between two processes meant to compile
 *  the same circuit, which is the one thing a pinned key cannot tolerate. */
export function makePrevProofClass(flags: FeatureFlags) {
  if (sideloadedClasses > 0)
    throw new Error(
      'a SECOND side-loaded proof class in one process: build one slice program per process',
    );
  sideloadedClasses++;
  class PrevProof extends DynamicProof<Field, Field> {
    static publicInputType = Field;
    static publicOutputType = Field;
    static maxProofsVerified = 1 as const;
    static featureFlags = flags;
  }
  return PrevProof;
}

export type FriBraidCtx = {
  w: SegmentedWalk;
  shape: FriShape;
  ft: FriLaneTable;
  op: OpenedPlan;
  plan: FriPlan;
  /** ⚑ THE HASH THE CHAIN IS BUILT AT, AS THE SUITE ITSELF — defaulted to the
   *  deployed one so every existing caller is unchanged, and checked against
   *  `w.hash` inside `runSegments` so a context cannot hold a walk shaped like
   *  one hash and an executor running another. */
  suite?: MerkleSuite<any>;
};

export type FriSliceOpts = {
  /** ⚑ FALSE builds the UNBOUND CONTROL — the boundary assertions removed. */
  bindCarry?: boolean;
  /** ⚑ FALSE builds the UNPINNED CONTROL — still verifies its predecessor,
   *  against whatever key it is handed. */
  pinVk?: boolean;
  prevVkHash?: bigint;
  prevFlags: FeatureFlags;
};

export function friSliceProgramName(si: number, n: number, o: { bindCarry?: boolean; pinVk?: boolean } = {}) {
  const bind = o.bindCarry !== false;
  const pin = o.pinVk !== false;
  return `dregg-root-fri-slice${si}-of${n}${bind ? '' : '-UNBOUND'}${pin ? '' : '-UNPINNED'}`;
}

/** The private-input widths of slice `si` — compile-time, and the driver builds
 *  its witness to exactly this shape. */
export function friSliceShape(ctx: FriBraidCtx, si: number) {
  const { w, plan } = ctx;
  const sl = plan.slices[si];
  const CL = plan.chunkSize;
  let aux = 0;
  for (let k = sl.from; k < sl.to; k++) aux += auxLanes(w.segs[k], w.hash);
  return {
    nLiveIn: w.liveIn[sl.from].length,
    nLiveOut: w.liveIn[sl.to].length,
    nAirRead: sl.readsAirChunks.length * CL,
    nAirOther: plan.nAirChunks - sl.readsAirChunks.length,
    nFriRead: sl.readsFriChunks.length * CL,
    nFriOther: plan.nFriChunks - sl.readsFriChunks.length,
    nAux: aux,
    isLast: si + 1 === plan.slices.length,
  };
}

/**
 * ONE FRI slice as its own `ZkProgram` with ONE method, taking its predecessor
 * as a side-loaded `DynamicProof` and pinning that predecessor's verification
 * key hash to a compile-time constant.
 *
 * ⚑ SLICE 0's PREDECESSOR IS THE AIR CHAIN. It does not enter a
 * `stepBoundary`; it enters `airTerminalSeal(dagDigest, digest(acc), 7)` — the
 * value AIR slice 6 emitted — recomputed here from the `dagDigest` THIS circuit
 * re-derives out of the AIR column chunks it loaded, and from the accumulator it
 * carries. That single assertion is the braid: a FRI walk over a different
 * column assignment computes a different `dagDigest`, and the seal does not
 * match.
 */
export function makeFriSliceProgram(ctx: FriBraidCtx, si: number, opts: FriSliceOpts) {
  const { w, shape, ft, op, plan } = ctx;
  const suite = ctx.suite ?? babyBearSuite;
  const bind = opts.bindCarry !== false;
  const pin = opts.pinVk !== false;
  const sl = plan.slices[si];
  const sh = friSliceShape(ctx, si);
  const CL = plan.chunkSize;
  const N = plan.slices.length;
  if (pin && opts.prevVkHash === undefined)
    throw new Error(
      `FRI slice ${si} pins its predecessor's verification key and was given none — an unpinned ` +
        "side-loaded chain accepts any program's proof and is not a chain",
    );

  const Prev = makePrevProofClass(opts.prevFlags);
  const pinned = opts.prevVkHash ?? 0n;
  const arr = (n: number) => Provable.Array(Field, Math.max(n, 1));

  const prog = ZkProgram({
    name: friSliceProgramName(si, N, opts),
    publicInput: Field,
    publicOutput: Field,
    methods: {
      slice: {
        privateInputs: [
          Prev,
          VerificationKey,
          BbExt, //                         the AIR chain's terminal accumulator, carried
          arr(sh.nLiveIn),
          arr(sh.nAirRead),
          arr(sh.nAirOther),
          arr(sh.nFriRead),
          arr(sh.nFriOther),
          arr(sh.nAux),
        ],
        async method(
          bIn: Field,
          prev: InstanceType<typeof Prev>,
          vk: VerificationKey,
          acc: BbExt,
          liveIn: Field[],
          airLanes: Field[],
          airOther: Field[],
          friLanes: Field[],
          friOther: Field[],
          aux: Field[],
        ) {
          if (pin) vk.hash.assertEquals(Field(pinned));
          prev.verify(vk);

          const dagDigest = chunkedCommitment(
            plan.nAirChunks,
            CL,
            sl.readsAirChunks,
            airLanes.slice(0, sh.nAirRead),
            airOther.slice(0, sh.nAirOther),
            babyBearKinds(sh.nAirRead),
          );
          const friDigest = chunkedCommitment(
            plan.nFriChunks,
            CL,
            sl.readsFriChunks,
            friLanes.slice(0, sh.nFriRead),
            friOther.slice(0, sh.nFriOther),
            readLaneKinds(ft.kinds, sl.readsFriChunks, CL),
          );
          const friCommit = Poseidon.hash([dagDigest, friDigest]);

          const live = liveIn.slice(0, sh.nLiveIn);
          //  ⚑ CANONICALISE A CARRIED SLOT ONLY WHERE THAT MEANS ANYTHING. The
          //  digest and sponge registers hold native field elements under a
          //  native-digest hash, and a `canonicalLane` on one refuses every
          //  honest proof. `SlotLayout.kinds` is the same per-entry vector the
          //  lane table carries, for the same reason.
          const liveSlots = w.liveIn[sl.from];
          live.forEach((l, i) => {
            if (w.slots.kinds[liveSlots[i]] === 0) canonicalLane(l, LANE_MAX);
          });
          for (const l of acc.limbs) canonicalLane(l, LANE_MAX);

          if (bind) {
            //  ⚑ THE BRAID. Slice 0 enters the AIR chain's terminal seal; every
            //  later slice enters this chain's own step boundary.
            const want =
              si === 0
                ? airTerminalSeal(dagDigest, digestOfLanes([...acc.limbs]), AIR_SLICES)
                : stepBoundary(friCommit, digestOfLanes([...live, ...acc.limbs]), AIR_SLICES + si);
            want.assertEquals(bIn);
            prev.publicOutput.assertEquals(bIn);
          }

          const sto: Sto = new Map();
          w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, live[i]));
          runSegments(w, shape, ft, op, plan, si, sto, {
            airLanes: airLanes.slice(0, sh.nAirRead),
            airOther: airOther.slice(0, sh.nAirOther),
            friLanes: friLanes.slice(0, sh.nFriRead),
            friOther: friOther.slice(0, sh.nFriOther),
            aux: aux.slice(0, sh.nAux),
          } as SliceIo,
          suite);
          const out = w.liveIn[sl.to].map((slot) => {
            const v = sto.get(slot);
            if (v === undefined)
              throw new Error(`slice ${si} must hand on slot ${w.slots.names[slot]} and does not hold it`);
            return v;
          });

          const publicOutput = sh.isLast
            ? airTerminalSeal(friCommit, digestOfLanes([...acc.limbs, ...out]), AIR_SLICES + N)
            : stepBoundary(friCommit, digestOfLanes([...out, ...acc.limbs]), AIR_SLICES + si + 1);
          return { publicOutput };
        },
      },
    },
  });
  return { prog, Prev, si, bind, pin, isLast: sh.isLast, shape: sh };
}

/** The boundary a slice ENTERS, out of circuit — the twin of the assertion
 *  above, so a process that compiled nothing can check every public field. */
export function friBoundaryIn(
  ctx: FriBraidCtx,
  twin: WalkTwin,
  si: number,
  dagDigest: Field,
  friCommit: Field,
  acc: bigint[],
): Field {
  const sl = ctx.plan.slices[si];
  if (si === 0) return airTerminalSeal(dagDigest, digestOfLanes(acc.map((x) => Field(x))), AIR_SLICES);
  return stepBoundary(
    friCommit,
    digestOfLanes([...twin.carry[sl.from].map((x) => Field(x)), ...acc.map((x) => Field(x))]),
    AIR_SLICES + si,
  );
}

export function friBoundaryOut(
  ctx: FriBraidCtx,
  twin: WalkTwin,
  si: number,
  friCommit: Field,
  acc: bigint[],
): Field {
  const sl = ctx.plan.slices[si];
  const N = ctx.plan.slices.length;
  const out = twin.carry[sl.to].map((x) => Field(x));
  if (si + 1 === N)
    return airTerminalSeal(friCommit, digestOfLanes([...acc.map((x) => Field(x)), ...out]), AIR_SLICES + N);
  return stepBoundary(
    friCommit,
    digestOfLanes([...out, ...acc.map((x) => Field(x))]),
    AIR_SLICES + si + 1,
  );
}
