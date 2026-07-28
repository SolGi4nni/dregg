import { Bool, Field, Gadgets, Provable, Struct, ZkProgram } from 'o1js';
import {
  P,
  assertLaneLt2p31,
  canonicalLane,
  permBigInt,
  permOutputBound,
  provablePermBounded,
  reduceLane,
} from './Poseidon2BabyBearW16.js';
import {
  BbDigest,
  DIGEST_ELEMS,
  RATE,
  WIDTH,
  spongeBB,
  spongeBigInt,
} from './Poseidon2Merkle.js';
import { BbExt, EXT_D, verifyCommitPhase } from './FriQueryStep.js';

// ---------------------------------------------------------------------------
// RUNG 3 — THE CHALLENGER. `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>,
// 16, 8>` — the Fiat-Shamir transcript — as an o1js/Kimchi circuit.
//
// ⚑ WHY THIS IS THE RUNG THAT MATTERS, AND NOT THE ROW COUNTS.
//
// Rung 2 walks one FRI query: it opens the rows, folds them, and lands on an
// evaluation. Every input to that walk — the query INDEX, the fold challenge
// `beta`, the batch challenge `alpha` — is a WITNESS. A statement whose query
// indices are witnessed says "there EXIST 19 indices at which this proof is
// consistent", and a cheating prover picks the 19 it can answer. That is not a
// weaker FRI; it is not FRI. The soundness of the whole protocol is the claim
// that the indices are drawn AFTER the commitments, by a function the prover
// cannot steer. This module is that function.
//
// So: rung 2 shows we can walk *a* FRI proof. This rung is what makes it *the
// prover's* FRI proof.
//
// ⚑ WHAT A TRANSCRIPTION GETS WRONG. The hash was never the risk — `p2bb` pins
// it. The risk is the state machine, and `DuplexChallenger` has four edges that
// each look like a detail and each silently change every challenge downstream:
//
//   1. `output_buffer.pop()` takes from the BACK. The first sample after a
//      permutation is `sponge_state[RATE-1]`, not `[0]`
//      (`duplex_challenger.rs:243-245`).
//   2. `observe` CLEARS the output buffer, discarding unread squeezes
//      (`:150`).
//   3. `sample` re-duplexes when the input buffer is NON-EMPTY, and the absorb
//      is an OVERWRITE of only the buffered prefix — the unabsorbed rate lanes
//      keep the PREVIOUS permutation's output rather than being zero-filled
//      (`:86-99, 239-241`).
//   4. `check_witness(0, w)` returns BEFORE observing (`grinding_challenger.rs:
//      41-43`). The deployed commit-phase PoW is 0 bits, so all 16 per-layer
//      calls must leave the transcript byte-identical. A circuit that "checked"
//      them by absorbing the witness would get all 16 betas wrong.
//
// Each of those is pinned by a Rust test against the DEPLOYED challenger
// (`mina-pasta-hash-probe/src/p2chal.rs`), each with a discriminating polarity,
// and the whole schedule is KAT'd end to end by `p2fritranscript`.
//
// ⚑ WHAT THIS RUNG IS NOT. It derives the FRI challenges GIVEN a transcript
// state. The state is reached by observing a `preamble` — a stand-in for the
// batch-STARK's own observes (degree bits, trace commitments, public values,
// zeta) that precede `verify_fri`. Binding that preamble to the real STARK
// preamble is a further rung and is not done here. It is, however, a strictly
// smaller hole than a witnessed index: the preamble is ABSORBED, so a prover
// that changes it changes every beta and every index.
// ---------------------------------------------------------------------------

/** The deployed root's FRI knobs — `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §1.2,
 *  each re-derived from `ir2_leaf_wrap_config()` and mirrored in the Rust
 *  emitter's constants, which the KAT compares field by field. */
export type FriKnobs = {
  logBlowup: number;
  logFinalPolyLen: number;
  commitPowBits: number;
  queryPowBits: number;
  maxLogArity: number;
  numQueries: number;
  logGlobalMaxHeight: number;
  extraQueryIndexBits: number;
  layers: number;
  indexBits: number;
  finalPolyLen: number;
};

export const DEPLOYED_KNOBS: FriKnobs = {
  logBlowup: 6,
  logFinalPolyLen: 0,
  /** ZERO — so `check_witness` returns before observing, 16 times. */
  commitPowBits: 0,
  queryPowBits: 16,
  /** ONE. The root folds by TWO. */
  maxLogArity: 1,
  numQueries: 19,
  logGlobalMaxHeight: 22,
  extraQueryIndexBits: 0,
  /** `(22 - 6 - 0) / 1`. */
  layers: 16,
  /** `log_global_max_height + extra_query_index_bits`. */
  indexBits: 22,
  /** `2^log_final_poly_len` — ONE coefficient, so the final check is a
   *  CONSTANT comparison and the Horner evaluation degenerates. */
  finalPolyLen: 1,
};

const LANE_MAX = (1n << 31n) - 1n;

// ===========================================================================
// 1. The out-of-circuit twin. Calls `permBigInt` — the same reference the
//    Lean-pinned KAT validates — so a divergence between it and the circuit is
//    a real disagreement and not a re-implementation gap.
// ===========================================================================

export class ChallengerBigInt {
  state: bigint[] = Array(WIDTH).fill(0n);
  inputBuffer: bigint[] = [];
  outputBuffer: bigint[] = [];
  /** Instrumentation: permutations performed. The transcript's whole cost. */
  perms = 0;

  duplexing() {
    // OVERWRITE the first `input_buffer.len()` lanes. The rest keep the
    // previous permutation's output — see edge (3) in the header.
    for (let i = 0; i < this.inputBuffer.length; i++) this.state[i] = this.inputBuffer[i];
    this.inputBuffer = [];
    this.state = permBigInt(this.state);
    this.perms++;
    this.outputBuffer = this.state.slice(0, RATE);
  }
  observe(v: bigint) {
    this.outputBuffer = [];
    this.inputBuffer.push(((v % P) + P) % P);
    if (this.inputBuffer.length === RATE) this.duplexing();
  }
  observeSlice(vs: bigint[]) {
    for (const v of vs) this.observe(v);
  }
  sample(): bigint {
    if (this.inputBuffer.length > 0 || this.outputBuffer.length === 0) this.duplexing();
    return this.outputBuffer.pop()!;
  }
  sampleExt(): bigint[] {
    return Array.from({ length: EXT_D }, () => this.sample());
  }
  sampleBits(bits: number): number {
    return Number(this.sample() & ((1n << BigInt(bits)) - 1n));
  }
  clone(): ChallengerBigInt {
    const c = new ChallengerBigInt();
    c.state = this.state.slice();
    c.inputBuffer = this.inputBuffer.slice();
    c.outputBuffer = this.outputBuffer.slice();
    c.perms = this.perms;
    return c;
  }
  /** `GrindingChallenger::grind` — the honest prover's side of the PoW. The
   *  search is serial rather than SIMD, which is the only difference from
   *  `grinding_challenger.rs:105-200`. */
  grind(bits: number): bigint {
    if (bits === 0) return 0n;
    for (let w = 0n; w < P; w++) if (this.clone().checkWitness(bits, w)) return w;
    throw new Error('no PoW witness exists — impossible for bits < log2(p)');
  }
  /** `GrindingChallenger::check_witness`. ⚑ At `bits == 0` this returns
   *  WITHOUT observing — the deployed commit-phase PoW, 16 times. */
  checkWitness(bits: number, witness: bigint): boolean {
    if (bits === 0) return true;
    this.observe(witness);
    return this.sampleBits(bits) === 0;
  }
}

// ===========================================================================
// 2. Range plumbing the challenger needs and the Merkle path did not.
// ===========================================================================

/**
 * Assert `0 <= v < 2^n` for `n` in `1..=36`.
 *
 * The Merkle rung only ever needed `< 2^31`; the challenger needs arbitrary
 * widths because `sample_bits(k)` splits a canonical lane into a `k`-bit low
 * part and a `(31-k)`-bit high part, and BOTH have to be bounded or the split
 * is not unique.
 *
 * ⚑ THE BOUND IS CARRIED TWICE, AND THE SECOND CARRIER IS WHY. The 12-bit
 * lookups are the real constraint at proving time — but `Provable.runAndCheck`
 * DOES NOT EVALUATE LOOKUP CONSTRAINTS. Measured: `rangeCheck3x12(Field(4096))`
 * runs clean under `runAndCheck`, and `assertLaneLt2p31(2^31)` is caught only
 * because ITS witness truncates to 31 bits and the recomposition then fails.
 * So a gadget whose bound rests on the lookup alone is sound in a proof and
 * UNTESTABLE outside one — a gate can never show it refusing. The witness here
 * therefore masks the TOP limb to `topBits` rather than a full 12, which makes
 * the recomposition `acc.assertEquals(v)` tight on its own: an out-of-range `v`
 * loses bits and fails a plain equality that every instrument can see.
 *
 * The first version of this function did not do that, and the negative test
 * written for it — 2^n at a bound of n bits — was GREEN. That is how it was
 * found.
 */
export function assertLtPow2(v: Field, n: number) {
  if (n <= 0) {
    v.assertEquals(Field(0));
    return;
  }
  if (n > 36) throw new Error(`assertLtPow2: ${n} bits is past the lookup budget`);
  const nl = Math.ceil(n / 12);
  const topBits = n - 12 * (nl - 1); // 1..12
  const limbs = Provable.witness(Provable.Array(Field, nl), () => {
    let x = v.toBigInt();
    const out: Field[] = [];
    for (let i = 0; i < nl; i++) {
      const width = BigInt(i === nl - 1 ? topBits : 12);
      out.push(Field(x & ((1n << width) - 1n)));
      x >>= width;
    }
    return out;
  });
  // Scale the TOP limb so that a 12-bit lookup on the scaled value is exactly a
  // `topBits` check on the limb.
  const checked = limbs.map((l, i) => (i === nl - 1 ? l.mul(1n << BigInt(12 - topBits)) : l));
  for (let i = 0; i < checked.length; i += 3)
    Gadgets.rangeCheck3x12(checked[i], checked[i + 1] ?? Field(0), checked[i + 2] ?? Field(0));
  // Offsets are 12 bits apart regardless of the top limb's own width.
  let acc = limbs[0];
  for (let i = 1; i < nl; i++) acc = acc.add(limbs[i].mul(1n << BigInt(12 * i)));
  acc.assertEquals(v);
}

/**
 * The CONSTRAINT half of `sample_bits(k)`: for a canonical `c < p < 2^31`,
 * `c = hi*2^k + sum_i b_i 2^i` with every `b_i` boolean and `hi < 2^(31-k)`.
 *
 * ⚑ SEPARATED FROM THE WITNESSING HALF ON PURPOSE. This is the ONE place in the
 * whole challenger where a witness can lie and the transcript still looks
 * right: without the bound on `hi`, the linear relation is satisfiable over
 * Pasta for ANY bit pattern at all (`hi = (c - lo) * 2^-k` always exists), so a
 * prover would derive whatever query index it liked out of a perfectly correct
 * sponge. A function that witnesses its own inputs cannot be shown to refuse a
 * dishonest one, so the pieces are arguments and
 * `fri-challenger-rows.ts` supplies a lying `hi` and requires a refusal.
 */
export function assertLowBitsSplit(c: Field, bits: Bool[], hi: Field, k: number) {
  if (bits.length !== k) throw new Error(`assertLowBitsSplit: ${bits.length} bits for k=${k}`);
  assertLtPow2(hi, 31 - k);
  let acc = hi.mul(1n << BigInt(k));
  for (let i = 0; i < k; i++) acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
  acc.assertEquals(c);
}

/** The same split with the low part forced to ZERO — the PoW condition. Cheaper
 *  than a bit decomposition because `sum b_i 2^i = 0` is not witnessed at all. */
export function assertLowBitsZero(c: Field, hi: Field, k: number) {
  assertLtPow2(hi, 31 - k);
  hi.mul(1n << BigInt(k)).assertEquals(c);
}

// ===========================================================================
// 3. The in-circuit challenger.
// ===========================================================================

/**
 * `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>` in circuit.
 *
 * ⚑ THE SCHEDULE IS COMPILE-TIME, THE VALUES ARE NOT. A verifier's observe/
 * sample sequence is fixed by the protocol parameters, not by the proof: 16
 * commitments of 8 lanes, 4 final-poly limbs, 16 arity tags, 19 indices. So
 * `inputBuffer`/`outputBuffer` are plain JS arrays whose LENGTHS are known
 * while the circuit is being built, and the whole duplex state machine unrolls
 * into straight-line constraints with no `Provable.if` on a buffer position
 * anywhere. That is what makes this affordable; a challenger whose schedule
 * depended on witnessed data would not be.
 *
 * Lane discipline: every state lane is kept `< 2^31` (one `reduceLane` per lane
 * after each permutation), every observed witness is range-checked on entry,
 * and every SAMPLED value is `canonicalLane`d — sampling is the one place a
 * non-canonical representative would be WRONG rather than merely large, because
 * p3 reads `as_canonical_u64` when it slices bits out of a challenge.
 */
export class Challenger {
  state: Field[] = Array(WIDTH).fill(Field(0));
  inputBuffer: Field[] = [];
  outputBuffer: Field[] = [];
  /** Instrumentation, out of circuit: permutations emitted so far. */
  perms = 0;

  duplexing() {
    const lanes = this.state.slice();
    for (let i = 0; i < this.inputBuffer.length; i++) lanes[i] = this.inputBuffer[i];
    this.inputBuffer = [];
    const out = provablePermBounded(lanes, LANE_MAX);
    const bound = permOutputBound(LANE_MAX);
    // Bring every lane back under 2^31: the state is re-fed to the permutation
    // on the next duplex, and the rate is squeezed as challenges.
    this.state = out.map((x) => reduceLane(x, bound));
    this.perms++;
    this.outputBuffer = this.state.slice(0, RATE);
  }

  /** Absorb one element. The value is a witness, so it is range-checked HERE —
   *  the bound chain is a claim about the witness and an unchecked one makes it
   *  vacuous. */
  observe(v: Field) {
    assertLaneLt2p31(v);
    this.outputBuffer = [];
    this.inputBuffer.push(v);
    if (this.inputBuffer.length === RATE) this.duplexing();
  }
  observeSlice(vs: Field[]) {
    for (const v of vs) this.observe(v);
  }
  observeDigest(d: BbDigest) {
    this.observeSlice(d.limbs);
  }
  /** `observe_algebra_element` — the limbs, in basis order. */
  observeExt(e: BbExt) {
    this.observeSlice(e.limbs);
  }
  /** A COMPILE-TIME constant: no range check, no witness. Used for the
   *  `log_arity` schedule tags, which are protocol data and not proof data. */
  observeConstant(c: bigint) {
    this.outputBuffer = [];
    this.inputBuffer.push(Field(c));
    if (this.inputBuffer.length === RATE) this.duplexing();
  }

  /** One base-field challenge, CANONICAL. */
  sample(): Field {
    if (this.inputBuffer.length > 0 || this.outputBuffer.length === 0) this.duplexing();
    const v = this.outputBuffer.pop()!;
    return canonicalLane(v, LANE_MAX);
  }
  /** `sample_algebra_element::<BinomialExtensionField<BabyBear,4>>()`. */
  sampleExt(): BbExt {
    return new BbExt({ limbs: Array.from({ length: EXT_D }, () => this.sample()) });
  }

  /**
   * `sample_bits(k)` — but returning the BITS, which is what a FRI query index
   * is for: `verifyQuery` consumes exactly these as its slot selectors and path
   * directions.
   *
   * A canonical sample `c < p < 2^31` is split as `c = hi*2^k + sum b_i 2^i`
   * with every `b_i` boolean and `hi < 2^(31-k)`. Both bounds are load-bearing:
   * the split is unique only because the low part cannot exceed `2^k` and the
   * high part cannot make up the difference, and without the high bound a
   * prover could shift bits out of the index entirely.
   */
  sampleBitsAsBits(k: number): Bool[] {
    if (k < 1 || k > 30) throw new Error(`sampleBitsAsBits: k=${k} out of range`);
    const c = this.sample();
    const bits = Provable.witness(Provable.Array(Bool, k), () => {
      const v = c.toBigInt();
      return Array.from({ length: k }, (_, i) => Bool(((v >> BigInt(i)) & 1n) === 1n));
    });
    const hi = Provable.witness(Field, () => Field(c.toBigInt() >> BigInt(k)));
    assertLowBitsSplit(c, bits, hi, k);
    return bits;
  }

  /**
   * `check_witness(bits, w)`, ASSERTED rather than returned.
   *
   * ⚑ At `bits == 0` this observes NOTHING and constrains nothing — that is not
   * an optimisation, it is what `grinding_challenger.rs:41-43` does, and the
   * deployed commit-phase PoW is 0 bits. Getting this wrong shifts the whole
   * transcript.
   *
   * At `bits > 0` the witness is absorbed and the next sample's low `bits` bits
   * are forced to zero — expressed as `c = hi * 2^bits` with `hi` bounded, so
   * the PoW costs one sample and one range check rather than a bit
   * decomposition.
   */
  assertCheckWitness(bits: number, witness: Field) {
    if (bits === 0) return;
    this.observe(witness);
    const c = this.sample();
    const hi = Provable.witness(Field, () => Field(c.toBigInt() >> BigInt(bits)));
    assertLowBitsZero(c, hi, bits);
  }
}

// ===========================================================================
// 4. The FRI transcript — `verify_fri`'s challenger schedule, both twins.
// ===========================================================================

export type FriTranscriptInput<Digest, Ext, F> = {
  /** Stands in for the batch-STARK observes that precede `verify_fri`. */
  preamble: F[];
  /** `proof.commit_phase_commits` — one MMCS root per fold layer. */
  commits: Digest[];
  /** `proof.final_poly` — `2^log_final_poly_len` extension coefficients. */
  finalPoly: Ext[];
  /** `proof.query_pow_witness`. */
  queryPowWitness: F;
};

export type FriChallengesOut<Ext, B> = {
  alpha: Ext;
  betas: Ext[];
  /** `num_queries` index bit-vectors, low bit first — exactly the shape
   *  `verifyQuery` consumes. */
  queryIndexBits: B[][];
};

/**
 * The schedule, read off `p3_fri::verifier::verify_fri` line for line
 * (`fri/src/verifier.rs:139-270`):
 *
 *   1. `alpha = sample_algebra_element()`                                :139
 *   2. per layer: `observe(commit)`; `check_witness(commit_pow, w)`;     :211-219
 *      `beta = sample_algebra_element()`
 *   3. `observe_algebra_slice(final_poly)`                               :236
 *   4. `observe(Val::from_usize(log_arity))` per layer                   :249-251
 *   5. `check_witness(query_pow_bits, query_pow_witness)`                :254
 *   6. per query: `index = sample_bits(log_global_max_height + extra)`   :268
 *
 * ⚑ ORDER IS THE WHOLE POINT. Step 4 exists so the variable-arity schedule is
 * bound BEFORE the query grind; step 5 before step 6 so the indices cost work.
 * Moving any of them past another is a real weakening that no hash KAT sees.
 */
export function deriveFriChallengesBigInt(
  input: FriTranscriptInput<bigint[], bigint[], bigint>,
  knobs: FriKnobs,
): FriChallengesOut<bigint[], boolean> & { perms: number } {
  const c = new ChallengerBigInt();
  c.observeSlice(input.preamble);
  const alpha = c.sampleExt();
  const betas: bigint[][] = [];
  for (let r = 0; r < knobs.layers; r++) {
    c.observeSlice(input.commits[r]);
    // `commit_pow_bits = 0` — returns without observing.
    if (!c.checkWitness(knobs.commitPowBits, 0n))
      throw new Error(`commit-phase PoW failed at layer ${r}`);
    betas.push(c.sampleExt());
  }
  for (const e of input.finalPoly) c.observeSlice(e);
  for (let r = 0; r < knobs.layers; r++) c.observe(BigInt(knobs.maxLogArity));
  if (!c.checkWitness(knobs.queryPowBits, input.queryPowWitness))
    throw new Error('the query PoW witness does not satisfy the deployed 16-bit grind');
  const queryIndexBits = Array.from({ length: knobs.numQueries }, () => {
    const v = c.sampleBits(knobs.indexBits);
    return Array.from({ length: knobs.indexBits }, (_, i) => ((v >> i) & 1) === 1);
  });
  return { alpha, betas, queryIndexBits, perms: c.perms };
}

/** The in-circuit twin of the same schedule. Returns the challenger too, so a
 *  caller can keep absorbing (the STARK continues after FRI). */
export function deriveFriChallenges(
  input: FriTranscriptInput<BbDigest, BbExt, Field>,
  knobs: FriKnobs,
): FriChallengesOut<BbExt, Bool> & { challenger: Challenger } {
  const c = new Challenger();
  c.observeSlice(input.preamble);
  const alpha = c.sampleExt();
  const betas: BbExt[] = [];
  for (let r = 0; r < knobs.layers; r++) {
    c.observeDigest(input.commits[r]);
    // ⚑ `commit_pow_bits = 0`: NOTHING is observed and nothing is constrained.
    c.assertCheckWitness(knobs.commitPowBits, Field(0));
    betas.push(c.sampleExt());
  }
  for (const e of input.finalPoly) c.observeExt(e);
  for (let r = 0; r < knobs.layers; r++) c.observeConstant(BigInt(knobs.maxLogArity));
  c.assertCheckWitness(knobs.queryPowBits, input.queryPowWitness);
  const queryIndexBits = Array.from({ length: knobs.numQueries }, () =>
    c.sampleBitsAsBits(knobs.indexBits),
  );
  return { alpha, betas, queryIndexBits, challenger: c };
}

/** Witness a whole transcript of the given shape — for `getRows()`. The values
 *  are irrelevant to the row count; the SHAPE is not. */
export function witnessTranscriptShape(
  knobs: FriKnobs,
  preambleLen: number,
): FriTranscriptInput<BbDigest, BbExt, Field> {
  const wit = <T>(f: () => T, t: any) => Provable.witness(t, f);
  return {
    preamble: Array.from({ length: preambleLen }, () => wit(() => Field(1), Field)),
    commits: Array.from({ length: knobs.layers }, () => wit(() => BbDigest.zero(), BbDigest)),
    finalPoly: Array.from({ length: knobs.finalPolyLen }, () => wit(() => BbExt.zero(), BbExt)),
    queryPowWitness: wit(() => Field(0), Field),
  };
}

// ===========================================================================
// 5. The ZkProgram.
// ===========================================================================

/** What a transcript proof carries out: the challenges, compressed into one
 *  digest so the public output is a fixed size independent of `num_queries`.
 *  ⚑ This is a BINDING of the derived values, not a re-derivation of them —
 *  the consumer re-hashes the challenges it was handed and compares. */
export class ChallengeDigest extends Struct({ limbs: Provable.Array(Field, DIGEST_ELEMS) }) {}

/**
 * **The Rung-3 statement.** Given a transcript (preamble, commit-phase
 * commitments, final polynomial, query PoW witness), the challenges are THESE
 * — `alpha`, every `beta`, and every query index — and the query PoW witness
 * really grinds `query_pow_bits` zeros.
 *
 * The public output binds all of them with the deployed sponge, so a consumer
 * (the query walk) can be handed the challenges in the clear and check they are
 * the ones this proof derived, instead of witnessing them.
 */
export function makeFriTranscriptProgram(knobs: FriKnobs, preambleLen: number) {
  const { layers, finalPolyLen, numQueries, indexBits } = knobs;
  return ZkProgram({
    name: `dregg-fri-transcript-l${layers}-q${numQueries}-p${preambleLen}`,
    publicOutput: ChallengeDigest,
    methods: {
      deriveChallenges: {
        privateInputs: [
          Provable.Array(Field, preambleLen),
          Provable.Array(BbDigest, layers),
          Provable.Array(BbExt, finalPolyLen),
          Field, // query PoW witness
        ],
        async method(
          preamble: Field[],
          commits: BbDigest[],
          finalPoly: BbExt[],
          queryPowWitness: Field,
        ) {
          const out = deriveFriChallenges(
            { preamble, commits, finalPoly, queryPowWitness },
            knobs,
          );
          // Bind every challenge into one digest with the same sponge the MMCS
          // uses. `alpha` and the betas are already canonical (they came out of
          // `sample`); the index bits are recomposed so the digest depends on
          // the indices themselves and not merely on their count.
          const row: Field[] = [...out.alpha.limbs];
          for (const b of out.betas) row.push(...b.limbs);
          for (const qb of out.queryIndexBits) {
            let acc = Field(0);
            for (let i = 0; i < indexBits; i++) acc = acc.add(qb[i].toField().mul(1n << BigInt(i)));
            row.push(acc);
          }
          const d = spongeBB(row);
          return { publicOutput: new ChallengeDigest({ limbs: d.limbs }) };
        },
      },
    },
  });
}

/** The out-of-circuit twin of the program's public output, so the KAT can check
 *  the PROVEN digest rather than only the intermediate challenges. */
export function challengeDigestBigInt(
  out: FriChallengesOut<bigint[], boolean>,
  knobs: FriKnobs,
): bigint[] {
  const row: bigint[] = [...out.alpha];
  for (const b of out.betas) row.push(...b);
  for (const qb of out.queryIndexBits) {
    let acc = 0n;
    for (let i = 0; i < knobs.indexBits; i++) if (qb[i]) acc += 1n << BigInt(i);
    row.push(acc);
  }
  return spongeBigInt(row);
}

// ===========================================================================
// 6. THE SEAM — the fold chain driven by DERIVED challenges.
// ===========================================================================

/**
 * **The Rung-5 statement, and the point of the whole exercise.**
 *
 * Rung 2/4 walk a FRI query at a WITNESSED index under WITNESSED betas. Rung 3
 * derives the index and the betas from a transcript. Neither alone is a FRI
 * verifier: the first proves "some index works", the second proves "the index
 * is i" — and a prover satisfies both by answering at its own index while
 * deriving a different one. This program is the JOIN, and the join is the only
 * place the two can be checked to be the SAME index.
 *
 * What is bound, and what is not:
 *
 *   BOUND — the query index and every `beta` come out of the transcript, not
 *   out of the witness. The SAME `commits[r]` that the challenger absorbs is the
 *   MMCS root round `r`'s row must open under, so a prover cannot absorb one
 *   commitment and open against another. The final polynomial is absorbed AND
 *   is the value the chain must land on. The query PoW is checked.
 *
 *   NOT BOUND — `initial`, the reduced opening the chain starts from. Binding it
 *   to an input-phase opening under `alpha` IS the DEEP quotient, and it is the
 *   next rung. Also not bound: the transcript's `preamble` to the batch-STARK's
 *   own observes (§3.12).
 */
export function makeDerivedQueryProgram(opts: {
  knobs: FriKnobs;
  preambleLen: number;
  pathDepths: number[];
}) {
  const { knobs, preambleLen, pathDepths } = opts;
  const { layers, finalPolyLen, indexBits } = knobs;
  if (pathDepths.length !== layers) throw new Error('pathDepths.length != layers');
  const maxDepth = Math.max(...pathDepths, 1);

  class DerivedQueryClaim extends Struct({
    commits: Provable.Array(BbDigest, layers),
    finalPoly: Provable.Array(BbExt, finalPolyLen),
  }) {}

  const prog = ZkProgram({
    name: `dregg-fri-derived-query-l${layers}-p${preambleLen}`,
    publicInput: DerivedQueryClaim,
    publicOutput: Field, //  the DERIVED query index the chain walked
    methods: {
      proveDerivedQuery: {
        privateInputs: [
          Provable.Array(Field, preambleLen),
          Field, //                                       query PoW witness
          BbExt, //                                       the initial reduced opening
          Provable.Array(BbExt, layers), //               siblings
          Provable.Array(Provable.Array(BbDigest, maxDepth), layers),
        ],
        async method(
          claim: DerivedQueryClaim,
          preamble: Field[],
          queryPowWitness: Field,
          initial: BbExt,
          siblings: BbExt[],
          paths: BbDigest[][],
        ) {
          const chal = deriveFriChallenges(
            {
              preamble,
              commits: claim.commits,
              finalPoly: claim.finalPoly,
              queryPowWitness,
            },
            knobs,
          );
          const bits = chal.queryIndexBits[0];
          verifyCommitPhase({
            indexBits: bits,
            initial,
            rounds: Array.from({ length: layers }, (_, r) => ({
              sibling: siblings[r],
              path: paths[r].slice(0, pathDepths[r]),
              // ⚑ THE SEAM: the commitment the challenger ABSORBED is the one
              // the row must open under. Two different arrays here would make
              // the whole composition decorative.
              beta: chal.betas[r],
              commit: claim.commits[r],
            })),
            rollIns: [],
            finalPoly: claim.finalPoly,
            logGlobalMaxHeight: knobs.logGlobalMaxHeight,
          });
          let acc = Field(0);
          for (let i = 0; i < indexBits; i++)
            acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
          return { publicOutput: acc };
        },
      },
    },
  });
  return { prog, DerivedQueryClaim };
}
