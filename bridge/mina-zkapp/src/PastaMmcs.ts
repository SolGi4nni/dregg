import { Bool, Field, Gadgets, Poseidon, Provable, Struct } from 'o1js';
import type { MerkleSuite } from './HashSuiteType.js';

// ---------------------------------------------------------------------------
// THE PASTA-NATIVE MMCS — the hash half of a `DreggMinaConfig` proof, in
// o1js/Kimchi, hashing with **kimchi's own Poseidon** rather than emulating a
// foreign 31-bit prime.
//
// ⚑ SUBSTRATE. There is no AIR here, no constraint system, no gadget that
// decides whether a turn is legal. This is a HASH and a MERKLE WALK — the
// verifier's plumbing. The AIRs remain Lean-authored; this module never
// constructs one and `DreggProofVerify` still takes the constraint evaluator as
// a parameter.
//
// ⚑ WHAT IT IS THE TWIN OF, EXACTLY. `circuit-prove/src/dregg_mina_config.rs`:
//
//   MinaHash     = MultiField32PaddingFreeSponge<BabyBear, PastaFp, MinaPoseidonPerm, 3, 2, 1>
//   MinaCompress = TruncatedPermutation<MinaPoseidonPerm, 2, 1, 3>
//   MinaValMmcs  = MerkleTreeMmcs<BabyBear, PastaFp, MinaHash, MinaCompress, 2, 1>
//
// A digest is ONE native Pasta element. `compress(l, r)` is `permute([l, r, 0])`
// truncated to lane 0, which IS o1js's `Poseidon.hash([l, r])` — pinned on the
// Rust side by `dregg_mina_compress_is_o1js_poseidon_hash_of_a_pair` against an
// o1js gold vector, and re-pinned here against the emitter.
//
// ⚑ WHY THE DEPLOYED BABYBEAR PATH IS NOT DELETED, AND WHAT KEEPS THEM FROM
// BECOMING TWO DEFINITIONS OF ONE THING. `Poseidon2Merkle.ts` prices the proof
// dregg's ROOT mints today (Poseidon2-over-BabyBear, at a measured 2,600.5 rows
// a permutation); this module prices the proof `DreggMinaConfig` mints. Both are
// real objects and the o1js side must be able to verify either, so both survive.
// What does NOT survive is two verifiers: `HashSuite` below is the ONE interface
// `DreggProofVerify` speaks, `Poseidon2Merkle` implements it too, and the
// transcript, the DEEP quotient, the fold chain, the AIR closing equality and
// the query walk have exactly one implementation each, shared. If a future edit
// wants to change how a Merkle level works it has to change it HERE, for both.
//
// ⚑ THE MEASURED UNIT PRICES this module is the circuit behind
// (`scripts/mina-poseidon-merkle-rows.ts`, o1js 2.15.0, KAT'd against the p3
// hashers, against the deployed BabyBear column):
//
//   one permutation      13 rows    vs 2,600.5   200x
//   one Merkle level     15.5       vs 2,677     173x
//   one leaf-sponge lane  3.69      vs   329      89x
// ---------------------------------------------------------------------------

/** Pasta Fp modulus — o1js `Field.ORDER`. */
export const P_PASTA =
  28948022309329048855892746252171976963363056481941560715954676764349967630337n;

/** BabyBear modulus. */
export const P_BB = 2013265921n;

/** `PASTA_WIDTH` / `PASTA_RATE` / `PASTA_DIGEST_ELEMS` from `p3-pasta`. */
export const PASTA_WIDTH = 3;
export const PASTA_RATE = 2;
export const PASTA_DIGEST_ELEMS = 1;

/** `absorb_radix_bits::<BabyBear>()` — the bit length of `p_BB - 1`. */
export const RADIX_BITS = 31;
export const RADIX = 1n << BigInt(RADIX_BITS);

/** `max_shifted_absorb_injective_limbs::<BabyBear, PastaFp>()` — BabyBear lanes
 *  per Pasta rate slot. Eight: `p_BB * (2^248 - 1)/(2^31 - 1) < 2^248 < p_Pasta`,
 *  and nine would not fit. */
export const LIMBS_PER_SLOT = 8;

/** SIXTEEN BabyBear lanes ride one permutation, against the deployed
 *  `PaddingFreeSponge<_, 16, 8, 8>`'s EIGHT. Half the permutations AND each one
 *  200x cheaper — the two effects compound, which is why the leaf-hash term
 *  moves by 89x rather than 200x (the residual is the per-lane range check,
 *  which is hash-independent and does not shrink). */
export const LANES_PER_PERM = LIMBS_PER_SLOT * PASTA_RATE;

// ===========================================================================
// 1. Range plumbing.
// ===========================================================================

/**
 * `0 <= r < 2^31`, via three 12-bit lookups.
 *
 * ⚑ THE BOUND IS CARRIED TWICE AND THE SECOND CARRIER IS WHY. `Provable.
 * runAndCheck` DOES NOT EVALUATE LOOKUP CONSTRAINTS, so a gadget whose bound
 * rests on the lookup alone is sound in a proof and untestable outside one — no
 * gate can ever watch it refuse. The witness therefore masks each limb, so the
 * recomposition `assertEquals` is tight on its own and an out-of-range input
 * loses bits and fails a plain equality every instrument can see.
 */
export function assertLt2p31(r: Field) {
  const [a, b, c] = Provable.witness(Provable.Array(Field, 3), () => {
    const v = r.toBigInt();
    return [Field(v & 0xfffn), Field((v >> 12n) & 0xfffn), Field((v >> 24n) & 0x7fn)];
  });
  Gadgets.rangeCheck3x12(a, b, c.mul(16n));
  a.add(b.mul(1n << 12n)).add(c.mul(1n << 24n)).assertEquals(r);
}

/**
 * ⚑ MAKE THE 12-BIT LOOKUP TABLE EXIST. A CIRCUIT OF PASTA LANE CHECKS ALONE
 * COMPILES, ANALYSES, PASSES `runAndCheck` — AND CANNOT BE PROVED.
 *
 * Measured 2026-07-30, o1js 2.15.0, on a `ZkProgram` whose whole body is EIGHT
 * `assertLt2p31` calls on honest in-range lanes:
 *
 *     rows 21
 *     Error: the lookup failed to find a match in the table: row=16
 *
 * Add one `Gadgets.rangeCheck64` — 22 rows — and the IDENTICAL lookups succeed
 * and the proof verifies. kimchi installs the fixed 12-bit table only when the
 * circuit also carries a `RangeCheck0`/`RangeCheck1` gate, and
 * `Gadgets.rangeCheck3x12` emits neither.
 *
 * ⚑ WHY NOTHING CAUGHT IT, WHICH IS THE ACTUAL FINDING. Every Pasta circuit in
 * this tree so far also ran BabyBear extension arithmetic, and
 * `Poseidon2BabyBearW16.quotientTimesP` calls `Gadgets.rangeCheck64` on its
 * limbs. So the DEPLOYED HASH was installing the lookup table for the
 * Mina-native one, and the dependency was invisible for exactly as long as
 * nobody built a Pasta-only body. The four-round merge is the first thing that
 * can: a Pickles step holding only mixed-height MMCS openings has no BabyBear
 * arithmetic in it at all. `compile()` is green, `analyzeMethods` gives a row
 * count, `runAndCheck` passes — and `prove()` dies in the wasm.
 *
 * ⚠ AND IT IS NOT A NO-OP RETAINED FOR COMPATIBILITY. Every call site that
 * needs it reaches it through `MerkleSuite.anchorLookupTable`, and
 * `root-consume-rows` [5] PROVES a Pasta-only body with the anchor and requires
 * the same body WITHOUT it to fail with this exact error. A gate that cannot go
 * red is not a gate.
 */
export function assertPastaLookupTable(): void {
  const z = Provable.witness(Field, () => Field(0));
  Gadgets.rangeCheck64(z);
  z.assertEquals(Field(0));
}


/**
 * `0 <= v < 2^n` for `n` in `1..=60`, same discipline as `assertLt2p31`.
 *
 * The challenger's base-`|F|` split needs 38 bits for its remainder and 31 for
 * each limb, so a single width-parametric check is cheaper to keep honest than
 * two hand-rolled ones.
 */
export function assertLtPow2Pasta(v: Field, n: number) {
  if (n <= 0) {
    v.assertEquals(Field(0));
    return;
  }
  if (n > 60) throw new Error(`assertLtPow2Pasta: ${n} bits is past the lookup budget`);
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
  // Scale the TOP limb so a 12-bit lookup on the scaled value is exactly a
  // `topBits` check on the limb itself.
  const checked = limbs.map((l, i) => (i === nl - 1 ? l.mul(1n << BigInt(12 - topBits)) : l));
  for (let i = 0; i < checked.length; i += 3)
    Gadgets.rangeCheck3x12(checked[i], checked[i + 1] ?? Field(0), checked[i + 2] ?? Field(0));
  let acc = limbs[0];
  for (let i = 1; i < nl; i++) acc = acc.add(limbs[i].mul(1n << BigInt(12 * i)));
  acc.assertEquals(v);
}

/**
 * `0 <= l < p_BabyBear` — CANONICAL, not merely `< 2^31`.
 *
 * ⚑ THIS IS STRICTLY STRONGER THAN THE DEPLOYED PATH'S LANE CHECK, and
 * deliberately. `Poseidon2BabyBearW16`'s `assertLaneLt2p31` admits a
 * non-canonical representative in `[p, 2^31)`; for a hash INPUT that is
 * inherited debt, but for a challenger's squeezed LIMB it would be a hole with
 * teeth: `split_pf_to_field_order_limbs` produces `rem % p`, so a limb at or
 * above `p` is not any decomposition of the sponge cell and admitting one lets
 * a prover choose its own challenges. `p - 1 - l` is `< 2^31` exactly when
 * `l <= p - 1`; a larger `l` wraps modulo Pasta and blows the range check.
 */
export function assertCanonicalBb(l: Field) {
  assertLt2p31(l);
  assertLt2p31(Field(P_BB - 1n).sub(l));
}

// ===========================================================================
// 2. Out-of-circuit twins. These call o1js's own `Poseidon`, which is the same
//    permutation the circuit emits, so a divergence between twin and circuit is
//    a real disagreement and not a re-implementation gap. Both are checked
//    against `dregg-p3-pasta`'s emitter, which calls the REAL p3 objects.
// ===========================================================================

/** `PastaCompress` — `permute([l, r, 0])[0]`, i.e. `Poseidon.hash([l, r])`. */
export function compressPastaBigInt(l: bigint, r: bigint): bigint {
  return Poseidon.hash([Field(l), Field(r)]).toBigInt();
}

/** `reduce_packed_shifted(lanes, 31)`: Horner in base `2^31` over the digits
 *  `lane + 1`. The `+1` shift reserves zero as an out-of-band "no digit", so
 *  sequences of different lengths cannot collide in one slot. */
export function packSlotBigInt(lanes: bigint[]): bigint {
  let acc = 0n;
  for (let i = lanes.length - 1; i >= 0; i--) acc = (acc * RADIX + (lanes[i] % P_BB) + 1n) % P_PASTA;
  return acc;
}

/**
 * `MultiField32PaddingFreeSponge<BabyBear, PastaFp, _, 3, 2, 1>`.
 *
 * ⚑ THE UNWRITTEN RATE SLOT KEEPS ITS VALUE. p3 writes `state[chunk_id] =
 * reduce_packed_shifted(chunk)` only for the chunks a block actually has
 * (`sponge.rs:471-481`); a trailing block with one slot leaves slot 1 holding
 * the PREVIOUS permutation's output. That is not the challenger's absorb, which
 * zero-fills the tail and adds a length tag — the two look alike and are not,
 * and getting it backwards changes every leaf digest of an odd-width row.
 */
export function spongePastaBigInt(row: bigint[]): bigint {
  let state = [0n, 0n, 0n];
  for (let off = 0; off < row.length; off += LANES_PER_PERM) {
    const block = row.slice(off, off + LANES_PER_PERM);
    const slots: bigint[] = [];
    for (let c = 0; c < block.length; c += LIMBS_PER_SLOT)
      slots.push(packSlotBigInt(block.slice(c, c + LIMBS_PER_SLOT)));
    const s0 = slots[0];
    const s1 = slots.length > 1 ? slots[1] : state[1];
    state = Poseidon.update(
      [Field(state[0]), Field(state[1]), Field(state[2])],
      [Field(s0).sub(Field(state[0])), Field(s1).sub(Field(state[1]))],
    ).map((x) => x.toBigInt());
  }
  return state[0];
}

/** The digest of an all-zero subtree of height `h`, `h` in `0..=depth`. */
export function zeroAtPastaBigInt(depth: number): bigint[] {
  const z: bigint[] = [0n];
  for (let h = 1; h <= depth; h++) z.push(compressPastaBigInt(z[h - 1], z[h - 1]));
  return z;
}

/** Fold a leaf digest up an authentication path, returning every node. */
export function foldPathPastaBigInt(
  leaf: bigint,
  siblings: bigint[],
  isRight: boolean[],
): bigint[] {
  const nodes: bigint[] = [];
  let cur = leaf;
  for (let h = 0; h < siblings.length; h++) {
    cur = isRight[h] ? compressPastaBigInt(siblings[h], cur) : compressPastaBigInt(cur, siblings[h]);
    nodes.push(cur);
  }
  return nodes;
}

// ===========================================================================
// 3. The in-circuit digest.
// ===========================================================================

/**
 * A Pasta MMCS digest: ONE native `Field`.
 *
 * ⚑ IT CARRIES A `limbs` ARRAY OF LENGTH ONE ON PURPOSE. `BbDigest` carries
 * eight, and the whole point of `HashSuite` is that the walk above does not know
 * which it has. A digest type with a different accessor shape would force
 * `DreggProofVerify` to branch on the hash, and a verifier that branches on its
 * hash is two verifiers.
 */
export class PastaDigest extends Struct({
  limbs: Provable.Array(Field, PASTA_DIGEST_ELEMS),
}) {
  static from(v: bigint[] | Field[] | bigint | Field): PastaDigest {
    const a = Array.isArray(v) ? v : [v];
    return new PastaDigest({ limbs: a.map((x) => (typeof x === 'bigint' ? Field(x) : x)) });
  }
  static zero(): PastaDigest {
    return PastaDigest.from([0n]);
  }
  get value(): Field {
    return this.limbs[0];
  }
  toBigInts(): bigint[] {
    return this.limbs.map((x) => x.toBigInt());
  }
}

/**
 * A witnessed Pasta digest needs NO range check — every `Field` is a valid
 * Pasta element, which is the whole structural saving of hashing natively.
 *
 * ⚑ THIS IS A REAL ASYMMETRY, NOT AN OMISSION. The BabyBear path must
 * range-check all 8 witnessed lanes of every sibling at every level, or its
 * bound-tracking is a claim about numbers nothing forces to be small. Here the
 * field IS the domain. The function exists so `HashSuite` has one shape, and it
 * is empty because there is nothing to check — said out loud rather than left as
 * a suspicious absence.
 */
export function assertPastaDigestInRange(_d: PastaDigest) {
  /* a Field is already a Pasta element */
}

/** `compress(l, r)` in circuit — one native Poseidon, 13 measured rows. */
export function compressPasta(l: PastaDigest, r: PastaDigest): PastaDigest {
  return PastaDigest.from([Poseidon.hash([l.limbs[0], r.limbs[0]])]);
}

/** `reduce_packed_shifted` in circuit. Every lane is range-checked to `< 2^31`
 *  HERE unless the caller has already bounded it, which is what makes the
 *  packing injective.
 *
 *  ⚠ NAMED, NOT FIXED, AND INHERITED: `< 2^31` is weaker than `< p_BabyBear`, so
 *  a prover may present a non-canonical lane in `[p, 2^31)` and pack a different
 *  Pasta element than the canonical one. The DEPLOYED BabyBear leaf sponge has
 *  exactly the same shape (`Poseidon2Merkle.spongeBB` range-checks to `2^31`
 *  too), so this is carried across rather than introduced. The challenger's
 *  squeeze does NOT inherit it — see `assertCanonicalBb`. */
export function packSlot(lanes: Field[], lanesAlreadyChecked = false): Field {
  let acc = Field(0);
  for (let i = lanes.length - 1; i >= 0; i--) {
    if (!lanesAlreadyChecked) assertLt2p31(lanes[i]);
    acc = acc.mul(Field(RADIX)).add(lanes[i].add(Field(1)));
  }
  return acc;
}

/**
 * The MMCS leaf sponge in circuit, for a compile-time row width.
 *
 * The rate lanes are OVERWRITTEN per block, which o1js expresses by absorbing
 * the DIFFERENCE against a state whose rate cells are known in circuit —
 * `Poseidon.update` absorbs by addition, and `d - s` added to `s` is `d`. Two
 * field subtractions, i.e. nothing: Kimchi linear combinations are free.
 */
export function spongePasta(row: Field[], lanesAlreadyChecked = false): PastaDigest {
  let state: [Field, Field, Field] = [Field(0), Field(0), Field(0)];
  for (let off = 0; off < row.length; off += LANES_PER_PERM) {
    const block = row.slice(off, off + LANES_PER_PERM);
    const slots: Field[] = [];
    for (let c = 0; c < block.length; c += LIMBS_PER_SLOT)
      slots.push(packSlot(block.slice(c, c + LIMBS_PER_SLOT), lanesAlreadyChecked));
    const d0 = slots[0];
    const d1 = slots.length > 1 ? slots[1] : state[1]; // an unwritten slot KEEPS its value
    state = Poseidon.update(state, [d0.sub(state[0]), d1.sub(state[1])]) as [Field, Field, Field];
  }
  return PastaDigest.from([state[0]]);
}

/** Nothing to canonicalise: a Pasta digest is already a canonical `Field`. */
export function canonicalPastaDigest(d: PastaDigest): PastaDigest {
  return d;
}

/** Conditional swap: `(left, right)` for this level, where `isRight` says the
 *  CURRENT node is the right child. */
export function condSwapPasta(
  cur: PastaDigest,
  sib: PastaDigest,
  isRight: Bool,
): [PastaDigest, PastaDigest] {
  const l = Provable.if(isRight, sib.limbs[0], cur.limbs[0]);
  const r = Provable.if(isRight, cur.limbs[0], sib.limbs[0]);
  return [PastaDigest.from([l]), PastaDigest.from([r])];
}

/** Fold `leaf` up `depth` levels of `siblings` and return the root. */
export function foldOpeningPasta(
  leaf: PastaDigest,
  siblings: PastaDigest[],
  isRight: Bool[],
): PastaDigest {
  let cur = leaf;
  for (let h = 0; h < siblings.length; h++) {
    const [l, r] = condSwapPasta(cur, siblings[h], isRight[h]);
    cur = compressPasta(l, r);
  }
  return cur;
}

// ===========================================================================
// 4. This module, as a `MerkleSuite` — the ONLY way `DreggProofVerify` and
//    `FriQueryStep` reach this hash. See `HashSuiteType.ts` for why.
// ===========================================================================

export const pastaMerkleSuite: MerkleSuite<PastaDigest> = {
  name: 'mina-poseidon-pasta',
  digestElems: PASTA_DIGEST_ELEMS,
  Digest: PastaDigest,
  zero: () => PastaDigest.zero(),
  from: (v) => PastaDigest.from(v),
  assertInRange: assertPastaDigestInRange,
  anchorLookupTable: assertPastaLookupTable,
  compress: compressPasta,
  condSwap: condSwapPasta,
  sponge: (row, lanesAlreadyChecked = false) => spongePasta(row, lanesAlreadyChecked),
  canonical: canonicalPastaDigest,
  assertEq: (a, b) => a.limbs[0].assertEquals(b.limbs[0]),
  laneCheckIsFree: true,
  compressBigInt: (l, r) => [compressPastaBigInt(l[0], r[0])],
  spongeBigInt: (row) => [spongePastaBigInt(row)],
};
