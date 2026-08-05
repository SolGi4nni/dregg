// DREGG CAPABILITY, SIDE-LOADED — a capability whose AUTHORITY is a Mina verification key and
// whose SCOPE is dregg's own facet lattice, narrowable without the issuer's involvement.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ WHAT THIS IS FOR
//
// dregg's thesis is "a turn = the exercise of an attenuable proof-carrying token over owned state,
// leaving a receipt." Three clauses. A generic proof-verifier zkApp gets *proof-carrying* and
// nothing else — it checks that some proof verified under a key it already trusts. It has no notion
// of a token that can be NARROWED and handed on, which is the clause dregg is actually about.
//
// Side-loading is what makes the missing clause reachable, for one reason, and o1js says it out loud:
//
//     "NOTE: In the case of `DynamicProof`s, the circuit makes no assertions about the
//      verificationKey used on its own. This is the responsibility of the application developer"
//        — o1js 2.15.0, dist/node/lib/proof-system/proof.d.ts:121-123
//
// That is not a caveat, it is the whole affordance. A `DynamicProof` hands the circuit a proof
// verified under a key OF THE PROVER'S CHOOSING, plus that key's identity as a `Field`. Deciding
// WHICH keys count is then ordinary in-circuit arithmetic — and a decision procedure over key
// identities is exactly a capability policy. Attenuation is the case where the policy admits a key
// the gate has never seen, because the key that DID verify the parent vouched for it.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ WHY `authority` CANNOT BE FORGED — established at o1js source, not asserted here
//
// `DreggAttenuate.attenuate` sets the chain's authority to `parentVk.hash`. That would be worthless
// if `parentVk.hash` were a free witness, because the prover supplies the whole `VerificationKey`
// struct. It is not free. When a `DynamicProof` is verified, o1js re-derives the hash from the key
// MATERIAL inside the circuit and constrains the two to agree:
//
//     const circuitVk = Pickles.sideLoaded.vkToCircuit(() => vk.data);
//     const hash = inCircuitVkHash(circuitVk);
//     Field(hash).assertEquals(vk.hash, 'Provided VerificationKey hash not correct');
//     Pickles.sideLoaded.inCircuit(computedTag, circuitVk);
//        — o1js 2.15.0, dist/node/lib/proof-system/zkprogram.js:557-563
//
// where `inCircuitVkHash` is `Poseidon(prefix "MinaSideLoadedVk****" ‖ Pickles.sideLoaded.vkDigest)`
// (zkprogram.js:486-492). So `parentVk.hash` is pinned to the bytes that actually ran the parent
// verification. `authority` therefore names the key that really verified the parent, and a child
// cannot claim an ancestor it did not descend from.
//
// ⚠ Note this is STRICTLY STRONGER than what the chain checks at ingest. Mina's GraphQL/JSON door
// reads `data` and `hash` as independent fields and never calls `digest_vk`
// (`fields_derivers_zkapps.ml:555-574`, MEASURED by scripts/foreign-vk-register-gate.ts step E' —
// a bent tag byte and a lying hash were both ACCEPTED). The in-circuit path refuses both.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ WHAT o1js DEMANDS OF A FOREIGN PROOF, BEYOND WHAT PICKLES' VERIFIER CHECKS
//
// A side-loaded slot is opened by exactly one call, and every argument is frozen at the VERIFIER's
// compile time — so a foreign proof that disagrees with any of them cannot be admitted at all:
//
//     Pickles.sideLoaded.create(
//       tag.name,
//       Proof.maxProofsVerified,                      // 0 | 1 | 2  — the FOREIGN circuit's recursion arity
//       Proof.publicInputType?.sizeInFields()  ?? 0,  // app-state width, in Fp elements
//       Proof.publicOutputType?.sizeInFields() ?? 0,
//       featureFlagsToMlOption(Proof.featureFlags, withRuntimeTables))
//        — o1js 2.15.0, dist/node/lib/proof-system/zkprogram.js:594
//
// and the binding declares the same five (dist/node/bindings.d.ts:763-785). Feature flags are the
// sharpest of them; o1js states the consequence plainly:
//
//     "Only proofs that use the exact same composition of custom gates which were expected by
//      Pickles can be verified using side loading."   — proof.d.ts:141-142
//
// so a verifier compiled at `FeatureFlags.allNone` cannot verify a proof that uses a range-check or
// xor gate, no matter how sound that proof is. `allMaybe` accepts any composition and pays for it.
//
// ─────────────────────────────────────────────────────────────────────────────────────────────────
// ⚑ AND ONE THING o1js's OWN DOCUMENTATION GETS WRONG. MEASURED 2026-08-05.
//
// proof.d.ts:113-114 says of `maxProofsVerified`: "If you are unsure about what that is for you, you
// should use 2." That reads as an upper bound with padding underneath. IT IS NOT A BOUND. It must
// EQUAL the foreign proof's actual arity. Verifying one arity-0 proof through three slots that
// differ only in this number:
//
//     tag maxProofsVerified = 0  ->  PROVED (27.5s)
//     tag maxProofsVerified = 1  ->  "Constraint unsatisfied (unreduced) ...
//                                     step_verifier.ml line 1315 / step_main.ml line 85
//                                     prevs_verified"
//     tag maxProofsVerified = 2  ->  TypeError: Cannot read properties of undefined (reading '2')
//                                     (js_of_ocaml indexing a shorter array — not even a refusal)
//
// ⚑ THE CONSEQUENCE IS ARCHITECTURAL AND IT SHAPES THIS FILE. One side-loaded slot admits foreign
// programs of exactly ONE recursion arity. A root capability (verifies nothing, arity 0) and a
// delegated one (verifies its parent, arity 1) therefore CANNOT share a slot, which is why there are
// two proof classes below and two methods on the gate. Following o1js's advice here would have
// produced a contract that crashes on every proof it was built to accept.
//
// The good news for depth: attenuation is arity-preserving. Every attenuation step verifies exactly
// one proof, so a delegate at depth 1 and a delegate at depth 7 are both arity 1 and share a slot.
// The arity split is root-vs-delegate, once, not per level.
//
// scripts/dregg-capability-gate.ts re-measures all of this on every run rather than citing it.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE LATTICE IS DREGG'S, TRANSCRIBED — cell/src/facet.rs
//
// The scope carried here is `EffectMask = u32` (facet.rs:31), dregg's own faceted-capability
// bitmask, and the two predicates enforced in-circuit are its two exported functions verbatim:
//
//     is_facet_attenuation(parent, child)  :=  child & parent == child     (facet.rs:144-146)
//     is_effect_permitted(Some(m), bit)    :=  m != 0  &&  bit & m != 0    (facet.rs:160-166)
//
// ⚑ The `m != 0` conjunct is not decoration. It is dregg's P2-1 audit fix: `Some(0)` USED to read as
// "unrestricted", so a capability that looked maximally faceted was in fact unrestricted
// (facet.rs:154-159). A transcription that dropped it would reproduce the vulnerability, so the gate
// carries a control that a zero mask REFUSES.
//
// The numeric constraint is `FacetConstraint::MaxTransferAmount` with its attenuation order
// `is_at_least_as_tight: a <= b` (facet.rs:355-361, :400-404).
//
// ⚠ WHAT IS NOT HERE. `ExtendedFacet`'s other three constraints (`AllowedTargets`, `RateLimit`,
// `Budget`) are not carried. They are stateful or list-shaped and none of them is needed to show
// that narrowing binds. Their absence is a scope choice, not a claim that the mask plus one budget
// is the whole of dregg's facet algebra.

import {
  Bool,
  DynamicProof,
  FeatureFlags,
  Field,
  Gadgets,
  Provable,
  Struct,
  UInt64,
  Undefined,
  VerificationKey,
  ZkProgram,
} from 'o1js';

// ── dregg's effect bits, from cell/src/facet.rs:36-116 ───────────────────────────────────────────
// Transcribed rather than imported: this file is TypeScript and that file is Rust. The transcription
// is CHECKED — scripts/dregg-capability-gate.ts re-reads cell/src/facet.rs and refuses to run if any
// bit here disagrees with the shift the Rust declares, so a divergence is a red gate and not a
// comment that went stale.

export const EFFECT_SET_FIELD = 1n << 0n;
export const EFFECT_TRANSFER = 1n << 1n;
export const EFFECT_GRANT_CAPABILITY = 1n << 2n;
export const EFFECT_REVOKE_CAPABILITY = 1n << 3n;
export const EFFECT_EMIT_EVENT = 1n << 4n;
export const EFFECT_INCREMENT_NONCE = 1n << 5n;
export const EFFECT_CREATE_CELL = 1n << 6n;
export const EFFECT_SET_PERMISSIONS = 1n << 7n;
export const EFFECT_SET_VERIFICATION_KEY = 1n << 8n;
export const EFFECT_NOTE_SPEND = 1n << 9n;
export const EFFECT_NOTE_CREATE = 1n << 10n;
export const EFFECT_SEAL_OPS = 1n << 11n;
export const EFFECT_BRIDGE_OPS = 1n << 12n;
export const EFFECT_INTRODUCE = 1n << 13n;
export const EFFECT_OBLIGATION_OPS = 1n << 14n;
export const EFFECT_ESCROW_OPS = 1n << 15n;
export const EFFECT_DELEGATION_OPS = 1n << 16n;
export const EFFECT_SOVEREIGN_OPS = 1n << 17n;
export const EFFECT_QUEUE_OPS = 1n << 18n;
export const EFFECT_CAPTP_OPS = 1n << 19n;
export const EFFECT_REFUSAL = 1n << 20n;
export const EFFECT_LIFECYCLE_OPS = 1n << 21n;
export const EFFECT_BURN = 1n << 22n;
export const EFFECT_ATTENUATE_CAPABILITY = 1n << 23n;
export const EFFECT_SET_PROGRAM = 1n << 24n;
export const EFFECT_REACTIVE_OPS = 1n << 25n;
export const EFFECT_MINT = 1n << 26n;
export const EFFECT_ROTATE_PQ_IDENTITY = 1n << 27n;
export const EFFECT_ALL = 0xffff_ffffn;

/** The named facets, facet.rs:121-135. */
export const FACET_READ_ONLY = EFFECT_EMIT_EVENT;
export const FACET_TRANSFER_ONLY = EFFECT_TRANSFER;
export const FACET_STATE_WRITER = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
export const FACET_ADMIN =
  EFFECT_SET_PERMISSIONS | EFFECT_SET_VERIFICATION_KEY | EFFECT_ROTATE_PQ_IDENTITY;
export const FACET_DELEGATOR =
  EFFECT_GRANT_CAPABILITY | EFFECT_REVOKE_CAPABILITY | EFFECT_INTRODUCE;

/** `(name, shift)` for every bit above, so the gate can diff this table against the Rust. The names
 *  are the Rust constant suffixes exactly; a rename on either side shows up as a missing key. */
export const EFFECT_BITS: ReadonlyArray<readonly [string, bigint]> = [
  ['SET_FIELD', 0n],
  ['TRANSFER', 1n],
  ['GRANT_CAPABILITY', 2n],
  ['REVOKE_CAPABILITY', 3n],
  ['EMIT_EVENT', 4n],
  ['INCREMENT_NONCE', 5n],
  ['CREATE_CELL', 6n],
  ['SET_PERMISSIONS', 7n],
  ['SET_VERIFICATION_KEY', 8n],
  ['NOTE_SPEND', 9n],
  ['NOTE_CREATE', 10n],
  ['SEAL_OPS', 11n],
  ['BRIDGE_OPS', 12n],
  ['INTRODUCE', 13n],
  ['OBLIGATION_OPS', 14n],
  ['ESCROW_OPS', 15n],
  ['DELEGATION_OPS', 16n],
  ['SOVEREIGN_OPS', 17n],
  ['QUEUE_OPS', 18n],
  ['CAPTP_OPS', 19n],
  ['REFUSAL', 20n],
  ['LIFECYCLE_OPS', 21n],
  ['BURN', 22n],
  ['ATTENUATE_CAPABILITY', 23n],
  ['SET_PROGRAM', 24n],
  ['REACTIVE_OPS', 25n],
  ['MINT', 26n],
  ['ROTATE_PQ_IDENTITY', 27n],
];

/** Out-of-circuit `is_facet_attenuation`, facet.rs:144-146. Used only to predict what the circuit
 *  will do, so a control that is supposed to go red is known to be red for the stated reason. */
export const isFacetAttenuation = (parent: bigint, child: bigint) => (child & parent) === child;

/** Out-of-circuit `is_effect_permitted(Some(mask), bit)`, facet.rs:160-166, INCLUDING P2-1. */
export const isEffectPermitted = (mask: bigint, bit: bigint) => mask !== 0n && (bit & mask) !== 0n;

// ── the token ────────────────────────────────────────────────────────────────────────────────────

/**
 * What a proof of capability-possession exposes. This is the whole token: five field elements, no
 * signature, no bearer key. Possession of a proof whose public output is this record IS possession
 * of the capability — which is the point of a proof-carrying token.
 */
export class DreggCapability extends Struct({
  /**
   * The ROOT of the delegation chain, as the Mina verification-key hash of the program that issued
   * it. `Field(0)` is the sentinel for "I am myself a root, and my own key is my authority" — a
   * program cannot name its own verification key from inside itself, so the root's identity is
   * supplied by whoever verifies it: the gate checks `vk.hash`, and `DreggAttenuate` substitutes
   * `parentVk.hash` at the first attenuation step. See `attenuate` below.
   */
  authority: Field,
  /** High 16 bytes of the dregg `CellId` this capability is over. */
  subjectHi: Field,
  /** Low 16 bytes of the same. A `CellId` is 32 bytes and Pallas Fp is ~254 bits, so it does not
   *  fit in one element; splitting is the standard move and is stated rather than hidden. */
  subjectLo: Field,
  /** `EffectMask`, facet.rs:31. Range-checked to 32 bits everywhere it is produced. */
  effectMask: Field,
  /** `FacetConstraint::MaxTransferAmount`, facet.rs:327. A `UInt64` value carried as its `Field`. */
  maxTransfer: Field,
}) {}

// ── the root issuer ──────────────────────────────────────────────────────────────────────────────

/**
 * ISSUE a root capability. Its verification key hash IS the authority that every descendant chains
 * to, so compiling this program is what mints the root.
 *
 * ⚑ `authority` is hard-wired to `Field(0)` and is NOT an input. If it were an input, this program
 * would be a universal forger: anyone could run it, claim any authority and any mask, and every
 * downstream check would pass. The sentinel is what forces the identity to be supplied by a
 * verifier that has the key in hand.
 */
export const DreggCapabilityRoot = ZkProgram({
  name: 'dregg-capability-root',
  publicOutput: DreggCapability,
  methods: {
    issue: {
      privateInputs: [Field, Field, Field, UInt64],
      async method(subjectHi: Field, subjectLo: Field, effectMask: Field, maxTransfer: UInt64) {
        // `EffectMask` is a u32. Without this a "mask" could carry bits above 32 that
        // `Gadgets.and(_, _, 32)` would silently drop, and the drop would look like an attenuation.
        Gadgets.rangeCheck32(effectMask);
        return {
          publicOutput: new DreggCapability({
            authority: Field(0),
            subjectHi,
            subjectLo,
            effectMask,
            maxTransfer: maxTransfer.value,
          }),
        };
      },
    },
  },
});

// ── the side-loaded slot ─────────────────────────────────────────────────────────────────────────

/**
 * A ROOT capability proof — arity 0, because a root verifies nothing.
 *
 * Every field of this class is a COMPILE-TIME PIN on whoever verifies it; see the header. The arity
 * is 0 and not 2 because 2 does not work, measured, and the measurement is in the header.
 *
 * `featureFlags = allMaybe`: the root's gate composition differs from the attenuator's, and both must
 * be verifiable through slots built from one policy. `allMaybe` accepts any composition and pays a
 * proving overhead for it. ⚠ Do NOT read that as "allNone would refuse both" — measured, `allNone`
 * accepts the ROOT and refuses the ATTENUATOR; see the two `...AllNone` classes below for why.
 */
export class DreggRootCapabilityProof extends DynamicProof<undefined, DreggCapability> {
  static publicInputType = Undefined;
  static publicOutputType = DreggCapability;
  static maxProofsVerified = 0 as const;
  static featureFlags = FeatureFlags.allMaybe;
}

/**
 * A DELEGATED capability proof — arity 1, because every attenuation step verifies exactly one
 * parent. ⚑ Depth does not change this: a delegate at depth 1 and a delegate at depth 7 are both
 * arity 1, so ONE slot admits the whole tower below the root. That is what makes unbounded
 * attenuation depth expressible at all under the arity pin described in the header.
 */
export class DreggDelegatedCapabilityProof extends DynamicProof<undefined, DreggCapability> {
  static publicInputType = Undefined;
  static publicOutputType = DreggCapability;
  static maxProofsVerified = 1 as const;
  static featureFlags = FeatureFlags.allMaybe;
}

/**
 * The same two slots at `allNone`, existing ONLY so the gate can measure the feature-flag pin with a
 * control that moves BOTH ways. Nothing in the capability path uses them.
 *
 * ⚑ AND THE PAIR IS THE POINT, because the naive expectation is wrong. o1js says "Only proofs that
 * use the exact same composition of custom gates ... can be verified using side loading"
 * (proof.d.ts:141-142), which reads as though any circuit would be refused by `allNone`. MEASURED
 * 2026-08-05: the ROOT circuit side-loads through an `allNone` slot FINE, because `rangeCheck32`
 * compiles to generic gates and sets no flag; the ATTENUATOR does not, because `Gadgets.and` emits
 * `Xor16` and that is a flagged gate. So the pin is real but it bites on the GATE TYPES a circuit
 * actually emits, not on "does this circuit use gadgets". A one-sided probe would have concluded
 * the opposite, which is why both are here.
 */
export class DreggRootCapabilityProofAllNone extends DynamicProof<undefined, DreggCapability> {
  static publicInputType = Undefined;
  static publicOutputType = DreggCapability;
  static maxProofsVerified = 0 as const;
  static featureFlags = FeatureFlags.allNone;
}

export class DreggDelegatedCapabilityProofAllNone extends DynamicProof<undefined, DreggCapability> {
  static publicInputType = Undefined;
  static publicOutputType = DreggCapability;
  static maxProofsVerified = 1 as const;
  static featureFlags = FeatureFlags.allNone;
}

// ── the attenuator ───────────────────────────────────────────────────────────────────────────────

/**
 * NARROW a capability. This is the clause that makes the whole thing dregg-shaped: it runs with no
 * involvement from the issuer, produces a token under a DIFFERENT verification key, and the gate
 * will honor that token without ever having seen its key.
 *
 * Three things are enforced, and every one of them is a transcription:
 *
 *   1. `parent.verify(parentVk)` — and o1js constrains `parentVk.hash` to `parentVk.data` while
 *      doing it (zkprogram.js:557-563). This is what makes (3) unforgeable.
 *   2. `child & parent == child` — `is_facet_attenuation`, facet.rs:144-146. Authority narrows,
 *      never amplifies; `cannot_attenuate_widening` (turn/src/tests.rs:11849) is the Rust twin.
 *   3. `childMax <= parentMax` — `FacetConstraint::is_at_least_as_tight`, facet.rs:402-404.
 *
 * and the authority is carried, not chosen:
 *
 *      authority := if parent.authority == 0 then parentVk.hash else parent.authority
 *
 * so the first attenuation of a root FIXES the chain's authority to the root's real key, and every
 * later step inherits it unchanged. Depth is unbounded and the gate's check never changes.
 */
/**
 * The narrowing itself, shared by both methods below. `parent` is deliberately typed loosely: the
 * two callers differ ONLY in the arity of the slot the parent came through, and the algebra is
 * identical. Splitting the algebra as well as the slot would be two places for the lattice to drift.
 */
function narrow(
  p: DreggCapability,
  parentVkHash: Field,
  childMask: Field,
  childMaxTransfer: UInt64,
): DreggCapability {
  // (2) is_facet_attenuation(parent.effectMask, childMask). `Gadgets.and(_, _, 32)` range-checks
  // both operands to 32 bits as part of its own constraint set, so a childMask with bits above 32
  // cannot slip past by being truncated into agreement.
  Gadgets.and(childMask, p.effectMask, 32).assertEquals(
    childMask,
    'attenuation would AMPLIFY: child mask has a bit the parent does not (cell/src/facet.rs:144)',
  );

  // (3) is_at_least_as_tight for MaxTransferAmount.
  childMaxTransfer.assertLessThanOrEqual(
    UInt64.Unsafe.fromField(p.maxTransfer),
    'attenuation would RAISE the transfer ceiling (cell/src/facet.rs:402)',
  );

  return new DreggCapability({
    authority: Provable.if(p.authority.equals(0), parentVkHash, p.authority),
    subjectHi: p.subjectHi,
    subjectLo: p.subjectLo,
    effectMask: childMask,
    maxTransfer: childMaxTransfer.value,
  });
}

export const DreggAttenuate = ZkProgram({
  name: 'dregg-capability-attenuate',
  publicOutput: DreggCapability,
  methods: {
    /** FIRST narrowing: the parent is a root (arity 0). This is the step that FIXES the chain's
     *  authority, by substituting the root's real verification-key hash for the sentinel. */
    attenuateRoot: {
      privateInputs: [DreggRootCapabilityProof, VerificationKey, Field, UInt64],
      async method(
        parent: DreggRootCapabilityProof,
        parentVk: VerificationKey,
        childMask: Field,
        childMaxTransfer: UInt64,
      ) {
        parent.verify(parentVk);
        return { publicOutput: narrow(parent.publicOutput, parentVk.hash, childMask, childMaxTransfer) };
      },
    },

    /** SUBSEQUENT narrowings: the parent is itself a delegate (arity 1). The authority is already
     *  fixed and is inherited unchanged, so depth is unbounded and the gate's check never changes.
     *  ⚑ Both methods emit an arity-1 proof, which is why the whole tower shares one gate slot. */
    attenuateDelegated: {
      privateInputs: [DreggDelegatedCapabilityProof, VerificationKey, Field, UInt64],
      async method(
        parent: DreggDelegatedCapabilityProof,
        parentVk: VerificationKey,
        childMask: Field,
        childMaxTransfer: UInt64,
      ) {
        parent.verify(parentVk);
        return { publicOutput: narrow(parent.publicOutput, parentVk.hash, childMask, childMaxTransfer) };
      },
    },
  },
});

// ── THE ROGUE, and why the gate has to pin a second key ──────────────────────────────────────────

/**
 * ⚑ THE ATTACK THIS EXISTS TO EXHIBIT, and it is not hypothetical — an earlier revision of
 * `DreggCapabilityGate` was open to it.
 *
 * `authority` is unforgeable: it is `parentVk.hash`, pinned in-circuit to the bytes that verified the
 * parent. So a gate that checks ONLY `cap.authority == rootAuthority` knows the chain really
 * descends from its root. It does NOT know that the descent was a NARROWING — because the program
 * that computed the child's scope was chosen by the prover, and this file cannot stop someone
 * writing a different one.
 *
 * This is that different one. It is honest about the ancestry (it really verifies the parent, and
 * really derives `authority` from the key that did it) and simply DOES NOT CHECK THE NARROWING. Its
 * output is a capability with a mask and a ceiling of the prover's choosing, carrying the real root's
 * authority. Against a gate that pins only the root, it is a total forgery of scope.
 *
 * ⚑ SO THE GATE PINS TWO FIELDS: which capability TREE (`rootAuthority`) and which narrowing RULE
 * (`attenuatorProgram`). That is not a retreat from "a key the gate has never seen" — it relocates
 * the claim to where it is true. The gate has never seen, and cannot enumerate, the DELEGATES: how
 * many narrowings happened, who performed them, or to what. It holds two constants and honors an
 * unbounded tower. What it does fix is the attenuation SEMANTICS, which every capability system
 * fixes — biscuit fixes its Datalog evaluator, macaroons fix caveat evaluation. A system that let the
 * bearer choose the narrowing rule would not have a narrowing rule.
 *
 * scripts/dregg-capability-gate.ts compiles this, PROVES with it, prints that its output satisfies
 * every other conjunct the gate checks, and then shows the gate refusing it.
 */
export const DreggRogueAttenuate = ZkProgram({
  name: 'dregg-capability-rogue-attenuate',
  publicOutput: DreggCapability,
  methods: {
    forge: {
      privateInputs: [DreggRootCapabilityProof, VerificationKey, Field, UInt64],
      async method(
        parent: DreggRootCapabilityProof,
        parentVk: VerificationKey,
        anyMask: Field,
        anyCeiling: UInt64,
      ) {
        // Honest about the ancestry — this is what makes it dangerous rather than merely wrong.
        parent.verify(parentVk);
        const p = parent.publicOutput;
        // ⚑ AND THEN: no `is_facet_attenuation`, no `is_at_least_as_tight`. That is the whole attack.
        return {
          publicOutput: new DreggCapability({
            authority: Provable.if(p.authority.equals(0), parentVk.hash, p.authority),
            subjectHi: p.subjectHi,
            subjectLo: p.subjectLo,
            effectMask: anyMask,
            maxTransfer: anyCeiling.value,
          }),
        };
      },
    },
  },
});

// ── the in-circuit facet predicate, shared by the gate ───────────────────────────────────────────

/**
 * `is_effect_permitted(Some(mask), effectBit)` (facet.rs:160-166), as constraints.
 *
 * Returns a `Bool` rather than asserting, so a caller can report WHICH conjunct failed. Both are
 * required and the first is the P2-1 fix — see the file header. `Gadgets.and` range-checks its
 * operands, which is also what confines `effectBit` to the u32 the Rust declares.
 */
export function isEffectPermittedInCircuit(mask: Field, effectBit: Field): Bool {
  const nonEmpty = mask.equals(0).not(); // Some(0) => deny all  (facet.rs:163)
  const hit = Gadgets.and(mask, effectBit, 32).equals(0).not(); // bit & m != 0  (facet.rs:164)
  return nonEmpty.and(hit);
}
