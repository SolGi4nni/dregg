import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';

// ---------------------------------------------------------------------------
// WHICH KEY IS THIS — the named registry of verification-key NOTIONS, and a
// refusal that says which one it wanted.
//
// ⚑ THE OBSERVATION THAT PRODUCED THIS FILE. `DreggHeadGate.advanceHead` pins a
// `TERMINAL_VK_HASH` that comes out of an o1js `.compile()`. dregg's key
// REGISTERED on Mina devnet (`devnet-foreign-vk-registration.json`, account
// `B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm`) is DERIVED from
// Lean-emitted `KimchiWrapMain` gates. The two numbers differ, and `advanceHead`
// would refuse the registered one.
//
// ⚑ AND THAT IS CORRECT. They are NOT two epochs of one object; they are two
// objects at OPPOSITE ENDS OF THE BRIDGE, and neither was ever an input to the
// other's consumer:
//
//   PROVER SIDE, INSIDE OUR OWN CIRCUIT. `terminalVkHash` is a compile-time
//   constant baked into a zkApp's verification key so that `DynamicProof.verify`
//   accepts exactly ONE side-loaded o1js program. o1js says a `DynamicProof`
//   circuit "makes no assertions about the verificationKey used on its own", so
//   the pin is what stops the gate verifying SOME program's proof and calling it
//   dregg's. The object it names is an o1js `ZkProgram` — a verifier OF dregg's
//   STARK, written in o1js, compiled by o1js.
//
//   VERIFIER SIDE, IN MINA'S LEDGER. The registered key is ACCOUNT STATE. It is
//   the object Mina's `make_zkapp_verifier_index` reconstructs a `VerifierIndex`
//   from when it checks a zkApp proof. The circuit it keys is dregg's OWN
//   Lean-authored `wrap_main` assembly, encoded as a
//   `Pickles.Side_loaded.Verification_key.Stable.V2`.
//
// One is "which o1js program may speak to our gate". The other is "which circuit
// Mina will check dregg's proofs against". A hash comparison between them is a
// category error, and until this file existed it produced an ANONYMOUS NUMBER
// MISMATCH — the shape in which a real drift and a category error are
// indistinguishable, and the shape this tree has been bitten by before (the
// head's nine `vk_pin` literals named a program no descriptor in this tree had,
// and one test caught it).
//
// ⚑ SO: EVERY NOTION IS NAMED, ITS VALUE IS READ FROM ITS PRODUCER RATHER THAN
// WRITTEN HERE, AND A MISMATCH IS REPORTED BY NAME. `KNOWN_VK_NOTIONS` carries
// PROSE ONLY — not one hash literal — because a constant pinned against a copy
// of itself is decoration. `resolveVkNotions` goes to the artifacts.
//
// ⚑ WHAT THIS DOES NOT DO. It does not verify anything. Identifying a key by its
// hash is a LOOKUP; it says which of the tree's known circuits a number belongs
// to, so a refusal can name it. Every soundness statement about either object
// lives where that object does.
// ---------------------------------------------------------------------------

/** Which end of the bridge a key lives at. The distinction the anonymous hash
 *  mismatch was hiding. */
export type VkSide =
  /** A compile-time pin INSIDE one of our zkApp circuits, naming the one
   *  side-loaded o1js program that circuit will verify. */
  | 'prover-side-pin'
  /** Account state in Mina's ledger — the key Mina reconstructs a
   *  `VerifierIndex` from. */
  | 'mina-ledger-account-state';

export type VkNotion = {
  /** Stable machine name. This is what a refusal prints. */
  id: string;
  /** WHICH CIRCUIT this is the key of, in words. Never "the dregg VK". */
  circuit: string;
  /** Which toolchain produced the key object itself. */
  producedBy: 'o1js .compile()' | 'pickles-vk-derive (Lean-emitted gates)';
  side: VkSide;
  /** The command that regenerates the value. */
  producer: string;
  /** Path, relative to `bridge/mina-zkapp`, whose contents ARE the current
   *  value. Read at resolve time; never transcribed into this file. */
  valuePath: string;
  /** The SOURCE FILE that writes `valuePath`, relative to `bridge/mina-zkapp`.
   *
   *  ⚑ WHY IT IS DECLARED SEPARATELY. A notion whose producer has never been run
   *  in this checkout resolves to ABSENT, and an absent value is indistinguishable
   *  from a `valuePath` that names a file NOTHING WRITES. The author of this
   *  registry got that wrong on the first pass (the shrink pins land in
   *  `.fullchain/uniform-claim-shrink/`, not `.fullchain/`), and only noticed by
   *  reading the producer. So the gate reads it too: the source must exist and
   *  must mention the artifact it is credited with writing. Two independent
   *  places, which is the difference between a gate and a decoration.
   *
   *  `null` when NOTHING IN THE TREE WRITES `valuePath` — which is a real state
   *  and worth printing rather than papering over: `devnet-foreign-vk-
   *  registration.json` is a HAND-MAINTAINED deployment record, written by no
   *  script (grep-exhaustive, 2026-08-05), so its prose goes stale silently and
   *  its numbers are as good as the last person to edit them.
   *
   *  ⚠ WHAT IT DOES NOT ESTABLISH: that the producer writes `valuePath` to that
   *  exact path. Both key rings are written through a TEMPLATE
   *  (`key-${specName(sp)}.json`, uniform-claim-keys.ts:332,419) and the shrink
   *  pins through a composed directory, so there is no literal to compare. This
   *  says the credited producer EXISTS — the `mina-shrink-head` class, where an
   *  npm script named a `dist/` file with no source at all. */
  producerSource: string | null;
  /** How to get the hash out of `valuePath`. */
  valueField: (j: any) => string | undefined;
  /** A second, independent path that must agree with `valuePath` — the emitted
   *  pin file that mirrors the producer. `null` when the notion has only one
   *  source. */
  mirrorPath: string | null;
  mirrorField: ((j: any) => string | undefined) | null;
  /** Who consumes this key, at file:line. */
  consumer: string;
  /** What a reader must know before quoting this key. Empty string for none. */
  caveat: string;
};

/**
 * The verification-key notions this tree has. PROSE ONLY — adding a hash here
 * would make every downstream comparison a pin against its own definition.
 */
export const KNOWN_VK_NOTIONS: readonly VkNotion[] = [
  {
    id: 'o1js-rootfriuniform-terminal-babybear',
    circuit:
      'o1js ZkProgram `dregg-root-fri-block42-CLAIM` — the TERMINAL POSITION of the ' +
      'RootFriUniform claim-carrying chain (131 programs / 912 steps, key-tree depth 8, ' +
      'leaf 130), which verifies dregg\'s root batch-STARK over its real p3-emitted ' +
      'BabyBear MMCS commitments',
    producedBy: 'o1js .compile()',
    side: 'prover-side-pin',
    producer:
      'CLAIMKEYS_SUITE=babybear HEAD_KEYS=.fullchain/uniform-claim npm run uniform-claim-keys, ' +
      'then npm run head-anchor-pins -- --emit',
    valuePath: '.fullchain/uniform-claim/key-block42.json',
    producerSource: 'scripts/uniform-claim-keys.ts',
    valueField: (j) => j?.hash,
    mirrorPath: 'dregg-chain-pins.json',
    mirrorField: (j) => j?.terminalVkHash,
    consumer: 'DreggHeadAnchor.ts:543 — DreggHeadGate.advanceHead / reportFork',
    caveat: '',
  },
  {
    id: 'o1js-rootfriuniform-terminal-pasta',
    circuit:
      'o1js ZkProgram `dregg-root-fri-block9-CLAIM` — the terminal position of the PASTA-suite ' +
      'RootFriUniform chain (12 programs / 199 steps, leaf 11)',
    producedBy: 'o1js .compile()',
    side: 'prover-side-pin',
    producer:
      'CLAIMKEYS_SUITE=pasta HEAD_KEYS=.fullchain/uniform-claim-pasta npm run uniform-claim-keys, ' +
      'then npm run head-anchor-pins -- --emit',
    valuePath: '.fullchain/uniform-claim-pasta/key-block9.json',
    producerSource: 'scripts/uniform-claim-keys.ts',
    valueField: (j) => j?.hash,
    mirrorPath: 'dregg-chain-pins-pasta.json',
    mirrorField: (j) => j?.terminalVkHash,
    consumer: 'DreggHeadAnchor.ts:543, when built from dregg-chain-pins-pasta.json',
    caveat:
      'THE PASTA CHAIN IS A RE-MINT. It is fed `rehashRealRootFri(pastaSuite)` ' +
      '(head-anchor-pins.ts:127, uniform-claim-keys.ts:182): the opened VALUES are real but the ' +
      'MMCS digests are RECOMPUTED from those openings, so RootConsume.ts:389-393 in its own ' +
      'voice — "the input-phase equalities are true by construction and PROVE NOTHING ABOUT THE ' +
      'PROVER". Nothing binds to dregg\'s real BabyBear root. A key for it is a real key; the ' +
      'chain under it settles nothing.',
  },
  {
    id: 'o1js-shrink-partition-walk',
    circuit:
      'o1js ZkProgram `walk` of MinaShrinkPartition — the o1js Kimchi verifier of dregg\'s ' +
      'NATIVE-PASTA batch-STARK shrink terminal (the `DreggMinaConfig` shrink of the apex)',
    producedBy: 'o1js .compile()',
    side: 'prover-side-pin',
    producer: 'npm run mina-shrink-partition',
    //  `mina-shrink-partition.ts:38,213` — WORK is `.fullchain/uniform-claim-shrink`.
    valuePath: '.fullchain/uniform-claim-shrink/shrink-partition-pins.json',
    producerSource: 'scripts/mina-shrink-partition.ts',
    valueField: (j) => j?.terminalVkHash,
    mirrorPath: null,
    mirrorField: null,
    consumer: 'DreggShrinkHead.ts:138 — DreggShrinkHeadGate.advanceHead',
    caveat:
      'A DIFFERENT SEAL FAMILY from the RootFriUniform head gate: three-field UNTAGGED ' +
      '`partitionTerminalSeal`, not the four-field tagged `airTerminalSeal`. The two gates cannot ' +
      'consume each other\'s terminals even if the keys were swapped.',
  },
  {
    id: 'lean-kimchi-wrapmain-w4bind',
    circuit:
      'the LEAN-EMITTED `Dregg2.Circuit.Emit.KimchiWrapMain` wrap_main assembly at rung ' +
      '`w4_bind`, padded to Mina\'s 2^14 wrap domain and encoded as a ' +
      '`Pickles.Side_loaded.Verification_key.Stable.V2` (1796 bytes, 28 Pallas commitments)',
    producedBy: 'pickles-vk-derive (Lean-emitted gates)',
    side: 'mina-ledger-account-state',
    producer:
      'cargo run --release --manifest-path metatheory/fixtures/pickles-vk-derive/Cargo.toml ' +
      '-- <out-dir> --log2-domain 14',
    valuePath: 'devnet-foreign-vk-registration.json',
    //  ⚑ NOTHING WRITES THIS FILE. It is a hand-maintained deployment record;
    //  `devnet-register-foreign-vk.ts` sends the transaction and does not emit it.
    producerSource: null,
    valueField: (j) => j?.vk?.hash,
    mirrorPath: null,
    mirrorField: null,
    consumer:
      'MINA ITSELF — `make_zkapp_verifier_index` on devnet account ' +
      'B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm. NO o1js gate in this tree ' +
      'consumes it, and none can.',
    caveat:
      'THE VALUE READ HERE IS THE REGISTERED EPOCH, NOT HEAD\'S. The registration record\'s own ' +
      '`theHashIsNotStableAcrossCommits` note says the derived hash moves when the Lean assembly ' +
      'moves. `resolveVkNotions` measures that separately — see `leanEmissionEpoch`.',
  },
] as const;

export function vkNotion(id: string): VkNotion {
  const n = KNOWN_VK_NOTIONS.find((k) => k.id === id);
  if (n === undefined)
    throw new Error(
      `no verification-key notion named '${id}'. Known: ${KNOWN_VK_NOTIONS.map((k) => k.id).join(', ')}`,
    );
  return n;
}

export type ResolvedVk = {
  notion: VkNotion;
  /** The current value, or `null` when the producer has not been run in this
   *  checkout. NEVER a default — an absent artifact is absent. */
  hash: bigint | null;
  /** Why `hash` is null, or '' when it is not. */
  absent: string;
  /** Set when `mirrorPath` disagrees with `valuePath`: this notion is ONE object
   *  and its pin has DRIFTED from its producer. This is the wound the sibling
   *  `check_subproof_program_pin` closes by recomputing rather than trusting a
   *  literal, and it is why the mirror is read at all. */
  drift: string;
};

/**
 * The Lean wrap emission's own identity, measured rather than recited.
 *
 * ⚑ WHY A SHA AND NOT A HASH. The derived VK hash is only obtainable by running
 * `pickles-vk-derive` (a release cargo build), which a cheap gate cannot do. The
 * emission fixture's sha256 is the thing the registration record itself named as
 * "the real anchor: if a future re-derivation disagrees with `vk.hash`, check
 * that sha FIRST". Two emissions with the same sha derive the same key; a
 * different sha means the circuit moved and the chain simply holds an older one.
 */
export type LeanEmissionEpoch = {
  /** sha256 of `metatheory/fixtures/pickles-vk-derive/fixtures/wrapmain_smoke_w4_bind.json`. */
  currentSha256: string | null;
  /** sha256 the registered key was derived from, read from the registration
   *  record — never transcribed here. */
  registeredSha256: string | null;
  /** `public_input_size` / gate count of the CURRENT emission. */
  currentShape: string | null;
  /** The registered emission's shape, in the registration record's own words. */
  registeredShape: string | null;
  /** True when the two shas agree — i.e. the chain holds HEAD's circuit. */
  chainHoldsCurrent: boolean;
};

function readJson(p: string): any | null {
  if (!existsSync(p)) return null;
  try {
    return JSON.parse(readFileSync(p, 'utf8'));
  } catch {
    return null;
  }
}

/**
 * ⚑ THE SEAM THAT MAKES THE DRIFT CHECK REFUTABLE. `drift` below is the only
 * check here that can catch the "one object, two epochs" wound, and on a healthy
 * tree it is never exercised — which is exactly the shape of a gate nobody has
 * proved can go red. `perturb` lets a self-test hand the resolver a mutated copy
 * of a pin file IN MEMORY, so the red path is demonstrated without touching a
 * tracked file (this working tree is shared with other lanes).
 *
 * It is a TEST SEAM and it is never reached in a normal run: `resolveVkNotions`
 * with no second argument reads the artifacts and nothing else.
 */
export type VkResolveOpts = {
  /** Called with each artifact's repo-relative path and its parsed contents;
   *  returns what the resolver should see instead. */
  perturb?: (relPath: string, parsed: any) => any;
};

/**
 * Read every notion's CURRENT value from its producer's artifact.
 *
 * @param appRoot absolute path to `bridge/mina-zkapp`.
 */
export function resolveVkNotions(appRoot: string, opts: VkResolveOpts = {}): ResolvedVk[] {
  const load = (rel: string): any | null => {
    const j = readJson(resolve(appRoot, rel));
    return opts.perturb === undefined || j === null ? j : opts.perturb(rel, j);
  };
  return KNOWN_VK_NOTIONS.map((notion) => {
    const j = load(notion.valuePath);
    if (j === null)
      return {
        notion,
        hash: null,
        absent: `${notion.valuePath} does not exist — run: ${notion.producer}`,
        drift: '',
      };
    const raw = notion.valueField(j);
    if (raw === undefined || raw === null || String(raw).length === 0)
      return {
        notion,
        hash: null,
        absent: `${notion.valuePath} exists but carries no key hash where one was expected`,
        drift: '',
      };
    const hash = BigInt(String(raw));
    let drift = '';
    if (notion.mirrorPath !== null && notion.mirrorField !== null) {
      const m = load(notion.mirrorPath);
      if (m === null) {
        drift = `${notion.mirrorPath} does not exist, so nothing mirrors the producer`;
      } else {
        const mr = notion.mirrorField(m);
        if (mr === undefined || String(mr).length === 0) {
          drift = `${notion.mirrorPath} carries no value for this notion`;
        } else if (BigInt(String(mr)) !== hash) {
          drift =
            `${notion.mirrorPath} pins ${String(mr)} but its PRODUCER ` +
            `${notion.valuePath} now holds ${hash.toString()}. ONE OBJECT, DRIFTED: a ` +
            're-emission moved the key and the pin did not follow. Re-run: ' +
            notion.producer;
        }
      }
    }
    return { notion, hash, absent: '', drift };
  });
}

/** Measure the Lean wrap emission's epoch against the registered one. */
export function leanEmissionEpoch(appRoot: string, repoRoot: string): LeanEmissionEpoch {
  const emissionPath = resolve(
    repoRoot,
    'metatheory/fixtures/pickles-vk-derive/fixtures/wrapmain_smoke_w4_bind.json',
  );
  let currentSha256: string | null = null;
  let currentShape: string | null = null;
  if (existsSync(emissionPath)) {
    const bytes = readFileSync(emissionPath);
    currentSha256 = createHash('sha256').update(bytes).digest('hex');
    const j = readJson(emissionPath);
    if (j !== null)
      currentShape =
        `${Array.isArray(j.gates) ? j.gates.length : '?'} Lean rows, ` +
        `public input ${j.public_input_size ?? '?'}`;
  }
  const reg = readJson(resolve(appRoot, 'devnet-foreign-vk-registration.json'));
  const registeredSha256: string | null = reg?.derivedFrom?.emissionSha256 ?? null;
  const registeredShape: string | null = reg?.vk?.circuit ?? null;
  return {
    currentSha256,
    registeredSha256,
    currentShape,
    registeredShape,
    chainHoldsCurrent:
      currentSha256 !== null && registeredSha256 !== null && currentSha256 === registeredSha256,
  };
}

/** What a supplied hash IS, as far as this tree knows. */
export function identifyVkHash(hash: bigint, resolved: ResolvedVk[]): ResolvedVk | null {
  return resolved.find((r) => r.hash !== null && r.hash === hash) ?? null;
}

/**
 * ⚑ THE REFUSAL. A hash mismatch that says only "mismatch" is how this stayed
 * invisible; this names the circuit that was wanted, the circuit that arrived,
 * and — when they are different objects — WHY re-deriving either cannot help.
 */
export function explainVkMismatch(
  wantId: string,
  got: bigint,
  resolved: ResolvedVk[],
): string {
  const want = resolved.find((r) => r.notion.id === wantId);
  if (want === undefined)
    throw new Error(`explainVkMismatch: '${wantId}' is not a known notion`);
  const w = want.notion;
  const lines: string[] = [];
  lines.push(`WANTED  ${w.id}`);
  lines.push(`        ${w.circuit}`);
  lines.push(`        produced by ${w.producedBy}; ${w.side}`);
  lines.push(`        value        ${want.hash === null ? `ABSENT — ${want.absent}` : want.hash}`);
  lines.push(`        regenerate   ${w.producer}`);
  lines.push('');
  lines.push(`SUPPLIED ${got}`);

  const hit = identifyVkHash(got, resolved);
  if (hit === null) {
    lines.push('        This is NOT a key this tree knows. It is neither a stale epoch of the');
    lines.push('        wanted circuit nor any other named notion here. Known notions:');
    for (const r of resolved)
      lines.push(
        `          ${r.notion.id.padEnd(38)} ${r.hash === null ? '(absent in this checkout)' : r.hash}`,
      );
    return lines.join('\n');
  }
  if (hit.notion.id === w.id) {
    lines.push('        This IS the wanted notion — so the two disagree as ONE OBJECT AT TWO');
    lines.push('        EPOCHS. Something re-emitted and something else did not follow.');
    lines.push(`        Re-run its producer: ${w.producer}`);
    return lines.join('\n');
  }
  const g = hit.notion;
  lines.push(`        = ${g.id}`);
  lines.push(`        ${g.circuit}`);
  lines.push(`        produced by ${g.producedBy}; ${g.side}`);
  lines.push(`        consumed by ${g.consumer}`);
  lines.push('');
  lines.push('⚑ THESE ARE TWO DIFFERENT CIRCUITS, NOT TWO EPOCHS OF ONE.');
  if (g.side !== w.side) {
    lines.push('  They are at OPPOSITE ENDS OF THE BRIDGE:');
    lines.push(
      `    ${w.side === 'prover-side-pin' ? 'wanted' : 'supplied'}   is a compile-time pin inside one of OUR zkApp circuits — ` +
        'which side-loaded o1js program that circuit will verify;',
    );
    lines.push(
      `    ${w.side === 'prover-side-pin' ? 'supplied' : 'wanted'} is ACCOUNT STATE IN MINA'S LEDGER — the circuit Mina checks ` +
        'dregg\'s proofs against.',
    );
    lines.push('  No re-derivation, re-compile or re-registration makes one usable as the other.');
  } else {
    lines.push('  Both are prover-side pins, but they name different programs, and a proof of one');
    lines.push('  is not a proof of the other. Supply the terminal of the chain this gate pins.');
  }
  if (g.caveat) lines.push(`  ⚠ ${g.caveat}`);
  return lines.join('\n');
}
