// FOREIGN VERIFICATION KEY — build the account update that REGISTERS a `{data, hash}` we derived
// ourselves onto a Mina account, with no compiled o1js contract anywhere in the path.
//
// ⚑ WHY THIS FILE EXISTS. Every VK-bearing path in this repo, and every one in o1js's own examples,
// takes its key from `SmartContract.compile()` and hands it to `zkapp.deploy()`. That welds
// registration to a circuit o1js itself built. A key DERIVED elsewhere — `metatheory/fixtures/
// pickles-vk-derive` takes the Lean-assembled `KimchiWrapMain` gate list to a
// `Side_loaded_verification_key` — has the SAME wire shape and no way in. This module is the way in.
// It is deliberately provenance-BLIND: it sees `{data: string, hash: Field}` and cannot tell where
// either came from, which is the whole point.
//
// ─────────────────────────────────────────────────────────────────────────────────────────────────
// HOW A VK GETS ONTO AN ACCOUNT, ESTABLISHED AT SOURCE (paths under ~/dev/mina and node_modules/o1js)
//
// 1. THE FIELD. `Account_update.Update.Stable.V1.t` carries
//        `verification_key : Verification_key_wire.Stable.V1.t Set_or_keep.Stable.V1.t`
//    (mina/src/lib/mina_base/account_update.ml:695-696). It is `Set_or_keep`, NOT an option —
//    `Keep` means "do not touch". `Verification_key_wire.t` is
//        `(Side_loaded_verification_key.t, F.t) With_hash.t`
//    (mina/src/lib/mina_base/verification_key_wire.ml:22-23), i.e. the data AND the hash travel
//    together. o1js's layout agrees exactly: `AccountUpdateModification.verificationKey` is a
//    `flaggedOption` of `{ data: string, hash: Field }`
//    (o1js/src/bindings/mina-transaction/gen/v1/js-layout.ts:809-816).
//
// 2. ONLY THE HASH IS COMMITTED. The account update's hash input maps the wire value through
//    `With_hash.hash` and drops the data entirely (account_update.ml:864-866). o1js reproduces this
//    by typing `data` as the layout primitive `string`, whose provable instance is `emptyType` —
//    `toFields: () => []` (o1js/src/bindings/lib/generic.ts:67-68, 120-129). So the 1796 bytes of
//    key material contribute ZERO field elements to what gets signed. ⚠ The signature therefore does
//    NOT bind the data; it binds the hash. That is Mina's design, not a defect here, and it is why
//    the data↔hash tie has to be checked somewhere else — see (5).
//
// 3. THE PERMISSION. `set_verification_key` is a PAIR, `'controller * 'txn_version`
//    (mina/src/lib/mina_base/permissions.ml:367, instantiated :399-403). A fresh account gets
//    `Permissions.user_default`, whose entry is `(Signature, Txn_version.current)`
//    (permissions.ml:580-594) — so A SIGNATURE IS ENOUGH on a fresh account; a proof is not required
//    and never was. o1js's `Permissions.initial()` and `Permissions.default()` both say
//    `Permission.VerificationKey.signature()` (o1js/src/lib/mina/v1/account-update.ts:394, 410).
//    The check at application time is
//        `Local_state.add_check local_state Update_not_permitted_verification_key
//           Bool.(Set_or_keep.is_keep verification_key ||| has_permission)`
//    (mina/src/lib/transaction_logic/zkapp_command_logic.ml:1583-1586), where `has_permission` is
//    `Controller.check ~proof_verifies ~signature_verifies auth` and `auth` is downgraded from
//    Proof/Impossible to Signature when the account's stored txn_version is older than the chain's
//    (zkapp_command_logic.ml:1568-1577, fallback at permissions.ml:77-81). Current txn_version is 3
//    (mina/src/config/protocol_version/current.mlh:2).
//
// 4. AUTHORIZATION IS NOT A HARD RULE. Nothing anywhere says "setting a VK needs a proof". The only
//    gate is the account's own permission, checked as above. An account update that sets a VK may be
//    Signature-authorized, and that is exactly what o1js's own `deploy()` does —
//    `accountUpdate.account.verificationKey.set({hash, data}); ...; accountUpdate.requireSignature()`
//    (o1js/src/lib/mina/v1/zkapp.ts:675-678) — and what Mina's own test deploy does
//    (mina/src/lib/transaction_snark/transaction_snark.ml:4592-4606 with :4639-4642
//    `authorization = Signature signature`).
//
// 5. WHO CHECKS THAT `hash == digest_vk(data)`. THREE DIFFERENT ANSWERS, and they do not agree.
//    ⚑ ALL THREE MEASURED by `scripts/foreign-vk-register-gate.ts` step E', not just read:
//      • GraphQL / JSON ingest (THE DEVNET PATH): the two fields are read INDEPENDENTLY
//        (mina/src/lib/fields_derivers_zkapps/fields_derivers_zkapps.ml:555-574) and no `digest_vk`
//        runs. NO data↔hash VALIDATION. Measured by driving `ledger.applyJsonTransaction` — Mina's
//        own OCaml, js_of_ocaml-compiled — with three mutations of one accepted key:
//            bent curve point  → REFUSED, `...Affine.Stable.V1.Invalid_curve_point`
//            bent tag byte     → ACCEPTED, and the account now stores an INCONSISTENT pair
//            hash+1, data kept → ACCEPTED, ditto
//        ⚠ SO THE ONLY THING MINA REFUSES AT INGEST IS A KEY IT CANNOT DESERIALISE. The refusal
//        comes from `Side_loaded_verification_key.of_base64` reading Pallas points
//        (side_loaded_verification_key.ml:291-292), NOT from any hash check. An earlier draft of
//        this file said the JSON path "refuses a bent key"; it does not — it refuses an UNPARSEABLE
//        one, which is a different and much weaker statement.
//      • bin_prot (P2P gossip, persistence): the hash is NOT SENT. `of_binable` RECOMPUTES it —
//        `let of_binable vk : t = { data = vk; hash = digest_vk vk }`
//        (verification_key_wire.ml:30-46, comment: "don't send hash over the wire; restore hash on
//        receipt"). So a lie accepted at the JSON door does not survive gossip — it turns into a
//        DISAGREEMENT with every peer, which is worse than a rejection, not better.
//      • o1js LocalBlockchain: it DOES check, and it is the strictest of the three —
//            if (accountUpdate.update.verificationKey.isSome.toBoolean()) {
//              const isVkValid = await VerificationKey.checkValidity(...);
//              if (!isVkValid) throw Error(`The verification key hash is not consistent ...`);
//            }
//        (o1js/src/lib/mina/v1/transaction-validation.ts:314-320). ⚠ LOCAL-ONLY. A devnet
//        submission never reaches this code.
//    ⚑ CONSEQUENCE FOR THIS MODULE: the path we would actually submit over does NOT check, and the
//    only local acceptor that does is not on it. So THE BUILDER MUST.
//    `buildSetVerificationKeyUpdateChecked` refuses a key whose data does not hash to its stated
//    hash, so an inconsistent pair cannot leave this module inside a transaction.
//
// 6. WHICH VK VERIFIES A PROOF ON AN UPDATE THAT ALSO SETS ONE: the OLD one. The vk lookup
//    explicitly excludes the key being set by this same update — "only lookup _past_ vk setting, ie
//    exclude the new one we potentially set in this account_update"
//    (mina/src/lib/mina_base/zkapp_command.ml:1200-1232), and `register_verification_key` runs on
//    the ledger-loaded account ~330 lines before the set (zkapp_command_logic.ml:1228-1231 vs :1592).
//    So a first registration onto an account with no key CANNOT be proof-authorized — there is no
//    key to verify against. Signature is the only door for the first key.
//
// ─────────────────────────────────────────────────────────────────────────────────────────────────
// ⚠ NOTHING IN THIS FILE SUBMITS. It builds and validates. `scripts/foreign-vk-register-gate.ts`
// prints the command that WOULD submit and does not run it.

import { AccountUpdate, Field, Permissions, Provable, PublicKey, TokenId } from 'o1js';
import { existsSync, readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

/** The `{data, hash}` pair a Mina account stores. Identical in shape to what `.compile()` returns
 *  and to what `metatheory/fixtures/pickles-vk-derive` writes — that identity is the point. */
export type ForeignVerificationKey = { data: string; hash: Field | string | bigint };

/** Byte length of a `Side_loaded_verification_key.Stable.V2` binprot body:
 *  2 tags + 7 sigma + 1 nil + 15 coefficients + 1 nil + 6 selectors, each commitment 64 bytes. */
export const SIDE_LOADED_VK_BYTES = 2 + 7 * 64 + 1 + 15 * 64 + 1 + 6 * 64; // 1796

/** Refusals this module raises. `stage` says WHICH gate refused, so a caller can tell a malformed
 *  blob from a well-formed one whose hash lies. */
export class ForeignVkRefusal extends Error {
  constructor(
    readonly stage: 'shape' | 'base64' | 'length' | 'hash-range' | 'parse' | 'hash-mismatch',
    message: string,
    readonly cause_?: unknown,
  ) {
    super(`ForeignVkRefusal[${stage}]: ${message}`);
    this.name = 'ForeignVkRefusal';
  }
}

/** Strict base64 → bytes. Node's decoder is lenient (it skips junk), so re-encode and compare:
 *  a blob that does not round-trip is refused rather than silently truncated. */
export function decodeVkData(data: string): Uint8Array {
  if (typeof data !== 'string' || data.length === 0) {
    throw new ForeignVkRefusal('shape', 'verificationKey.data must be a non-empty base64 string');
  }
  const buf = Buffer.from(data, 'base64');
  if (buf.toString('base64') !== data) {
    throw new ForeignVkRefusal(
      'base64',
      `verificationKey.data is not canonical base64 (${data.length} chars decoded to ${buf.length} bytes and re-encoded differently)`,
    );
  }
  return new Uint8Array(buf);
}

/** Normalise the hash to a `Field`, refusing anything outside the field. `Field.from` throws on a
 *  non-canonical bigint, which is the same refusal Mina's `of_bigint` gives ("input exceeds field
 *  size"); it is caught here so the stage is named. */
export function normalizeVkHash(hash: Field | string | bigint): Field {
  try {
    return hash instanceof Field ? hash : Field.from(hash as string | bigint);
  } catch (e) {
    throw new ForeignVkRefusal('hash-range', `verificationKey.hash is not a field element: ${String(e)}`, e);
  }
}

/** SYNCHRONOUS, BINDINGS-FREE structural gate: shape, canonical base64, exact wire length, field
 *  range. Cheap enough to run on every call. ⚠ It does NOT check that the data hashes to the hash —
 *  that needs Mina's own reader, which is `assertForeignVkConsistent` below. Structural well-
 *  formedness alone is NOT sufficient; a bent commitment byte passes every check in here. */
export function assertForeignVkWellFormed(vk: ForeignVerificationKey): {
  bytes: Uint8Array;
  hash: Field;
} {
  if (vk === null || typeof vk !== 'object' || !('data' in vk) || !('hash' in vk)) {
    throw new ForeignVkRefusal('shape', 'expected an object with `data` and `hash`');
  }
  const bytes = decodeVkData(vk.data);
  if (bytes.length !== SIDE_LOADED_VK_BYTES) {
    throw new ForeignVkRefusal(
      'length',
      `expected ${SIDE_LOADED_VK_BYTES} bytes of Side_loaded_verification_key.Stable.V2, got ${bytes.length}`,
    );
  }
  return { bytes, hash: normalizeVkHash(vk.hash) };
}

// ── Mina's own reader ────────────────────────────────────────────────────────────────────────────
// `VerificationKey.checkValidity` is public but swallows the exception (`catch { return false }`,
// o1js/src/lib/proof-system/verification-key.ts:32-45). Mina's refusals are the informative part —
// `Invalid_curve_point`, `Read_error Unit_code 450`, "of_bigint: input exceeds field size" — so this
// reaches the same two internals it calls and lets the error through. o1js's package `exports` hides
// them, so resolve the package directory by walking up rather than through the export map.

const O1JS_DIR = (() => {
  let d = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const c = path.join(d, 'node_modules', 'o1js');
    if (existsSync(path.join(c, 'dist', 'node', 'index.js'))) return c;
    const up = path.dirname(d);
    if (up === d) throw new Error(`cannot locate node_modules/o1js above ${import.meta.url}`);
    d = up;
  }
})();

type Internals = {
  bindings: any;
  inCircuitVkHash: (vk: unknown) => Field;
  runAndCheckSync: (f: () => void) => void;
};
let internals: Internals | undefined;

async function o1jsInternals(): Promise<Internals> {
  if (internals !== undefined) return internals;
  const imp = (p: string) => import(pathToFileURL(path.join(O1JS_DIR, p)).href);
  // ⚑ keep the NAMESPACE, do not destructure: `Pickles` is a module-scope `let` that
  // `initializeBindings()` reassigns. A destructured copy snapshots `undefined`, and every call then
  // fails with the SAME shape of error a malformed key produces — which would make a red path pass
  // for the wrong reason.
  const bindings: any = await imp('dist/node/bindings.js');
  const { inCircuitVkHash } = (await imp('dist/node/lib/proof-system/zkprogram.js')) as any;
  const { synchronousRunners } = (await imp(
    'dist/node/lib/provable/core/provable-context.js',
  )) as any;
  await bindings.initializeBindings();
  if (typeof bindings.Pickles?.sideLoaded?.vkToCircuit !== 'function') {
    throw new Error(
      'o1js bindings did not expose Pickles.sideLoaded.vkToCircuit; refusing to run a check that cannot go green',
    );
  }
  const { runAndCheckSync } = await synchronousRunners();
  internals = { bindings, inCircuitVkHash, runAndCheckSync };
  return internals;
}

export type VkConsistency =
  | { ok: true; recomputedHash: Field }
  | { ok: false; stage: 'parse' | 'hash-mismatch'; message: string; recomputedHash?: Field };

/**
 * Run Mina's OWN binprot reader over `data` and compare the in-circuit digest to the stated `hash`.
 * This is exactly what `VerificationKey.checkValidity` does, and exactly what o1js's LocalBlockchain
 * runs on every VK-setting account update (transaction-validation.ts:314-320) — but it REPORTS the
 * refusal instead of collapsing it to `false`.
 */
export async function checkForeignVkConsistency(
  vk: ForeignVerificationKey,
): Promise<VkConsistency> {
  const { hash } = assertForeignVkWellFormed(vk);
  const { bindings, inCircuitVkHash, runAndCheckSync } = await o1jsInternals();
  let recomputed: bigint | undefined;
  try {
    runAndCheckSync(() => {
      const circuitVk = bindings.Pickles.sideLoaded.vkToCircuit(() => vk.data);
      // ⚑ `inCircuitVkHash` returns a CIRCUIT VARIABLE, not a constant — `.toBigInt()` on it outside
      // the checked computation throws "variables only exist inside checked computations". Read the
      // witness INSIDE, and inside `asProver`. (Same shape as scripts/mina-vk-parse-gate.mjs:97-107.)
      const h = inCircuitVkHash(circuitVk);
      Provable.asProver(() => {
        recomputed = h.toBigInt();
      });
    });
  } catch (e) {
    return { ok: false, stage: 'parse', message: String((e as Error)?.message ?? e) };
  }
  if (recomputed === undefined) {
    return { ok: false, stage: 'parse', message: 'reader produced no digest' };
  }
  // Compare OUT of circuit: an `assertEquals` inside `runAndCheckSync` would surface as a constraint
  // failure and blur the two refusals we most want to tell apart — a blob Mina cannot READ, versus a
  // blob Mina reads fine whose stated hash is a lie.
  if (recomputed !== hash.toBigInt()) {
    return {
      ok: false,
      stage: 'hash-mismatch',
      message: `data hashes to ${recomputed.toString()} but the key states ${hash.toString()}`,
      recomputedHash: Field.from(recomputed),
    };
  }
  return { ok: true, recomputedHash: Field.from(recomputed) };
}

/** `checkForeignVkConsistency`, as a refusal. */
export async function assertForeignVkConsistent(vk: ForeignVerificationKey): Promise<Field> {
  const r = await checkForeignVkConsistency(vk);
  if (!r.ok) throw new ForeignVkRefusal(r.stage, r.message);
  return r.recomputedHash;
}

// ── the builder ──────────────────────────────────────────────────────────────────────────────────

export type SetVerificationKeyArgs = {
  /** The account whose `zkapp.verification_key` is being set. */
  address: PublicKey;
  /** The key to register. Provenance is not inspected and cannot be. */
  verificationKey: ForeignVerificationKey;
  /** Defaults to the default token. */
  tokenId?: Field;
  /**
   * Permissions to set in the SAME account update. Optional and OFF by default: setting permissions
   * needs the `setPermissions` authorization on top of `setVerificationKey`, so folding it in
   * silently would make the update fail for a reason the caller did not ask for.
   * ⚠ If you pass `Permissions.default()` you are also setting `editState: proof` and `send: proof`,
   * which makes the account unusable by signature afterwards. Say what you mean.
   */
  permissions?: Permissions;
  /**
   * Authorization. `'signature'` (the default) is the only one that can place the FIRST key on an
   * account — see (6) in the header: the proof on a VK-setting update is verified against the OLD
   * key, and a fresh account has none. `'none'` leaves the update unauthorized for a caller that
   * intends to attach a proof itself.
   */
  authorization?: 'signature' | 'none';
  /** Shows up in `tx.toPretty()`. */
  label?: string;
};

/**
 * THE BUILDER. Given a `{data, hash}` from anywhere, produce the `AccountUpdate` that registers it.
 *
 * ⚑ PROVENANCE-BLIND BY CONSTRUCTION. There is no `.compile()`, no `SmartContract`, no `ZkProgram`
 * and no cached `_verificationKey` anywhere in this function. It reads two fields off a plain object.
 * A key from `SmartContract.compile()` and a key from `pickles-vk-derive` take identical paths.
 *
 * ⚑ AND IT IS NOT A PASS-THROUGH. Structural well-formedness is enforced here, synchronously. The
 * data↔hash tie needs Mina's reader and so is async — use {@link buildSetVerificationKeyUpdateChecked}
 * unless you have already run {@link assertForeignVkConsistent} yourself. The GraphQL ingest path
 * does not check it for you (see (5) in the header).
 *
 * Must be called inside `Mina.transaction(...)`; `AccountUpdate.create` pushes onto the current
 * transaction layout (o1js account-update.ts:1006-1018) and is a no-op push outside one.
 */
export function buildSetVerificationKeyUpdate(args: SetVerificationKeyArgs): AccountUpdate {
  const { hash } = assertForeignVkWellFormed(args.verificationKey);
  const data = args.verificationKey.data;

  const au = AccountUpdate.create(args.address, args.tokenId ?? TokenId.default);
  au.label = args.label ?? 'ForeignVerificationKey.buildSetVerificationKeyUpdate()';

  // The one line that does the work. `account.verificationKey` is `updateSubclass(au,
  // 'verificationKey', identity)`, i.e. `isSome := true; value := {data, hash}` on
  // `body.update.verificationKey` (o1js precondition.ts:203, 216-227). Written through the public
  // setter rather than poking the body, so the layout stays the one o1js serializes.
  au.account.verificationKey.set({ data, hash });

  if (args.permissions !== undefined) au.account.permissions.set(args.permissions);

  if ((args.authorization ?? 'signature') === 'signature') au.requireSignature();

  return au;
}

/** {@link buildSetVerificationKeyUpdate} with the data↔hash tie checked against Mina's own reader
 *  first. This is the one to use: it is the gate the GraphQL path does not give you. */
export async function buildSetVerificationKeyUpdateChecked(
  args: SetVerificationKeyArgs,
): Promise<AccountUpdate> {
  await assertForeignVkConsistent(args.verificationKey);
  return buildSetVerificationKeyUpdate(args);
}

// ── reading a key off disk / off an account ──────────────────────────────────────────────────────

/** Read a `{data, hash, ...}` JSON — the shape `pickles-vk-derive` writes and the shape o1js's
 *  `--reference-dump` writes. Extra keys are ignored; the two that matter must be present. */
export function loadForeignVk(file: string): ForeignVerificationKey {
  const j = JSON.parse(readFileSync(file, 'utf8'));
  if (typeof j?.data !== 'string' || (typeof j?.hash !== 'string' && typeof j?.hash !== 'number')) {
    throw new ForeignVkRefusal('shape', `${file} has no {data: string, hash: string} pair`);
  }
  return { data: j.data, hash: String(j.hash) };
}

/** What the resulting account update actually carries, for reporting and for asserting that two
 *  updates built from different provenances are structurally identical. */
export function describeVkUpdate(au: AccountUpdate): {
  isSome: boolean;
  hash: string;
  dataBytes: number;
  dataSha256: string;
  fieldsContributedByData: number;
} {
  const v = au.body.update.verificationKey;
  const bytes = decodeVkData(v.value.data);
  return {
    isSome: v.isSome.toBoolean(),
    hash: v.value.hash.toString(),
    dataBytes: bytes.length,
    dataSha256: createHash('sha256').update(bytes).digest('hex'),
    // See (2) in the header: the layout primitive `string` is `emptyType`, so this is 0 and the
    // signature does not bind the key material. Reported rather than assumed.
    fieldsContributedByData: 0,
  };
}
