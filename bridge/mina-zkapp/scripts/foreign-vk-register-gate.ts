// FOREIGN-VK REGISTRATION GATE — can we build, and does Mina's own machinery accept, an account
// update that registers a verification key we DERIVED OURSELVES?
//
// THE GAP THIS CLOSES. Every VK-bearing path in this tree takes its key from o1js `.compile()` and
// hands it to `zkapp.deploy()`. The side-loaded `DreggHeadAnchor.advanceHead(terminal, vk, ...)`
// (src/DreggHeadAnchor.ts:629-634) CONSUMES a key as a method argument; it registers nothing. So
// there was no path from `metatheory/fixtures/pickles-vk-derive`'s output — a real
// `Side_loaded_verification_key` derived from Lean-emitted `KimchiWrapMain` gates — onto an account.
// `src/ForeignVerificationKey.ts` is that path, and this is its gate.
//
// WHAT IT MEASURES, in order, GREEN-OR-BUST. Every leg is anchored: a refusal is only counted after
// the corresponding acceptance has been observed, so no red path passes vacuously.
//
//   A. SOURCE — the mechanism, restated from the files, with the two claims that are checkable at
//      runtime actually checked (the `string` layout primitive contributes 0 fields; a fresh
//      account's `setVerificationKey` permission is `Signature`).
//   B. PROVENANCE INDIFFERENCE — build the update from a DERIVED key and from a `.compile()` key and
//      show the two updates are byte-identical apart from the key itself.
//   C. TRANSACTION — construct it, `toJSON()` it, round-trip it through o1js's own
//      `ZkappCommand.fromJSON`, and confirm the VK survives the round trip.
//   D. THE GATE — apply it on `Mina.LocalBlockchain`, whose `ledger.applyJsonTransaction` IS Mina's
//      OCaml transaction logic compiled to JS by js_of_ocaml, and read the key back OFF THE ACCOUNT.
//   E. RED — one bent byte, at three separate layers, with the literal refusal printed.
//   F. SUBMIT — print the devnet command that WOULD register this key. ⚠ NEVER RUN HERE.
//
// ⚠ NOTHING HERE DEPLOYS, REGISTERS OR SUBMITS TO ANY NETWORK. The only chain touched is an
// in-process LocalBlockchain. Step F prints a command and exits.
//
// USAGE
//   npx ts-node --transpile-only scripts/foreign-vk-register-gate.ts [--vk <derived.json> ...]
//   ... --compile          also do a LIVE o1js `.compile()` for the `.compile()`-provenance leg
//                          (default: the recorded o1js-emitted keys in pickles-vk-derive/fixtures)
//
// Defaults for --vk: the three keys `metatheory/fixtures/pickles-vk-derive` writes, if a run has
// left them somewhere; otherwise pass them explicitly. Missing input is RED, never a skip.

import {
  AccountUpdate,
  Field,
  Mina,
  Permissions,
  PrivateKey,
  PublicKey,
  Types,
  UInt64,
} from 'o1js';
import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  ForeignVkRefusal,
  SIDE_LOADED_VK_BYTES,
  assertForeignVkWellFormed,
  buildSetVerificationKeyUpdate,
  buildSetVerificationKeyUpdateChecked,
  checkForeignVkConsistency,
  decodeVkData,
  describeVkUpdate,
  loadForeignVk,
  type ForeignVerificationKey,
} from '../src/ForeignVerificationKey.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, '..', '..', '..');

let fails = 0;
const step = (s: string) => console.log(`\n── ${s} ${'─'.repeat(Math.max(0, 78 - s.length))}`);
const note = (s: string) => console.log(`   ${s}`);
const green = (s: string) => console.log(`   GREEN: ${s}`);
const red = (s: string) => {
  console.log(`   RED:   ${s}`);
  fails++;
};
function must(cond: boolean, ok: string, bad: string) {
  if (cond) green(ok);
  else red(bad);
}

// ── inputs ───────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const vkPaths: string[] = [];
let liveCompile = false;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '--vk') vkPaths.push(argv[++i]!);
  else if (argv[i] === '--compile') liveCompile = true;
  else if (argv[i] === '-h' || argv[i] === '--help') {
    console.log(readFileSync(fileURLToPath(import.meta.url), 'utf8').split('\n').slice(0, 36).join('\n'));
    process.exit(0);
  } else {
    console.error(`unknown argument ${argv[i]}`);
    process.exit(2);
  }
}
if (vkPaths.length === 0) {
  for (const d of [process.env.DREGG_VK_DIR, path.join(REPO, 'metatheory/fixtures/pickles-vk-derive/out')]) {
    if (!d) continue;
    for (const n of ['vk-wrapmain-w3_branch.json', 'vk-wrapmain-w4_bind.json', 'vk-wrapmain-w4_bind-perturbed.json']) {
      const p = path.join(d, n);
      if (existsSync(p)) vkPaths.push(p);
    }
    if (vkPaths.length > 0) break;
  }
}
if (vkPaths.length === 0) {
  console.error(
    'RED: no derived verification keys given.\n' +
      '     Produce them first:\n' +
      `       cargo run --release --manifest-path ${REPO}/metatheory/fixtures/pickles-vk-derive/Cargo.toml -- <outdir> --log2-domain 14\n` +
      '     then pass --vk <outdir>/vk-wrapmain-w4_bind.json (or set DREGG_VK_DIR=<outdir>).\n' +
      '     ⚠ A missing input is RED, never a skip: a gate that quietly stops running is not a gate.',
  );
  process.exit(1);
}

// The key o1js ITSELF emitted, for the provenance-indifference leg. `compileMs` in this fixture is
// the tell: these came out of `.compile()`. A live compile is available behind --compile.
const REF_VKS = path.join(REPO, 'metatheory/fixtures/pickles-vk-derive/fixtures/o1js-reference-vks.json');

async function main() {
  console.log('FOREIGN-VK REGISTRATION GATE — a DERIVED verification key onto a Mina account');
  console.log(`   derived keys : ${vkPaths.length}`);
  vkPaths.forEach((p) => console.log(`                  ${p}`));

  // ═══ A. SOURCE ═════════════════════════════════════════════════════════════════════════════════
  step('A. THE MECHANISM, AT SOURCE');
  note('Update.verification_key : Verification_key_wire.t Set_or_keep.t');
  note('                          mina/src/lib/mina_base/account_update.ml:695-696');
  note('Verification_key_wire.t = (Side_loaded_verification_key.t, F.t) With_hash.t');
  note('                          mina/src/lib/mina_base/verification_key_wire.ml:22-23');
  note('o1js layout: verificationKey = flaggedOption { data: string, hash: Field }');
  note('                          o1js/src/bindings/mina-transaction/gen/v1/js-layout.ts:809-816');
  note('permission  : set_verification_key : Auth_required.t * Txn_version.t   (a PAIR)');
  note('                          mina/src/lib/mina_base/permissions.ml:367, :399-403');
  note('checked at  : Update_not_permitted_verification_key,');
  note('              Bool.(Set_or_keep.is_keep vk ||| has_permission)');
  note('                          mina/src/lib/transaction_logic/zkapp_command_logic.ml:1583-1586');
  note('fresh acct  : user_default sets it to (Signature, Txn_version.current)');
  note('                          mina/src/lib/mina_base/permissions.ml:580-594');
  note('  ⇒ A SIGNATURE IS ENOUGH. No proof is required to place the first key, and could not be:');
  note('    the vk that verifies a proof on a VK-setting update is the OLD one — "only lookup');
  note('    _past_ vk setting, ie exclude the new one we potentially set in this account_update"');
  note('                          mina/src/lib/mina_base/zkapp_command.ml:1200-1232');

  // The two source claims that are checkable HERE rather than quoted.
  const auA = AccountUpdate.default(PublicKey.empty());
  const auB = AccountUpdate.default(PublicKey.empty());
  auA.body.update.verificationKey.isSome = auB.body.update.verificationKey.isSome;
  auA.body.update.verificationKey.value.data = 'A'.repeat(64);
  auB.body.update.verificationKey.value.data = 'B'.repeat(2396);
  const fA = Types.AccountUpdate.toFields(auA).map(String).join(',');
  const fB = Types.AccountUpdate.toFields(auB).map(String).join(',');
  const nFields = Types.AccountUpdate.toFields(auA).length;
  must(
    fA === fB,
    `verificationKey.data contributes 0 fields to the commitment — two updates differing ONLY in ` +
      `data (64 vs 2396 chars) serialise to the SAME ${nFields} fields. ` +
      `The layout primitive 'string' is emptyType (o1js/src/bindings/lib/generic.ts:67-68,120-129); ` +
      `the OCaml maps through With_hash.hash (account_update.ml:864-866). ` +
      `⚠ A SIGNATURE DOES NOT BIND THE KEY MATERIAL, only its hash.`,
    'verificationKey.data DID change the field encoding — the source description above is wrong',
  );
  const pdef = Permissions.default();
  const pinit = Permissions.initial();
  must(
    Types.AuthRequired.toJSON(pdef.setVerificationKey.auth) === 'Signature' &&
      Types.AuthRequired.toJSON(pinit.setVerificationKey.auth) === 'Signature',
    `o1js Permissions.default()/initial() both give setVerificationKey.auth = Signature ` +
      `(txnVersion ${pdef.setVerificationKey.txnVersion.toString()}) — matches user_default`,
    'o1js default setVerificationKey permission is NOT Signature — the brief above is wrong',
  );

  // ═══ load the keys ═════════════════════════════════════════════════════════════════════════════
  step('B. PROVENANCE INDIFFERENCE — a DERIVED key and a .compile() key take the same path');

  const derived: { name: string; vk: ForeignVerificationKey }[] = vkPaths.map((p) => ({
    name: path.basename(p),
    vk: loadForeignVk(p),
  }));

  const compiled: { name: string; vk: ForeignVerificationKey }[] = [];
  if (!existsSync(REF_VKS)) {
    red(`${REF_VKS} missing — cannot run the .compile()-provenance leg`);
  } else {
    const j = JSON.parse(readFileSync(REF_VKS, 'utf8'));
    for (const k of ['refA', 'refB']) {
      if (j[k]?.data) {
        compiled.push({ name: `o1js-${k} (compileMs=${j[k].compileMs ?? '?'})`, vk: { data: j[k].data, hash: String(j[k].hash) } });
      }
    }
  }
  if (liveCompile) {
    const t0 = Date.now();
    const { ZkProgram } = await import('o1js');
    const P = ZkProgram({
      name: 'foreign-vk-gate-live-compile',
      publicInput: Field,
      methods: { id: { privateInputs: [], async method(x: Field) { x.assertEquals(x); } } },
    });
    const { verificationKey } = await P.compile();
    compiled.push({ name: `LIVE .compile() in this run (${((Date.now() - t0) / 1000).toFixed(1)}s)`, vk: { data: verificationKey.data, hash: verificationKey.hash } });
    green(`live o1js .compile() produced a key, hash ${verificationKey.hash.toString().slice(0, 24)}…`);
  }
  if (compiled.length === 0) red('no .compile()-provenance key available — the indifference leg cannot run');

  // Every key, both provenances, through the SAME builder and the SAME consistency check.
  const target = PrivateKey.random();
  const targetPk = target.toPublicKey();
  const rows: { name: string; provenance: string; bytes: number; hash: string; sha: string }[] = [];
  for (const [provenance, set] of [['DERIVED', derived], ['COMPILED', compiled]] as const) {
    for (const { name, vk } of set) {
      const { bytes } = assertForeignVkWellFormed(vk);
      const c = await checkForeignVkConsistency(vk);
      if (!c.ok) {
        red(`${provenance} ${name}: Mina's reader REFUSED a key that should be good — [${c.stage}] ${c.message}`);
        continue;
      }
      // The builder needs a transaction context to attach to; a bare Mina.transaction on a local
      // chain is the cheapest one. Built here purely to inspect the update it produces.
      const au = buildSetVerificationKeyUpdate({ address: targetPk, verificationKey: vk, authorization: 'none' });
      const d = describeVkUpdate(au);
      rows.push({ name, provenance, bytes: bytes.length, hash: d.hash, sha: d.dataSha256.slice(0, 16) });
      must(
        d.isSome && d.hash === c.recomputedHash.toString() && d.dataBytes === bytes.length,
        `${provenance.padEnd(8)} ${name.padEnd(46)} → update carries ${d.dataBytes}B, hash ${d.hash.slice(0, 20)}…`,
        `${provenance} ${name}: the update does not carry the key it was given`,
      );
    }
  }
  const derivedRows = rows.filter((r) => r.provenance === 'DERIVED');
  const compiledRows = rows.filter((r) => r.provenance === 'COMPILED');
  must(
    derivedRows.length > 0 && compiledRows.length > 0,
    `the builder accepted ${derivedRows.length} DERIVED and ${compiledRows.length} COMPILED keys — ` +
      `it has no branch on provenance and cannot: it reads {data, hash} off a plain object`,
    'one provenance did not make it through the builder',
  );
  must(
    new Set(rows.map((r) => r.hash)).size === rows.length,
    `all ${rows.length} keys have DISTINCT hashes — the updates differ in the key, not by accident`,
    'two keys collided on hash; the indifference result would be vacuous',
  );
  // ⚠ A DRAFT OF THIS GATE SAID the two provenances produce different-length wire objects. They do
  // not: `Side_loaded_verification_key.Stable.V2` is a FIXED 1796 bytes either way (2396 base64
  // chars — the draft had confused chars for bytes). Measured and asserted rather than narrated.
  const dLens = new Set(derivedRows.map((r) => r.bytes));
  const cLens = new Set(compiledRows.map((r) => r.bytes));
  must(
    dLens.size === 1 && cLens.size === 1 && [...dLens][0] === SIDE_LOADED_VK_BYTES && [...cLens][0] === SIDE_LOADED_VK_BYTES,
    `BOTH provenances are exactly ${SIDE_LOADED_VK_BYTES} bytes on the wire — derived ${[...dLens].join(',')} B, ` +
      `o1js .compile() ${[...cLens].join(',')} B. The objects are not merely both acceptable; they are the ` +
      `SAME FIXED-SIZE OBJECT, so there is nothing for the builder to branch on even if it wanted to.`,
    `wire sizes differ or miss the pin: derived {${[...dLens].join(',')}}, compiled {${[...cLens].join(',')}}, ` +
      `expected ${SIDE_LOADED_VK_BYTES}`,
  );

  // The head key used for everything downstream.
  const headline = derived.find((d) => !d.name.includes('perturbed')) ?? derived[derived.length - 1]!;
  const vk = headline.vk;
  note(`headline derived key: ${headline.name}`);

  // ═══ C. TRANSACTION ════════════════════════════════════════════════════════════════════════════
  step('C. TRANSACTION — construct, serialise, round-trip through o1js own ZkappCommand');

  const Local = await Mina.LocalBlockchain({ proofsEnabled: false, enforceTransactionLimits: true });
  Mina.setActiveInstance(Local);
  const [payer, holder] = Local.testAccounts;
  if (payer === undefined || holder === undefined) throw new Error('LocalBlockchain gave no test accounts');

  // What permission does an existing LocalBlockchain account actually carry? Measured, not assumed.
  const holderAccount = Mina.getAccount(holder);
  const holderPerm = Types.AuthRequired.toJSON(holderAccount.permissions.setVerificationKey.auth);
  note(`holder account ${holder.toBase58().slice(0, 14)}… setVerificationKey.auth = ${holderPerm}, ` +
    `txnVersion ${holderAccount.permissions.setVerificationKey.txnVersion.toString()}, ` +
    `existing zkapp vk = ${holderAccount.zkapp?.verificationKey?.hash?.toString() ?? 'NONE'}`);
  must(
    holderPerm === 'Signature',
    `the target account permits a SIGNATURE-authorized VK set — no proof needed, matching user_default`,
    `target account permits '${holderPerm}' for setVerificationKey; the signature path below cannot apply`,
  );

  const tx = await Mina.transaction({ sender: payer, fee: UInt64.from(100_000_000) }, async () => {
    await buildSetVerificationKeyUpdateChecked({
      address: holder,
      verificationKey: vk,
      label: `register derived VK ${headline.name}`,
    });
  });

  const json = tx.toJSON();
  const parsed = JSON.parse(json);
  const vkInJson = parsed.accountUpdates[0]?.body?.update?.verificationKey;
  must(
    vkInJson?.data === vk.data && String(vkInJson?.hash) === String(vk.hash),
    `tx.toJSON() carries the key verbatim: data ${String(vkInJson?.data).length} chars, hash ${String(vkInJson?.hash).slice(0, 20)}…`,
    `tx.toJSON() did not carry the key: ${JSON.stringify(vkInJson)?.slice(0, 200)}`,
  );
  // Round-trip through Mina's own decoder, the same call `Transaction.fromJSON` makes.
  const reencoded = JSON.stringify(Types.ZkappCommand.toJSON(Types.ZkappCommand.fromJSON(parsed)));
  must(
    reencoded === JSON.stringify(parsed),
    `ZkappCommand.fromJSON → toJSON is BYTE-IDENTICAL (${reencoded.length} chars) — the update is a ` +
      `well-formed zkApp command by o1js own codec, not just a shape we assembled`,
    `round-trip DIFFERED; the constructed command is not canonical`,
  );

  // ═══ D. THE GATE ═══════════════════════════════════════════════════════════════════════════════
  step("D. THE GATE — apply it on Mina own transaction logic and read the key back off the account");
  note('LocalBlockchain.sendTransaction runs TWO independent acceptors:');
  note('  (i)  verifyAccountUpdate — permissions + signature + VerificationKey.checkValidity');
  note('       o1js/src/lib/mina/v1/transaction-validation.ts:314-320');
  note('  (ii) ledger.applyJsonTransaction — MINA OWN OCAML TRANSACTION LOGIC, compiled to JS');
  note('       o1js/src/lib/mina/v1/local-blockchain.ts:182-186 -> bindings.js:31 ->');
  note('       dist/node/bindings/compiled/node_bindings/o1js_node.bc.cjs ("Generated by');
  note('       js_of_ocaml 4.0.0"). NOT a JS reimplementation. Checked below, not asserted.');

  // PROVENANCE OF THE ACCEPTOR. A JS reimplementation of the transaction logic would be a much
  // weaker witness than Mina's own, so establish which one we are talking to: the bundle must carry
  // Mina's own failure constants (mina/src/lib/mina_base/transaction_status.ml:31) and the
  // js_of_ocaml banner. A grep, but of the ARTIFACT THAT RUNS.
  {
    const bc = path.join(
      HERE, '..', 'node_modules/o1js/dist/node/bindings/compiled/node_bindings/o1js_node.bc.cjs',
    );
    const head = existsSync(bc) ? readFileSync(bc, 'utf8').slice(0, 200) : '';
    const body = existsSync(bc) ? readFileSync(bc, 'utf8') : '';
    must(
      head.includes('js_of_ocaml') && body.includes('Update_not_permitted_verification_key'),
      `the acceptor is Mina OWN OCaml: o1js_node.bc.cjs says "${head.split('\n')[0]!.replace('// ', '')}" ` +
        `and carries the failure constant Update_not_permitted_verification_key`,
      'could not establish that the LocalBlockchain acceptor is Mina own OCaml transaction logic',
    );
  }

  tx.sign([payer.key, holder.key]);
  let applied = false;
  try {
    const pending = await tx.send();
    applied = pending.status !== 'rejected';
    if (!applied) red(`transaction REJECTED: ${JSON.stringify((pending as any).errors)?.slice(0, 400)}`);
    else green(`transaction ACCEPTED by both acceptors (status=${pending.status})`);
  } catch (e) {
    red(`transaction threw: ${String((e as Error).message).slice(0, 600)}`);
  }

  if (applied) {
    const after = Mina.getAccount(holder);
    const onChain = after.zkapp?.verificationKey;
    must(
      onChain !== undefined,
      `the account now HAS a verification key`,
      `the account has NO verification key after an accepted transaction`,
    );
    if (onChain !== undefined) {
      must(
        onChain.hash.toString() === String(vk.hash),
        `on-account hash === the DERIVED hash: ${onChain.hash.toString()}`,
        `on-account hash ${onChain.hash.toString()} !== derived ${String(vk.hash)}`,
      );
      must(
        onChain.data === vk.data,
        `on-account data === the DERIVED base64, all ${onChain.data.length} chars ` +
          `(${decodeVkData(onChain.data).length} bytes of Side_loaded_verification_key.Stable.V2)`,
        `on-account data differs from what we submitted`,
      );
      must(
        decodeVkData(onChain.data).length === SIDE_LOADED_VK_BYTES,
        `the registered object is ${SIDE_LOADED_VK_BYTES} bytes — the wire shape pinned by pickles-vk-derive`,
        `registered object is ${decodeVkData(onChain.data).length} bytes, not ${SIDE_LOADED_VK_BYTES}`,
      );
      const c = await checkForeignVkConsistency({ data: onChain.data, hash: onChain.hash });
      must(
        c.ok,
        `Mina own reader re-parses the key OFF THE ACCOUNT and its digest matches the stored hash`,
        `the key on the account does not survive re-parsing: ${!c.ok ? c.message : ''}`,
      );
    }
  }

  // ═══ E. RED ════════════════════════════════════════════════════════════════════════════════════
  step('E. RED — one bent byte, refused at three separate layers');
  note('Anchored: every refusal below is on a mutation of the SAME key that was just ACCEPTED above,');
  note('so none of them can be passing for an unrelated reason.');

  const raw = Buffer.from(decodeVkData(vk.data));

  // (1) a bent COMMITMENT byte — takes the point off the Pallas curve. Mina's reader refuses.
  const bentCurve = Buffer.from(raw);
  bentCurve[2] = (bentCurve[2]! + 1) & 0xff; // sigma_comm[0].x
  const vkBentCurve: ForeignVerificationKey = { data: bentCurve.toString('base64'), hash: vk.hash };
  {
    const c = await checkForeignVkConsistency(vkBentCurve);
    must(
      !c.ok,
      `bent sigma_comm[0].x (byte 2, +1) → REFUSED at stage '${!c.ok ? c.stage : ''}': ` +
        `${!c.ok ? c.message.split('\n')[0]!.slice(0, 160) : ''}`,
      `a BENT COMMITMENT was ACCEPTED — the check proves nothing`,
    );
    // ...and structurally it is indistinguishable, which is why the structural gate is not enough.
    let structurallyFine = false;
    try {
      assertForeignVkWellFormed(vkBentCurve);
      structurallyFine = true;
    } catch {
      /* ignore */
    }
    must(
      structurallyFine,
      `⚠ and that same bent key PASSES every structural check (canonical base64, ${SIDE_LOADED_VK_BYTES} bytes, ` +
        `in-range hash) — only Mina own reader catches it. A length/base64 gate is NOT a VK gate.`,
      `the bent key failed the structural gate too, so this leg does not isolate the reader`,
    );
  }

  // (2) a bent TAG byte — still parses, but the digest moves. This separates 'parse' from
  //     'hash-mismatch' and shows the hash comparison is load-bearing on its own.
  const bentTag = Buffer.from(raw);
  bentTag[0] = raw[0] === 0 ? 1 : 0; // max_proofs_verified: N1 <-> N0
  const vkBentTag: ForeignVerificationKey = { data: bentTag.toString('base64'), hash: vk.hash };
  {
    const c = await checkForeignVkConsistency(vkBentTag);
    must(
      !c.ok && c.stage === 'hash-mismatch',
      `bent max_proofs_verified tag (byte 0, ${raw[0]}→${bentTag[0]}) PARSES but → REFUSED at stage ` +
        `'${!c.ok ? c.stage : 'ACCEPTED'}': ${!c.ok ? c.message.slice(0, 150) : ''}`,
      `a bent tag was ${c.ok ? 'ACCEPTED' : `refused at the wrong stage (${(c as any).stage})`}`,
    );
  }

  // (3) a bent HASH with intact data — the complement.
  const vkBentHash: ForeignVerificationKey = { data: vk.data, hash: (Field.from(String(vk.hash)).toBigInt() + 1n).toString() };
  {
    const c = await checkForeignVkConsistency(vkBentHash);
    must(
      !c.ok && c.stage === 'hash-mismatch',
      `hash+1 with intact data → REFUSED at stage '${!c.ok ? c.stage : 'ACCEPTED'}'`,
      `a lying hash was accepted`,
    );
  }

  // (4) THE BUILDER refuses — the checked builder will not emit an update for a bent key.
  {
    let refusal: unknown;
    try {
      await Mina.transaction({ sender: payer, fee: UInt64.from(100_000_000) }, async () => {
        await buildSetVerificationKeyUpdateChecked({ address: holder, verificationKey: vkBentCurve });
      });
    } catch (e) {
      refusal = e;
    }
    must(
      refusal instanceof ForeignVkRefusal,
      `the BUILDER refuses to construct the update: ${refusal instanceof Error ? refusal.message.slice(0, 150) : String(refusal)}`,
      `the builder CONSTRUCTED an update for a bent key — a builder that accepts anything is not a builder`,
    );
  }

  // (5) O1JS ITSELF refuses at send, even when the builder's check is bypassed. This is the leg that
  //     shows the refusal is not our own invention: transaction-validation.ts:314-320.
  {
    const bentTx = await Mina.transaction({ sender: payer, fee: UInt64.from(100_000_000) }, async () => {
      buildSetVerificationKeyUpdate({ address: holder, verificationKey: vkBentCurve }); // UNCHECKED
    });
    bentTx.sign([payer.key, holder.key]);
    let msg = '';
    let sent = false;
    try {
      const p = await bentTx.send();
      sent = p.status !== 'rejected';
      msg = JSON.stringify((p as any).errors ?? p.status);
    } catch (e) {
      msg = String((e as Error).message);
    }
    must(
      !sent,
      `o1js own send() REFUSES the bent key even with our check bypassed: ${msg.split('\n')[0]!.slice(0, 190)}`,
      `o1js ACCEPTED a bent key at send() — the LocalBlockchain leg above proves nothing about validity`,
    );
  }

  // (6) STRUCTURAL refusals — length and base64, each anchored on the good key passing.
  for (const [label, mutate] of [
    ['truncated by 1 byte', (b: Buffer) => b.subarray(0, b.length - 1).toString('base64')],
    ['non-canonical base64 (trailing junk)', (b: Buffer) => b.toString('base64') + 'A'],
  ] as const) {
    let stage = '';
    try {
      assertForeignVkWellFormed({ data: mutate(Buffer.from(raw)), hash: vk.hash });
    } catch (e) {
      stage = e instanceof ForeignVkRefusal ? e.stage : 'other';
    }
    must(stage !== '', `${label} → REFUSED at stage '${stage}'`, `${label} was ACCEPTED`);
  }

  // ═══ E\'. WHERE THE REFUSAL ACTUALLY LIVES ══════════════════════════════════════════════════════
  step("E\'. WHICH LAYER REFUSES — Mina\'s OCaml alone, with o1js\'s JS acceptor bypassed");
  note('Step E(5) showed o1js REFUSES a bent key at send(). That refusal came from the JS acceptor');
  note('(transaction-validation.ts:314-320), which a real devnet submission NEVER TOUCHES — GraphQL');
  note('goes straight to Zkapp_command.of_json. This leg calls ledger.applyJsonTransaction DIRECTLY,');
  note('bypassing the JS acceptor, and asks Mina alone. Three mutations, chosen to SEPARATE the two');
  note('things that could be doing the refusing:');
  note('  (a) bent CURVE POINT  — cannot be DESERIALISED at all');
  note('  (b) bent TAG          — deserialises fine, but the digest of the data MOVES');
  note('  (c) lying HASH        — data intact, stated hash off by one');
  note('If Mina validated data↔hash, (b) and (c) would both be refused.');
  {
    const cases: { label: string; vk: ForeignVerificationKey; expectAccepted: boolean; why: string }[] = [
      {
        label: '(a) bent sigma_comm[0].x',
        vk: vkBentCurve,
        expectAccepted: false,
        why: 'Side_loaded_verification_key.of_base64 deserialises the commitments as Pallas points and ' +
          'rejects an off-curve one (mina/src/lib/pickles/side_loaded_verification_key.ml:291-292)',
      },
      {
        label: '(b) bent max_proofs_verified tag',
        vk: vkBentTag,
        expectAccepted: true,
        why: 'it DESERIALISES, and nothing on the JSON path recomputes digest_vk — ' +
          'fields_derivers_zkapps.ml:555-574 reads `data` and `hash` as two INDEPENDENT fields',
      },
      {
        label: '(c) hash+1, data intact',
        vk: vkBentHash,
        expectAccepted: true,
        why: 'same reason; and the hash is the only part in the commitment ' +
          '(account_update.ml:864-866), so the signature is valid over it',
      },
    ];
    let idx = 2;
    for (const c of cases) {
      const acct = Local.testAccounts[idx++];
      if (acct === undefined) {
        red(`LocalBlockchain ran out of test accounts at index ${idx - 1}`);
        continue;
      }
      const t = await Mina.transaction({ sender: payer, fee: UInt64.from(100_000_000) }, async () => {
        buildSetVerificationKeyUpdate({ address: acct, verificationKey: c.vk }); // UNCHECKED, on purpose
      });
      t.sign([payer.key, acct.key]);
      let accepted = false;
      let thrown = '';
      try {
        (Local as any).applyJsonTransaction(t.toJSON());
        accepted = true;
      } catch (e) {
        // ⚑ js_of_ocaml exceptions are ARRAYS, not Errors — `.message` is undefined on them and an
        // earlier draft of this gate reported the refusal as "undefined". String() is the readable form.
        thrown = String(e).slice(0, 260);
      }
      must(
        accepted === c.expectAccepted,
        `${c.label.padEnd(32)} → Mina OCaml ${accepted ? 'ACCEPTED' : 'REFUSED'} (as predicted)` +
          (accepted ? '' : `\n          ${thrown}`),
        `${c.label} → Mina OCaml ${accepted ? 'ACCEPTED' : 'REFUSED'} but the source reading predicts ` +
          `${c.expectAccepted ? 'ACCEPTED' : 'REFUSED'} (${c.why}) — correct src/ForeignVerificationKey.ts (5) before citing it`,
      );
      if (accepted) {
        const stored = Mina.getAccount(acct).zkapp?.verificationKey;
        const consistent = stored ? await checkForeignVkConsistency({ data: stored.data, hash: stored.hash }) : undefined;
        note(`     stored on account: ${stored === undefined ? 'NOTHING' : `${decodeVkData(stored.data).length}B, hash ${stored.hash.toString().slice(0, 22)}…`}`);
        note(`     re-parse of the STORED pair: ${consistent === undefined ? 'n/a' : consistent.ok ? 'CONSISTENT' : `INCONSISTENT [${consistent.stage}]`}`);
        must(
          consistent !== undefined && !consistent.ok,
          `⚠ Mina stored a pair whose data does NOT hash to its hash. THE JSON/GraphQL INGEST PATH ` +
            `PERFORMS NO data↔hash VALIDATION. ${c.why}.`,
          `expected the stored pair to be inconsistent and it is not — this case does not demonstrate the gap`,
        );
      }
    }
    note('');
    note('⚑ THE CONCLUSION, AND IT IS THE REASON THE BUILDER CHECKS:');
    note('  Mina refuses a key it cannot DESERIALISE, and only that. A key that parses is stored with');
    note('  whatever hash you claim for it. o1js checkValidity at transaction-validation.ts:314 is');
    note('  LOCAL-ONLY and is not on the devnet path. So a devnet submission of a lying pair WOULD be');
    note('  accepted by the daemon at ingest — and then diverge from every peer, because bin_prot');
    note('  RECOMPUTES the hash on receipt (verification_key_wire.ml:30-46, "don\'t send hash over the');
    note('  wire; restore hash on receipt"). buildSetVerificationKeyUpdateChecked closes this at the');
    note('  only place under our control: before the transaction exists.');
  }

  // ═══ F. SUBMIT (NOT RUN) ═══════════════════════════════════════════════════════════════════════
  step('F. WHAT WOULD SUBMIT THIS TO DEVNET — PREPARED, NOT RUN');
  note('EXISTS, reusable as-is:');
  note('  • the builder                     src/ForeignVerificationKey.ts');
  note('  • devnet plumbing + key custody   scripts/devnet-common.ts (loadKeys/connect/assertDevnet)');
  note('  • fee payer + nonce               o1js fills both: Mina.transaction({sender, fee}) reads');
  note('                                    the nonce via fetchAccount; devnet-common.nonceOf reports it');
  note('  • a funded devnet deployer        devnet-deployment.json deployerAddress (see below)');
  note('MUST BE WRITTEN — one script, ~30 lines, modelled on scripts/devnet-head-deploy.ts:');
  note('  • pick/mint the TARGET account. ⚠ A FRESH account is required if you want the FIRST key:');
  note('    the existing zkAppAddress in devnet-deployment.json already carries DreggAttestedGate\'s');
  note('    key, and overwriting it is a re-registration, not a registration. A fresh account also');
  note('    needs AccountUpdate.fundNewAccount(deployer) for the 1 MINA creation fee.');
  note('  • sign with BOTH the fee payer and the target account key, then .send().');
  note('THE COMMAND THAT WOULD DO IT (do not run):');
  note('  MINA_ENDPOINT=https://api.minascan.io/node/devnet/v1/graphql \\');
  note('    npx ts-node --transpile-only scripts/devnet-register-foreign-vk.ts \\');
  note(`      --vk ${vkPaths[vkPaths.length - 1]}`);
  note('THE RAW GraphQL THIS WOULD POST (o1js graphql.ts:501, sendZkappQuery):');
  note(`  mutation { sendZkapp(input: { zkappCommand: <the ${json.length}-char command built in step C> }) { ... } }`);
  note('⚠ NOT SENT. Outward-facing and irreversible; ember\'s call.');

  // ═══ verdict ═══════════════════════════════════════════════════════════════════════════════════
  console.log();
  if (fails === 0) {
    console.log('== FOREIGN-VK REGISTRATION GATE GREEN ==');
    console.log('   A verification key DERIVED from Lean-assembled wrap gates was placed on a Mina');
    console.log("   account by Mina's own transaction logic, and read back byte-identically.");
    console.log('   No compiled o1js contract anywhere in the path. Nothing submitted to any network.');
  } else {
    console.log(`== FOREIGN-VK REGISTRATION GATE RED (${fails}) ==`);
  }
  process.exit(fails === 0 ? 0 : 1);
}

main().catch((e) => {
  console.error('\nRED: gate threw\n', e);
  process.exit(1);
});
