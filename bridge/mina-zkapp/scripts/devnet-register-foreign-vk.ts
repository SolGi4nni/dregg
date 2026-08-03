// REGISTER a verification key we DERIVED OURSELVES onto a Mina **DEVNET** account.
//
//   npx ts-node --transpile-only scripts/devnet-register-foreign-vk.ts --vk <derived.json>
//        DRY RUN. Builds the account update, validates the key against Mina's own reader, prints
//        the exact GraphQL that would be posted, and EXITS WITHOUT SENDING. No network contact
//        unless --fetch is passed.
//
//   ... --fetch          also read the target account and the fee payer's nonce off devnet
//                        (read-only queries; still does not send)
//   ... --broadcast      THE OUTWARD-FACING, IRREVERSIBLE ACT. Refuses unless everything below
//                        is present, and says which piece is missing rather than "not ready".
//
// ─────────────────────────────────────────────────────────────────────────────────────────────────
// WHY A SIGNATURE, AND WHY IT COULD NOT BE A PROOF
//
// A fresh account's `set_verification_key` permission is `(Signature, Txn_version.current)`
// (mina/src/lib/mina_base/permissions.ml:580-594), checked as `Update_not_permitted_verification_key`
// (mina/src/lib/transaction_logic/zkapp_command_logic.ml:1583-1586). So a signature suffices.
//
// It also could not be anything else. The vk that verifies a proof on a VK-SETTING update is the
// account's OLD one — the lookup explicitly excludes "the new one we potentially set in this
// account_update" (mina/src/lib/mina_base/zkapp_command.ml:1200-1232) — so an account with no key
// has nothing to verify a proof against. THE FIRST KEY ALWAYS GOES ON BY SIGNATURE.
//
// ⚠ WHAT THIS DOES NOT DO. It does not mint key material. Custody is the operator's: the target
// keypair is read from the same 0600 file outside the tree that every other devnet script uses
// (`devnet-common.ts`), under `vkTargetPrivate`/`vkTargetPublic`, and this script REFUSES rather
// than adding them. A dry run without a target uses an EPHEMERAL in-memory key, clearly labelled,
// so the build path can be exercised without touching custody at all.
//
// ⚠ AND IT IS NOT A PROOF. Registering a key says a node will STORE it and check proofs against it.
// It does not say any proof verifies under it. `KimchiWrapMain` §13 still names by sub-circuit what
// the wrap assembly does not emit.

import { AccountUpdate, Mina, PrivateKey, PublicKey, UInt32, UInt64, fetchAccount } from 'o1js';
import { readFileSync } from 'node:fs';
import {
  assertForeignVkConsistent,
  buildSetVerificationKeyUpdateChecked,
  decodeVkData,
  loadForeignVk,
} from '../src/ForeignVerificationKey.js';
import { KEYS_PATH, MINA_ENDPOINT, assertDevnet, connect, explorerAcct, mina } from './devnet-common.js';

const argv = process.argv.slice(2);
const flag = (n: string) => argv.includes(n);
const opt = (n: string) => {
  const i = argv.indexOf(n);
  return i >= 0 ? argv[i + 1] : undefined;
};

const VK_PATH = opt('--vk');
const BROADCAST = flag('--broadcast');
const FETCH = flag('--fetch') || BROADCAST;
const FEE = UInt64.from(Number(opt('--fee') ?? 100_000_000));

if (VK_PATH === undefined) {
  console.error(
    'REFUSING: no --vk given.\n' +
      '  Derive one first:\n' +
      '    cargo run --release --manifest-path metatheory/fixtures/pickles-vk-derive/Cargo.toml -- <outdir> --log2-domain 14\n' +
      '  then: --vk <outdir>/vk-wrapmain-w4_bind.json',
  );
  process.exit(2);
}

async function main() {
  const vk = loadForeignVk(VK_PATH!);
  const bytes = decodeVkData(vk.data);
  console.log('REGISTER A DERIVED VERIFICATION KEY — Mina devnet');
  console.log(`   key      : ${VK_PATH}`);
  console.log(`   wire     : ${bytes.length} bytes Side_loaded_verification_key.Stable.V2`);
  console.log(`   hash     : ${String(vk.hash)}`);
  console.log(`   mode     : ${BROADCAST ? '⚠ BROADCAST (outward-facing, irreversible)' : 'DRY RUN — will not send'}`);

  // 1. The key must be one Mina can read, and its hash must be the digest of its data. ⚠ The daemon
  //    does NOT check this at JSON ingest (measured: scripts/foreign-vk-registration-gate.sh step E'),
  //    so this is the only place it gets checked before the key becomes account state.
  const digest = await assertForeignVkConsistent(vk);
  console.log(`   VALIDATED: Mina's own reader parses it and its digest is ${digest.toString()}`);

  // 2. Custody. Never minted here.
  let target: PublicKey;
  let targetKey: PrivateKey | undefined;
  let ephemeral = false;
  const raw = (() => {
    try {
      return JSON.parse(readFileSync(KEYS_PATH, 'utf8'));
    } catch {
      return {};
    }
  })();
  if (typeof raw.vkTargetPrivate === 'string') {
    targetKey = PrivateKey.fromBase58(raw.vkTargetPrivate);
    target = targetKey.toPublicKey();
  } else if (!BROADCAST) {
    targetKey = PrivateKey.random();
    target = targetKey.toPublicKey();
    ephemeral = true;
  } else {
    console.error(
      `REFUSING: ${KEYS_PATH} has no \`vkTargetPrivate\`/\`vkTargetPublic\`.\n` +
        '  ⚑ A FRESH ACCOUNT IS REQUIRED, not a reused one. The first key can only go on by\n' +
        '    signature (see the header), and every account already named in devnet-deployment.json\n' +
        '    carries a key — setting one there is a RE-registration and needs that account to still\n' +
        '    permit it. Registering onto a virgin account is the thing being demonstrated.\n' +
        '  ⚑ THIS SCRIPT DOES NOT MINT KEY MATERIAL. Add a throwaway devnet keypair to that 0600\n' +
        '    file yourself, then fund it — the account also needs the 1 MINA creation fee, paid by\n' +
        '    the deployer via AccountUpdate.fundNewAccount below.',
    );
    process.exit(2);
  }
  console.log(`   target   : ${target.toBase58()}${ephemeral ? '   ⚠ EPHEMERAL in-memory key (dry run only, never written)' : ''}`);

  const deployerKey =
    typeof raw.deployerPrivate === 'string' ? PrivateKey.fromBase58(raw.deployerPrivate) : targetKey!;
  const deployer = deployerKey.toPublicKey();
  console.log(`   feepayer : ${deployer.toBase58()}${typeof raw.deployerPrivate === 'string' ? '' : '   ⚠ same as target (no deployer key in the file)'}`);
  console.log(`   fee      : ${mina(FEE.toBigInt())}`);

  // 3. Network state — nonce and whether the account exists. Read-only; skipped entirely without
  //    --fetch so the dry run can be proved with ZERO network contact.
  let accountExists = false;
  let nonce: UInt32 | undefined;
  // The fee payer used when building offline. ⚠ A SECOND `Mina.LocalBlockchain({})` would be a
  // DIFFERENT instance from the active one, and the transaction would be built against a chain
  // whose accounts do not exist — an earlier draft did exactly that.
  let localSender: PublicKey | undefined;
  if (FETCH) {
    assertDevnet();
    connect();
    const t = await fetchAccount({ publicKey: target });
    accountExists = t.account !== undefined;
    const d = await fetchAccount({ publicKey: deployer });
    nonce = d.account?.nonce;
    console.log(`   endpoint : ${MINA_ENDPOINT}`);
    console.log(`   target account exists: ${accountExists}${accountExists ? ` (vk: ${t.account?.zkapp?.verificationKey?.hash?.toString() ?? 'NONE'})` : ''}`);
    console.log(`   deployer nonce: ${nonce?.toString() ?? 'unknown'}, balance ${d.account ? mina(d.account.balance.toBigInt()) : 'UNFUNDED'}`);
    if (accountExists) {
      console.log(
        '   ⚠ the target account ALREADY EXISTS. Setting a key on it is a RE-registration and\n' +
          '     depends on its current setVerificationKey permission, which this script does not\n' +
          '     widen. A first registration wants a virgin account.',
      );
    }
  } else {
    // o1js needs SOME instance to build against. LocalBlockchain gives one without any network.
    localSender = (await (async () => {
      const L = await Mina.LocalBlockchain({ proofsEnabled: false });
      Mina.setActiveInstance(L);
      return L;
    })()).testAccounts[0]!;
    console.log('   endpoint : (none — offline dry run; pass --fetch to read devnet)');
  }

  // 4. THE TRANSACTION. Nothing here is specific to devnet: it is the same builder the gate proves
  //    against Mina's own transaction logic.
  const sender = FETCH ? deployer : localSender!;
  const tx = await Mina.transaction({ sender, fee: FEE }, async () => {
    // The account creation fee, when the target is new. Paid by the fee payer, not the target.
    if (!accountExists) AccountUpdate.fundNewAccount(sender);
    await buildSetVerificationKeyUpdateChecked({
      address: target,
      verificationKey: vk,
      label: `register derived VK from ${VK_PATH}`,
    });
  });

  const json = tx.toJSON();
  console.log(`\n   BUILT: a ${json.length}-char zkApp command, ${tx.transaction.accountUpdates.length} account updates`);
  console.log(`   the VK-setting update carries ${bytes.length} bytes and hash ${String(vk.hash)}`);

  if (!BROADCAST) {
    console.log('\n── THE GraphQL THAT WOULD BE POSTED (o1js graphql.ts:501) ──────────────────');
    console.log('   mutation { sendZkapp(input: { zkappCommand: <the command above> }) { zkapp { hash id } } }');
    console.log('\n── NOT SENT ────────────────────────────────────────────────────────────────');
    console.log('   This is a dry run. Registering a verification key on a public network is');
    console.log('   outward-facing and irreversible. To actually do it:');
    console.log(`     MINA_ENDPOINT=${MINA_ENDPOINT} \\`);
    console.log(`       npx ts-node --transpile-only scripts/devnet-register-foreign-vk.ts \\`);
    console.log(`         --vk ${VK_PATH} --broadcast`);
    console.log(`   and first put a fresh throwaway keypair in ${KEYS_PATH} as`);
    console.log('   `vkTargetPrivate`/`vkTargetPublic`, funded enough to cover the 1 MINA account');
    console.log('   creation fee plus the transaction fee.');
    process.exit(0);
  }

  // ── the outward-facing act ──────────────────────────────────────────────────────────────────────
  assertDevnet();
  tx.sign([deployerKey, targetKey!]);
  console.log('\n   SENDING…');
  const pending = await tx.send();
  console.log(`   tx hash : ${pending.hash}`);
  console.log(`   status  : ${pending.status}`);
  console.log(`   account : ${explorerAcct(target.toBase58())}`);
}

main().catch((e) => {
  console.error('\nFAILED\n', e);
  process.exit(1);
});
