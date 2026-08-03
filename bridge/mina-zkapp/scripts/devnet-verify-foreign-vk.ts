// READ A REGISTERED VERIFICATION KEY BACK OFF MINA DEVNET and check it against the key we derived.
//
//   npx ts-node --transpile-only scripts/devnet-verify-foreign-vk.ts --vk <derived.json> [--address B62...]
//
// ⚑ WHY THIS IS A SEPARATE SCRIPT FROM THE ONE THAT SENDS. `devnet-register-foreign-vk.ts --broadcast`
// ends at `pending` — that is the daemon ACCEPTING a transaction into its pool, which is not the
// same event as the key becoming account state. A broadcast that "succeeded" is not the milestone;
// the account holding the key is. This reads the account back from the network with NOTHING from the
// send path in scope, and is re-runnable forever after.
//
// ⚑ AND IT DOES NOT TRUST THE HASH THE CHAIN REPORTS. The registration gate MEASURED that Mina's
// JSON/GraphQL ingest performs no data↔hash validation (fields_derivers_zkapps.ml:555-574 reads the
// two as independent fields) — a parseable blob is stored with whatever hash you claim for it. So
// "the stored hash equals our hash" alone would be satisfiable by a key whose bytes are anything
// that deserialises. Check 3 below re-derives the digest from the BYTES THE CHAIN RETURNED, using
// Mina's own reader, and that is the check that makes the other two mean something.
//
// Read-only. No key material, no signing, no sending; a bare GraphQL query and a local digest.

import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import {
  assertForeignVkConsistent,
  decodeVkData,
  loadForeignVk,
} from '../src/ForeignVerificationKey.js';
import { MINA_ENDPOINT, assertDevnet, explorerAcct } from './devnet-common.js';

const argv = process.argv.slice(2);
const opt = (n: string) => {
  const i = argv.indexOf(n);
  return i >= 0 ? argv[i + 1] : undefined;
};

const VK_PATH = opt('--vk');
if (VK_PATH === undefined) {
  console.error('usage: devnet-verify-foreign-vk.ts --vk <derived.json> [--address B62...]');
  process.exit(2);
}

/** The target defaults to the same custody file the registration reads, so the two scripts cannot
 *  drift onto different accounts without someone saying so on the command line. */
const ADDRESS = (() => {
  const explicit = opt('--address');
  if (explicit !== undefined) return explicit;
  const p = process.env.DREGG_MINA_KEYS ?? `${homedir()}/.config/dregg-mina/devnet-keys.json`;
  const raw = JSON.parse(readFileSync(p, 'utf8'));
  if (typeof raw.vkTargetPublic !== 'string') {
    throw new Error(`${p} has no \`vkTargetPublic\`, and no --address was given`);
  }
  return raw.vkTargetPublic as string;
})();

async function gql<T>(query: string): Promise<T> {
  const r = await fetch(MINA_ENDPOINT, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ query }),
  });
  if (!r.ok) throw new Error(`GraphQL HTTP ${r.status} ${r.statusText}`);
  const j = (await r.json()) as { data?: T; errors?: unknown };
  if (j.errors) throw new Error(`GraphQL errors: ${JSON.stringify(j.errors)}`);
  if (!j.data) throw new Error('GraphQL returned no data');
  return j.data;
}

let fails = 0;
const green = (s: string) => console.log(`   GREEN: ${s}`);
const red = (s: string) => {
  console.log(`   RED:   ${s}`);
  fails += 1;
};

async function main() {
  assertDevnet();
  const local = loadForeignVk(VK_PATH!);
  const localBytes = decodeVkData(local.data);
  const localHash = String(local.hash);

  console.log('VERIFY A REGISTERED VERIFICATION KEY — read back off Mina devnet');
  console.log(`   endpoint : ${MINA_ENDPOINT}`);
  console.log(`   account  : ${ADDRESS}`);
  console.log(`   derived  : ${VK_PATH}`);
  console.log(`   local    : ${localBytes.length} bytes, hash ${localHash}`);

  // The account, straight from the daemon. `verificationKey.verificationKey` is the base64 wire
  // blob; `verificationKey.hash` is the field element stored beside it.
  const d = await gql<{
    account: null | {
      balance: { total: string };
      nonce: string;
      verificationKey: null | { hash: string; verificationKey: string };
    };
  }>(`{ account(publicKey: "${ADDRESS}") {
        balance { total }
        nonce
        verificationKey { hash verificationKey }
      } }`);

  if (d.account === null) {
    red('the account DOES NOT EXIST on this network — nothing was registered');
    return;
  }
  console.log(`   balance  : ${(Number(d.account.balance.total) / 1e9).toFixed(3)} MINA, nonce ${d.account.nonce}`);

  if (d.account.verificationKey === null) {
    red('the account exists but carries NO verification key');
    return;
  }
  const chainHash = d.account.verificationKey.hash;
  const chainData = d.account.verificationKey.verificationKey;
  const chainBytes = decodeVkData(chainData);
  console.log(`   on-chain : ${chainBytes.length} bytes, hash ${chainHash}`);
  console.log();

  // 1. The hash the chain stores is the hash we derived.
  if (chainHash === localHash) {
    green(`on-chain hash === derived hash: ${chainHash}`);
  } else {
    red(`on-chain hash ${chainHash} !== derived hash ${localHash}`);
  }

  // 2. The bytes round-trip. ⚠ Not implied by (1): the ingest path stores data and hash
  //    independently, so equal hashes with different bytes is a state the daemon permits.
  const localSha = createHash('sha256').update(localBytes).digest('hex');
  const chainSha = createHash('sha256').update(chainBytes).digest('hex');
  if (chainData === local.data && chainSha === localSha) {
    green(
      `on-chain data === derived data, all ${chainData.length} base64 chars / ${chainBytes.length} bytes ` +
        `(sha256 ${chainSha})`,
    );
  } else {
    red(`on-chain data differs: sha256 ${chainSha} vs derived ${localSha}`);
  }

  // 3. THE ONE THAT MAKES THE OTHER TWO MEAN SOMETHING. Re-derive the digest from the bytes the
  //    CHAIN returned, through Mina's own binprot reader, and compare to the hash the chain stores
  //    beside them. This is the check the GraphQL ingest path does not perform, so it is the only
  //    evidence that what is on the account is a CONSISTENT pair rather than a blob with a label.
  try {
    const digest = await assertForeignVkConsistent({ data: chainData, hash: chainHash });
    green(
      `Mina's own reader re-parses the ON-CHAIN bytes and their digest is ${digest.toString()} — ` +
        'equal to the hash stored beside them, so the account holds a CONSISTENT pair',
    );
  } catch (e) {
    red(`the ON-CHAIN pair is inconsistent or unreadable: ${String((e as Error)?.message ?? e)}`);
  }

  console.log();
  console.log(`   ${explorerAcct(ADDRESS)}`);
}

main()
  .then(() => {
    console.log();
    if (fails === 0) {
      console.log('== ON-CHAIN VERIFICATION KEY VERIFIED ==');
      console.log('   A key derived from Lean-emitted KimchiWrapMain gates is account state on Mina devnet.');
      console.log('   ⚠ THIS SAYS A NODE WILL STORE IT AND CHECK PROOFS AGAINST IT. It does NOT say any');
      console.log('   proof verifies under it — no proof has been produced for this circuit.');
    } else {
      console.log(`== ON-CHAIN VERIFICATION FAILED (${fails}) ==`);
    }
    process.exit(fails > 0 ? 1 : 0);
  })
  .catch((e) => {
    console.error('\nFAILED\n', e);
    process.exit(1);
  });
