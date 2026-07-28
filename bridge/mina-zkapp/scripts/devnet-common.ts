// Shared plumbing for the Mina **DEVNET** scripts (fund / deploy / attest).
//
// ⚑ DEVNET ONLY, THROWAWAY KEYS. Nothing here may be pointed at mainnet, and the
// key material never enters the repository: `loadKeys` reads a 0600 file OUTSIDE
// the tree (`~/.config/dregg-mina/devnet-keys.json` by default, `DREGG_MINA_KEYS`
// to override) and the repo only ever records the PUBLIC addresses. `keygen` mints
// that file if it is absent, which is what makes a fresh reproduction one command.

import { Mina, PrivateKey, PublicKey, fetchAccount } from 'o1js';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { homedir } from 'node:os';

/** Devnet GraphQL. Minascan's node proxy; `MINA_ENDPOINT` overrides. */
export const MINA_ENDPOINT =
  process.env.MINA_ENDPOINT ??
  'https://api.minascan.io/node/devnet/v1/graphql';

/** Where the throwaway devnet keys live — deliberately OUTSIDE the repo. */
export const KEYS_PATH =
  process.env.DREGG_MINA_KEYS ??
  `${homedir()}/.config/dregg-mina/devnet-keys.json`;

/** Refuse to run against anything that is not a devnet endpoint. */
export function assertDevnet() {
  const e = MINA_ENDPOINT.toLowerCase();
  if (!e.includes('devnet')) {
    throw new Error(
      `REFUSING: MINA_ENDPOINT ${MINA_ENDPOINT} is not a devnet endpoint. ` +
        'These scripts are devnet-only by construction.',
    );
  }
}

export type DevnetKeys = {
  deployerPrivate: string;
  deployerPublic: string;
  zkAppPrivate: string;
  zkAppPublic: string;
};

/** Mint the throwaway keypairs if they do not exist yet. Never overwrites. */
export function keygen(): DevnetKeys {
  if (existsSync(KEYS_PATH)) {
    return JSON.parse(readFileSync(KEYS_PATH, 'utf8')) as DevnetKeys;
  }
  const dep = PrivateKey.random();
  const zk = PrivateKey.random();
  const keys: DevnetKeys = {
    deployerPrivate: dep.toBase58(),
    deployerPublic: dep.toPublicKey().toBase58(),
    zkAppPrivate: zk.toBase58(),
    zkAppPublic: zk.toPublicKey().toBase58(),
  };
  mkdirSync(dirname(KEYS_PATH), { recursive: true, mode: 0o700 });
  writeFileSync(
    KEYS_PATH,
    JSON.stringify(
      {
        note:
          'THROWAWAY Mina DEVNET keys for the dregg attestation zkApp. ' +
          'Never mainnet. Never commit. Regenerate freely.',
        created: new Date().toISOString(),
        ...keys,
      },
      null,
      2,
    ),
    { mode: 0o600 },
  );
  return keys;
}

export function loadKeys(): {
  raw: DevnetKeys;
  deployerKey: PrivateKey;
  deployer: PublicKey;
  zkAppKey: PrivateKey;
  zkApp: PublicKey;
} {
  const raw = keygen();
  const deployerKey = PrivateKey.fromBase58(raw.deployerPrivate);
  const zkAppKey = PrivateKey.fromBase58(raw.zkAppPrivate);
  return {
    raw,
    deployerKey,
    deployer: deployerKey.toPublicKey(),
    zkAppKey,
    zkApp: zkAppKey.toPublicKey(),
  };
}

/** Point o1js at devnet (after asserting it IS devnet). */
export function connect() {
  assertDevnet();
  Mina.setActiveInstance(Mina.Network(MINA_ENDPOINT));
}

/** Balance in nanomina, or `null` when the account does not exist on chain. */
export async function balance(pk: PublicKey): Promise<bigint | null> {
  const r = await fetchAccount({ publicKey: pk });
  if (r.account === undefined) return null;
  return r.account.balance.toBigInt();
}

/** Current nonce, or `null` when the account does not exist on chain. */
export async function nonceOf(pk: PublicKey): Promise<number | null> {
  const r = await fetchAccount({ publicKey: pk });
  if (r.account === undefined) return null;
  return Number(r.account.nonce.toBigint());
}

export const explorerTx = (h: string) => `https://minascan.io/devnet/tx/${h}`;
export const explorerAcct = (a: string) =>
  `https://minascan.io/devnet/account/${a}`;

export const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';
export const mina = (nano: bigint) => (Number(nano) / 1e9).toFixed(3) + ' MINA';

/** Poll until `f` is true or the budget runs out. Returns whether it succeeded. */
export async function until(
  f: () => Promise<boolean>,
  label: string,
  budgetMs = 20 * 60_000,
  everyMs = 20_000,
): Promise<boolean> {
  const t0 = Date.now();
  for (;;) {
    if (await f()) return true;
    if (Date.now() - t0 > budgetMs) return false;
    process.stdout.write(`    ...waiting for ${label} (${secs(t0)})\n`);
    await new Promise((r) => setTimeout(r, everyMs));
  }
}
