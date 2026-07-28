// Fund the throwaway DEVNET deployer from the Mina testnet faucet.
//
//   npm run devnet:fund
//
// The faucet gates on a ZK "sum-to-100" captcha; `Mina.faucet` (o1js >= 2.15)
// fetches the challenge, compiles the tiny challenge circuit, proves, and
// submits. Requesting by hand against `/api/v1/faucet` returns
// `challenge-required` forever — the proof is the ticket, so this must go
// through o1js, not curl.
//
// One funding per address (`rate-limit`), 5/hour and 10/day per IP
// (`rate-limit-ip`). Both are reported as-is rather than retried.

import { Mina } from 'o1js';
import {
  balance,
  connect,
  explorerAcct,
  KEYS_PATH,
  loadKeys,
  mina,
  MINA_ENDPOINT,
  secs,
  until,
} from './devnet-common.js';

async function main() {
  console.log('=== dregg zkApp: fund the devnet deployer ===');
  connect();
  const { deployer, zkApp } = loadKeys();
  console.log(`  endpoint : ${MINA_ENDPOINT}`);
  console.log(`  keys     : ${KEYS_PATH}  (gitignored, 0600, OUTSIDE the repo)`);
  console.log(`  deployer : ${deployer.toBase58()}`);
  console.log(`  zkApp    : ${zkApp.toBase58()}\n`);

  const before = await balance(deployer);
  if (before !== null && before > 0n) {
    console.log(`  already funded: ${mina(before)} — nothing to do.`);
    console.log(`  ${explorerAcct(deployer.toBase58())}`);
    return;
  }

  console.log('  requesting from the faucet (solves the ZK captcha; ~1 min)...');
  const t = Date.now();
  try {
    await Mina.faucet(deployer);
  } catch (e) {
    const m = e instanceof Error ? e.message : String(e);
    console.error(`  faucet request FAILED: ${m}`);
    console.error(
      '  If this is `rate-limit`, the address is already funded (one per address).\n' +
        '  If `rate-limit-ip`, wait an hour. Otherwise fund by hand at\n' +
        `  https://faucet.minaprotocol.com/?address=${deployer.toBase58()} (choose Devnet).`,
    );
    process.exit(1);
  }
  console.log(`  faucet accepted the request in ${secs(t)}`);

  const ok = await until(
    async () => ((await balance(deployer)) ?? 0n) > 0n,
    'the funding transaction to land',
  );
  if (!ok) {
    console.error('  funds did not arrive within the budget.');
    process.exit(1);
  }
  console.log(`\n  funded: ${mina((await balance(deployer))!)}`);
  console.log(`  ${explorerAcct(deployer.toBase58())}`);
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
