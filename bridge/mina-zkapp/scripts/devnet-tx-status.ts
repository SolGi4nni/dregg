// Read a devnet transaction's ON-CHAIN outcome straight from the daemon.
//
//   npm run devnet:tx-status -- <txHash> [blocksToScan]
//
// Why this exists: a zkApp transaction whose account-state precondition fails is
// INCLUDED IN A BLOCK and marked failed — it consumes the fee and bumps the
// nonce, and its effects are discarded. "The state did not change" is only
// circumstantial evidence of that; `failureReason` is the daemon saying it. This
// is what turns the rejection in `devnet-attest.ts` from an inference into a
// quotation.
//
// ⚑ WINDOW. `bestChain` only reaches back a bounded number of blocks, so run
// this within an hour or so of the transaction. After that the block explorer is
// the record — `https://minascan.io/devnet/tx/<hash>`.

import { MINA_ENDPOINT, assertDevnet, explorerTx } from './devnet-common.js';

type ZkappCommand = {
  hash: string;
  failureReason: { index: number; failures: string[] }[] | null;
};

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

async function main() {
  assertDevnet();
  const hash = process.argv[2];
  const depth = Number(process.argv[3] ?? 20);
  if (!hash) {
    console.error('usage: npm run devnet:tx-status -- <txHash> [blocksToScan]');
    process.exit(2);
  }

  console.log(`scanning the last ${depth} blocks of ${MINA_ENDPOINT}`);
  console.log(`for ${hash}\n`);

  const data = await gql<{
    bestChain: {
      stateHash: string;
      protocolState: { consensusState: { blockHeight: string } };
      transactions: { zkappCommands: ZkappCommand[] };
    }[];
  }>(`{ bestChain(maxLength:${depth}) {
        stateHash
        protocolState { consensusState { blockHeight } }
        transactions { zkappCommands { hash failureReason { index failures } } }
      } }`);

  for (const b of data.bestChain) {
    for (const c of b.transactions.zkappCommands) {
      if (c.hash !== hash) continue;
      const height = b.protocolState.consensusState.blockHeight;
      console.log(`FOUND in block ${height} (${b.stateHash})`);
      if (c.failureReason === null) {
        console.log('  status       : APPLIED (no failure reason)');
      } else {
        console.log('  status       : INCLUDED AND FAILED');
        for (const f of c.failureReason) {
          console.log(`  accountUpdate[${f.index}]: ${f.failures.join(', ')}`);
        }
      }
      console.log(`  ${explorerTx(hash)}`);
      return;
    }
  }

  // Absence is NOT a verdict: the transaction may be pending, may have been
  // refused at admission, or may simply have fallen out of the scanned window.
  console.log(`NOT FOUND in the last ${depth} blocks.`);
  console.log('  This is not a verdict — it may be pending, refused at admission,');
  console.log('  or older than the scanned window. Check the explorer:');
  console.log(`  ${explorerTx(hash)}`);
  process.exitCode = 1;
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
