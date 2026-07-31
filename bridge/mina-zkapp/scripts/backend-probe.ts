// BACKEND PROBE — is `O1JS_BACKEND=native` usable HERE, and does it change the
// verification key?
//
//   npm run backend-probe
//
// ── WHY A PROBE AND NOT A README LINE ──────────────────────────────────────
// `@o1js/native` ships PER-PLATFORM optional binaries (`native-linux-x64`,
// `native-darwin-arm64`, …). npm installs the one matching the host, so whether
// the native backend is actually available is a property of the MACHINE THE
// DEMO RUNS ON, not of the lockfile. A runbook that says "set O1JS_BACKEND=native
// for 2.2x" and is read on a box where the optional dependency did not install
// is a runbook that hands someone a silent fallback — or a crash — at 08:00.
//
// So this asks the box. It compiles ONE small ZkProgram, proves once, verifies
// once, and prints the wall clock and the verification-key hash.
//
// ── THE ONE THING IT IS FOR ────────────────────────────────────────────────
// The VK hash is the load-bearing output, not the timing. A deployed zkApp's
// ADDRESS is a function of its verification key; the pins in `DreggHeadGate`
// live in the VK by design. If the two backends disagreed on a VK hash, then
// "compile on hbox with native, deploy from the mac" would be a silent flag day
// — the address would not correspond to the sources anyone read. Running both
// and comparing is what turns that from an assumption into a measurement.
//
// Compare two runs:
//
//   O1JS_BACKEND=native npm run backend-probe
//   npm run backend-probe                        # whatever the default is
//
// The script prints `backend-probe.json` shaped lines on stdout; the demo
// scripts diff the `vkHash` fields.

import { Field, Poseidon, ZkProgram, verify } from 'o1js';

const t0 = Date.now();
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(2)}s`;

/** A program small enough to compile in seconds and real enough to prove. */
const Probe = ZkProgram({
  name: 'dregg-backend-probe',
  publicInput: Field,
  publicOutput: Field,
  methods: {
    hash: {
      privateInputs: [Field],
      async method(seed: Field, x: Field) {
        // A few Poseidon rounds: enough constraints that the backend matters,
        // few enough that the probe stays a probe.
        let acc = Poseidon.hash([seed, x]);
        for (let i = 0; i < 8; i++) acc = Poseidon.hash([acc, Field(i)]);
        return { publicOutput: acc };
      },
    },
  },
});

async function main() {
  const requested = process.env.O1JS_BACKEND ?? '(unset — o1js default)';
  console.log('=== o1js BACKEND PROBE ===');
  console.log(`  O1JS_BACKEND requested : ${requested}`);
  console.log(`  node                   : ${process.version}  ${process.platform}-${process.arch}`);

  //  Report whether the platform binary is even present, BEFORE compiling —
  //  otherwise a missing optional dependency shows up only as "it was slow".
  let nativePkg = 'ABSENT';
  try {
    const id = `@o1js/native-${process.platform}-${process.arch}`;
    const { createRequire } = await import('node:module');
    const req = createRequire(import.meta.url);
    req.resolve(id);
    nativePkg = `present (${id})`;
  } catch {
    nativePkg = `ABSENT for ${process.platform}-${process.arch}`;
  }
  console.log(`  @o1js/native binary    : ${nativePkg}\n`);

  let t = Date.now();
  const { verificationKey } = await Probe.compile();
  const compileS = secs(t);
  console.log(`  compiled in ${compileS}`);
  console.log(`  vkHash ${verificationKey.hash.toString()}`);

  t = Date.now();
  const proof = await Probe.hash(Field(7), Field(11));
  const proveS = secs(t);
  console.log(`  proved in   ${proveS}`);

  t = Date.now();
  const okd = await verify(proof.proof, verificationKey);
  const verifyS = secs(t);
  if (!okd) {
    console.error('\n✗ the proof did not verify — this backend is not usable.');
    process.exit(1);
  }
  console.log(`  verified in ${verifyS}  (true)`);

  //  A single machine-readable line, so a shell can diff two runs without
  //  parsing prose.
  console.log(
    `\nBACKEND-PROBE ${JSON.stringify({
      backend: process.env.O1JS_BACKEND ?? null,
      platform: `${process.platform}-${process.arch}`,
      nativeBinary: nativePkg.startsWith('present'),
      vkHash: verificationKey.hash.toString(),
      compileS: Number(compileS.replace('s', '')),
      proveS: Number(proveS.replace('s', '')),
      verifyS: Number(verifyS.replace('s', '')),
    })}`,
  );
  console.log(`\n=== BACKEND PROBE PASS === ${secs(t0)}\n`);
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
