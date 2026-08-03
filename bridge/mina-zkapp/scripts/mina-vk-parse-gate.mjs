// MINA VK PARSE GATE — does Mina's OWN parser accept a verification key we DERIVED?
//
// WHAT A MINA `VerificationKey` IS, at source.
//   o1js `VerificationKey` is `Struct({ data: String, hash: Field })`
//   (o1js/dist/node/lib/proof-system/verification-key.js:8-13). `data` is base64 of the binprot
//   encoding of `Pickles.Side_loaded.Verification_key.Stable.V2.t`; `hash` is the field element a
//   zkApp account stores next to it. `VerificationKey.checkValidity` (:28-41) is the real acceptance
//   predicate: it runs `Pickles.sideLoaded.vkToCircuit(() => key.data)` — the OCaml binprot reader
//   compiled into o1js — and asserts `inCircuitVkHash(vk) == key.hash`, where `inCircuitVkHash`
//   (zkprogram.js:486-492) is `Poseidon_state(prefix "sideLoadedVK") absorbed with
//   Pickles.sideLoaded.vkDigest(vk)`.
//
//   The binprot body, DECODED FROM o1js's OWN DUMMY (verification-key.js:43-47, 1796 bytes):
//       [0]      max_proofs_verified      : Proofs_verified.t variant tag (0=N0, 1=N1, 2=N2)
//       [1]      actual_wrap_domain_size  : Proofs_verified.t variant tag
//       then wrap_index, a `Plonk_verification_key_evals.t`, 28 commitments in this order:
//         7  sigma_comm         then ONE 0x00 byte  (binprot nil of the pickles_types Vector)
//         15 coefficients_comm  then ONE 0x00 byte
//         generic, psm, complete_add, mul, emul, endomul_scalar
//       each commitment is 64 bytes: x (32 LE) || y (32 LE), a PALLAS point, NO tag, NO compression.
//   2 + 7*64 + 1 + 15*64 + 1 + 6*64 = 1796. Confirmed byte-for-byte against o1js's dummy, whose
//   every point is (1, sqrt(6)) and satisfies y^2 = x^3 + 5 over Pallas's BASE field Fp.
//   The same 28 fields, in the same order, are what openmina reads back out of an account to build a
//   verifier index: mina-rust/crates/ledger/src/proofs/verifiers.rs:446-476.
//
// WHAT THIS SCRIPT IS FOR. `metatheory/fixtures/pickles-vk-derive` DERIVES those 28 commitments from
// the Lean-assembled `KimchiWrapMain` gate list (Pallas/Fq) and writes that base64. This script is
// the GATE: Mina's own reader must accept it. Nothing here proves a PROOF verifies — this is the KEY.
//
// USAGE
//   node scripts/mina-vk-parse-gate.mjs --vk <derived-vk.json>          # the gate, green-or-bust
//   node scripts/mina-vk-parse-gate.mjs --vk <a.json> --vk <b.json>     # + show the hashes differ
//   node scripts/mina-vk-parse-gate.mjs --self-test                     # red path only
//   node scripts/mina-vk-parse-gate.mjs --reference-dump <out.json>     # compile two real o1js
//        circuits and dump their {data,hash} — an INDEPENDENT source for the encoding and a control
//        that o1js's own VK moves when o1js's own circuit moves.
//
// A `--vk` file is `{ "data": "<base64>", ... }`; extra keys are ignored.

import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { pathToFileURL, fileURLToPath } from 'node:url';
import path from 'node:path';

// o1js's package `exports` hides its internals, and the two calls this gate needs
// (`Pickles.sideLoaded.vkToCircuit`, `inCircuitVkHash`) are internal. Resolve the package
// directory by walking up from this script instead of through the export map.
const O1JS = (() => {
  let d = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const c = path.join(d, 'node_modules', 'o1js');
    if (existsSync(path.join(c, 'dist', 'node', 'index.js'))) return c;
    const up = path.dirname(d);
    if (up === d) throw new Error('cannot locate node_modules/o1js above ' + import.meta.url);
    d = up;
  }
})();
const imp = (p) => import(pathToFileURL(path.join(O1JS, p)).href);

const { Field, Provable, VerificationKey, ZkProgram } = await imp('dist/node/index.js');
// ⚑ keep the NAMESPACE, do not destructure: `Pickles` is a module-scope `let` that
// `initializeBindings()` reassigns (o1js dist/node/bindings.js:6,32). A destructured copy snapshots
// `undefined`, and every call below then fails with the SAME error a malformed key produces — which
// would make the red path pass for the wrong reason.
const bindings = await imp('dist/node/bindings.js');
const { inCircuitVkHash } = await imp('dist/node/lib/proof-system/zkprogram.js');
const { synchronousRunners } = await imp('dist/node/lib/provable/core/provable-context.js');

await bindings.initializeBindings();
if (typeof bindings.Pickles?.sideLoaded?.vkToCircuit !== 'function') {
  throw new Error('o1js bindings did not expose Pickles.sideLoaded.vkToCircuit; refusing to run a gate that cannot go green');
}
const { runAndCheckSync } = await synchronousRunners();

// ---- argv ----
const argv = process.argv.slice(2);
const vkPaths = [];
let selfTest = false;
let referenceDump = null;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '--vk') vkPaths.push(argv[++i]);
  else if (argv[i] === '--self-test') selfTest = true;
  else if (argv[i] === '--reference-dump') referenceDump = argv[++i];
  else throw new Error(`unknown argument ${argv[i]}`);
}

let failures = 0;
const say = (ok, msg) => {
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${msg}`);
};

// ---- the parse itself ----
// Returns the in-circuit VK hash, or throws. This is EXACTLY the call `VerificationKey.checkValidity`
// makes, run without the hash assertion so we can report the hash Mina's own reader computes.
function parseAndHash(data) {
  let hash;
  runAndCheckSync(() => {
    const vk = bindings.Pickles.sideLoaded.vkToCircuit(() => data);
    // Read the value INSIDE the checked computation: `inCircuitVkHash` returns a circuit variable,
    // and a variable read outside its runner throws "variables only exist inside checked
    // computations" — an error indistinguishable from a parse failure if it escapes.
    const h = inCircuitVkHash(vk);
    // Read the witness value INSIDE the checked computation and inside `asProver`: `h` is a circuit
    // VARIABLE, and reading it anywhere else throws an error indistinguishable from a parse failure.
    Provable.asProver(() => {
      hash = h.toBigInt().toString();
    });
  });
  return hash;
}

function tryParse(data) {
  try {
    return { ok: true, hash: parseAndHash(data) };
  } catch (e) {
    return { ok: false, error: String(e && e.message ? e.message : e).split('\n')[0] };
  }
}

// ---- reference dump: two REAL o1js circuits ----
if (referenceDump) {
  const mk = (name, extra) =>
    ZkProgram({
      name,
      publicInput: Field,
      methods: {
        run: {
          privateInputs: [Field],
          async method(pub, w) {
            let acc = w.mul(w);
            for (let i = 0; i < extra; i++) acc = acc.mul(w).add(Field(i));
            acc.assertEquals(acc);
            pub.assertEquals(pub);
          },
        },
      },
    });
  const out = {};
  for (const [name, extra] of [['refA', 1], ['refB', 2]]) {
    const t0 = Date.now();
    const { verificationKey } = await mk(name, extra).compile();
    out[name] = {
      data: verificationKey.data,
      hash: verificationKey.hash.toString(),
      dataBytes: Buffer.from(verificationKey.data, 'base64').length,
      compileMs: Date.now() - t0,
    };
    console.log(`compiled ${name}: ${out[name].dataBytes} binprot bytes, hash ${out[name].hash}`);
  }
  say(out.refA.data !== out.refB.data, 'two o1js circuits that differ produce DIFFERENT vk.data');
  say(out.refA.hash !== out.refB.hash, 'two o1js circuits that differ produce DIFFERENT vk.hash');
  // The dummy is a third, independent instance of the same encoding.
  const dummy = VerificationKey.dummySync();
  out.dummy = { data: dummy.data, hash: dummy.hash.toString(), dataBytes: Buffer.from(dummy.data, 'base64').length };
  say(out.dummy.dataBytes === 1796, `o1js dummy vk.data is 1796 binprot bytes (got ${out.dummy.dataBytes})`);
  writeFileSync(referenceDump, JSON.stringify(out, null, 2) + '\n');
  console.log(`wrote ${referenceDump}`);
}

// ⚑ NOTHING TO DO IS NOT GREEN. Run with no arguments this file used to reach its trailer with
// `vkPaths` empty, `parsed` empty and the red-path block skipped, print `GATE GREEN` and exit 0 —
// a verdict about zero keys. Its sibling `mina-proof-parse-gate.mjs` already refuses exactly this;
// this one did not, and only the caller (`mina-vk-derivation-gate.sh`, which reds below three VK
// files) kept the fail-open latent rather than live. (2026-08-03)
if (vkPaths.length === 0 && !selfTest && !referenceDump) {
  console.error('nothing to do: pass --vk <file> (repeatable), --self-test, or --reference-dump <file>');
  console.error('⚠ a run that grades no key is NOT green.');
  process.exit(2);
}

// ---- the gate ----
const parsed = [];
for (const p of vkPaths) {
  const j = JSON.parse(readFileSync(p, 'utf8'));
  const data = j.data ?? j.vk?.data;
  if (typeof data !== 'string') throw new Error(`${p}: no string field "data"`);
  const nbytes = Buffer.from(data, 'base64').length;
  const r = tryParse(data);
  say(r.ok, `o1js Pickles.sideLoaded.vkToCircuit PARSED ${path.basename(p)} (${nbytes} binprot bytes)` + (r.ok ? `` : ` -- ${r.error}`));
  if (!r.ok) continue;
  console.log(`      in-circuit VK hash = ${r.hash}`);
  const key = new VerificationKey({ data, hash: Field(r.hash) });
  const valid = await VerificationKey.checkValidity(key);
  say(valid === true, `o1js VerificationKey.checkValidity({data,hash}) === true for ${path.basename(p)}`);
  // A VK is accepted only against ITS OWN hash: state a different hash and it must refuse.
  const wrongHash = await VerificationKey.checkValidity(
    new VerificationKey({ data, hash: Field(r.hash).add(1) })
  );
  say(wrongHash === false, `checkValidity REFUSES ${path.basename(p)} under a hash off by one`);
  parsed.push({ path: p, data, hash: r.hash, bytes: nbytes });
}

if (parsed.length >= 2) {
  const distinct = new Set(parsed.map((p) => p.hash)).size;
  say(distinct === parsed.length, `the ${parsed.length} supplied VKs have ${distinct} DISTINCT in-circuit hashes`);
  for (const p of parsed) console.log(`      ${path.basename(p.path)} -> ${p.hash}`);
}

// ---- red path: the reader must REFUSE malformed keys ----
if (selfTest || parsed.length > 0) {
  const base = parsed.length ? parsed[0].data : VerificationKey.dummySync().data;
  const raw = Buffer.from(base, 'base64');
  // ANCHOR. A refusal only means something if the UNMUTATED key is accepted by the same call. If
  // this is red, every "REFUSED" below is a false pass and the whole red path is void.
  const anchor = tryParse(base);
  say(anchor.ok, `red-path ANCHOR: the unmutated key PARSES` + (anchor.ok ? ` (hash ${anchor.hash})` : ` -- ${anchor.error}`));
  if (!anchor.ok) {
    console.log('\nGATE RED: red-path anchor did not parse; refusals below would be vacuous');
    process.exit(1);
  }

  // (a) a point knocked OFF the curve: bump the x of sigma_comm[0] (bytes 2..34) by one.
  {
    const b = Buffer.from(raw);
    b[2] = (b[2] + 1) & 0xff;
    const r = tryParse(b.toString('base64'));
    say(!r.ok, `REFUSED: sigma_comm[0].x + 1 knocks the point off Pallas` + (r.ok ? ` -- ACCEPTED, hash ${r.hash}` : ` -- ${r.error}`));
  }
  // (b) truncation: one byte short.
  {
    const r = tryParse(raw.subarray(0, raw.length - 1).toString('base64'));
    say(!r.ok, `REFUSED: binprot truncated by one byte` + (r.ok ? ` -- ACCEPTED` : ` -- ${r.error}`));
  }
  // (c) the Vector nil after sigma_comm[6] replaced by a non-zero byte.
  {
    const b = Buffer.from(raw);
    b[2 + 7 * 64] = 0x01;
    const r = tryParse(b.toString('base64'));
    say(!r.ok, `REFUSED: the 0x00 binprot nil after sigma_comm[6] set to 0x01` + (r.ok ? ` -- ACCEPTED` : ` -- ${r.error}`));
  }
  // (d) an out-of-range field limb (x = p, the Pallas base modulus).
  {
    const b = Buffer.from(raw);
    const p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001n;
    let v = p;
    for (let i = 0; i < 32; i++) { b[2 + i] = Number(v & 0xffn); v >>= 8n; }
    const r = tryParse(b.toString('base64'));
    say(!r.ok, `REFUSED: sigma_comm[0].x set to the field modulus p` + (r.ok ? ` -- ACCEPTED` : ` -- ${r.error}`));
  }
}

console.log(failures === 0 ? '\nGATE GREEN' : `\nGATE RED: ${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
