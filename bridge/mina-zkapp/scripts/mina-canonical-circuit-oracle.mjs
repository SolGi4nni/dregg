// MINA CANONICAL CIRCUIT ORACLE — the byte target for a Lean-synthesized Pickles wrap/step circuit.
//
// WHAT THIS IS. o1-labs publishes Mina's OWN compiled circuits as `circuit-blobs` release assets, and
// a `*_gates.json` blob is EXACTLY kimchi's `Circuit { public_input_size, gates }` serde form — the
// same bytes `caml_pasta_f{p,q}_plonk_circuit_serialize` emits (mina/src/lib/crypto/kimchi_bindings/
// stubs/src/gate_vector.rs:96-104). mina-rust consumes these verbatim (`decode_gates_file`,
// mina-rust/crates/ledger/src/proofs/provers.rs:38-49). So the blobs ARE Mina's canonical circuits,
// already serialized: the wrap gate list is a DOWNLOAD, not a derivation.
//
// THE ONE NUMBER. kimchi's `CryptoDigest` (proof-systems/utils/src/hasher.rs) is
//     sha256( b"kimchi-circuit0" || bcs::to_bytes(Circuit{public_input_size, gates}) )
// and the OCaml constraint-system digest is `Md5.digest_bytes` of those 32 bytes
// (mina/src/lib/crypto/kimchi_backend/common/plonk_constraint_system.ml:1071-1075). A candidate gate
// list is byte-exact iff that md5 matches. THE BLOB FILENAMES CARRY THAT MD5 — o1-labs put it there —
// so recomputing it from the JSON is a diff against an INDEPENDENT source, not a pin against our own
// definition. Measured: all four blobs reproduce their own filename hash.
//
// REFERENCE (independent of us):  the md5 in the o1-labs release-asset FILENAME
//                              +  `ROWS` / `PRIMARY_LEN` transcribed by openmina into
//                                 mina-rust/crates/ledger/src/proofs/constants.rs
// CANDIDATE (computed here):     BCS-reserialize the blob JSON -> sha256 -> md5, and count the gates.
//
// ⚠ WHAT IS AND IS NOT CANONICAL. Verified at source (see docs/PICKLES-SYNTHESIS-EPOCH-SCOPE.md):
// a zkApp account stores the *wrap* VK (`wrap_index` = 28 column commitments), and `wrap_main` bakes
// the STEP vk commitments in as circuit CONSTANTS (mina/src/lib/pickles/wrap_main.ml:215-219,
// `Inner_curve.constant`), so the wrap circuit is PER-ZKAPP and a stock node has NO canonical-wrap
// check. These blobs are therefore the byte target for reproducing *Mina's own* transaction/blockchain
// wrap — the reference implementation of `wrap_main` — not a VK a third party must match.
//
// USAGE
//   node scripts/mina-canonical-circuit-oracle.mjs                     # all pinned circuits, green-or-bust
//   node scripts/mina-canonical-circuit-oracle.mjs --self-test         # + prove the digest goes RED
//   node scripts/mina-canonical-circuit-oracle.mjs --circuit wrap-transaction
//   node scripts/mina-canonical-circuit-oracle.mjs --circuit wrap-transaction --dump out.json
//   node scripts/mina-canonical-circuit-oracle.mjs --circuit wrap-transaction --candidate lean.json
//        ^ gate-by-gate diff of a Lean-emitted gate list against the canonical blob (localizes the
//          first divergence; the digest above is the total statement).
//
// Blobs resolve like mina-rust does (circuit_blobs.rs:126-152): $MINA_CIRCUIT_BLOBS_BASE_DIR, then
// ~/.mina/circuit-blobs, else fetched from the o1-labs release and cached there.
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runOracle } from './diff-oracle.mjs';

// ── GateType declaration order == the BCS variant index.
// mina/src/lib/crypto/proof-systems/kimchi/src/circuits/gate.rs `pub enum GateType`.
const GATE_TYPES = [
  'Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar',
  'Lookup', 'CairoClaim', 'CairoInstruction', 'CairoFlags', 'CairoTransition',
  'RangeCheck0', 'RangeCheck1', 'ForeignFieldAdd', 'ForeignFieldMul', 'Xor16', 'Rot64',
];
const GATE_INDEX = new Map(GATE_TYPES.map((n, i) => [n, i]));
const PERMUTS = 7; // kimchi/src/circuits/wires.rs:12

// ── The pinned circuit set. `md5` is lifted from the o1-labs asset FILENAME; `rows`/`primary` from
// mina-rust/crates/ledger/src/proofs/constants.rs (openmina's independent transcription).
const RELEASE_TAG = 'berkeley-devnet'; // mina-rust/crates/core/src/network.rs:162 `directory_name`
const CIRCUITS = {
  'wrap-transaction': {
    stem: 'wrap-wrap-proving-key-transaction-snark-b9a01295c8cc9bda6d12142a581cd305',
    md5: 'b9a01295c8cc9bda6d12142a581cd305', rows: 15122, primary: 40, // WrapTransactionProof
    note: 'canonical wrap_main, Tock/Fq — also the wrap for every zkapp branch (WrapZkapp*Proof reuse it)',
    vk: 'mina-devnet-wrap-transaction-vk.json',
  },
  'wrap-blockchain': {
    stem: 'wrap-wrap-proving-key-blockchain-snark-bbecaf158ca543ec8ac9e7144400e669',
    md5: 'bbecaf158ca543ec8ac9e7144400e669', rows: 14657, primary: 40, // WrapBlockProof
    note: 'a SECOND independently-compiled wrap_main — its non-Generic gate STREAM is identical',
    vk: 'mina-devnet-wrap-blockchain-vk.json',
  },
  'step-transaction': {
    stem: 'step-step-proving-key-transaction-snark-transaction-0-c33ec5211c07928c87e850a63c6a2079',
    md5: 'c33ec5211c07928c87e850a63c6a2079', rows: 17806, primary: 67, // StepTransactionProof
    note: 'step branch 0, Tick/Fp — app logic + the fixed step scaffolding',
  },
  'step-zkapp-proved': {
    stem: 'step-step-proving-key-transaction-snark-proved-4-0cafcbc6dffccddbc82f8c2519c16341',
    md5: '0cafcbc6dffccddbc82f8c2519c16341', rows: 20023, primary: 67, // StepZkappProvedProof
    note: 'step branch 4 — the one that runs `verify_one` on a side-loaded proof',
  },
};

// ── BCS. bcs::to_bytes over serde: usize->u64 LE, seq->ULEB128 len + elems, fixed array->no len,
// unit-variant enum->ULEB128 index, Vec<F> under `SerdeAs`->serialize_bytes (ULEB128 32 + 32 LE bytes).
function uleb128(n) {
  const out = [];
  for (;;) { const b = n & 0x7f; n >>>= 7; if (n) out.push(b | 0x80); else { out.push(b); return Buffer.from(out); } }
}
const u64le = (n) => { const b = Buffer.alloc(8); b.writeBigUInt64LE(BigInt(n)); return b; };

function bcsCircuit(publicInputSize, gates) {
  const parts = [u64le(publicInputSize), uleb128(gates.length)];
  for (const g of gates) {
    const idx = GATE_INDEX.get(g.typ);
    if (idx === undefined) throw new Error(`unknown GateType ${JSON.stringify(g.typ)}`);
    parts.push(uleb128(idx));
    if (g.wires.length !== PERMUTS) throw new Error(`PERMUTS=${PERMUTS}, gate has ${g.wires.length} wires`);
    for (const w of g.wires) { parts.push(u64le(w.row)); parts.push(u64le(w.col)); }
    parts.push(uleb128(g.coeffs.length));
    for (const c of g.coeffs) { const raw = Buffer.from(c, 'hex'); parts.push(uleb128(raw.length), raw); }
  }
  return Buffer.concat(parts);
}

export function circuitDigest(publicInputSize, gates) {
  const sha = createHash('sha256').update(Buffer.from('kimchi-circuit0')).update(bcsCircuit(publicInputSize, gates)).digest();
  return { sha256: sha.toString('hex'), md5: createHash('md5').update(sha).digest('hex') };
}

export function histogram(gates) {
  const h = new Map();
  for (const g of gates) h.set(g.typ, (h.get(g.typ) ?? 0) + 1);
  return h;
}

// ── Blob resolution, mirroring mina-rust/crates/ledger/src/proofs/circuit_blobs.rs.
function blobPath(stem) {
  const rel = join(RELEASE_TAG, `${stem}_gates.json`);
  for (const base of [process.env.MINA_CIRCUIT_BLOBS_BASE_DIR, join(homedir(), '.mina', 'circuit-blobs'),
                      '/usr/local/lib/mina/circuit-blobs']) {
    if (base && existsSync(join(base, rel))) return join(base, rel);
  }
  return null;
}

async function loadBlob(stem) {
  const hit = blobPath(stem);
  if (hit) return JSON.parse(readFileSync(hit, 'utf8'));
  const rel = join(RELEASE_TAG, `${stem}_gates.json`);
  const url = `https://github.com/o1-labs/circuit-blobs/releases/download/${RELEASE_TAG}/${stem}_gates.json`;
  process.stderr.write(`   fetching ${url}\n`);
  const res = await fetch(url);
  if (!res.ok) throw new Error(`circuit-blobs fetch failed: HTTP ${res.status} for ${url}`);
  const text = await res.text();
  const cache = join(homedir(), '.mina', 'circuit-blobs', rel);
  mkdirSync(dirname(cache), { recursive: true });
  writeFileSync(cache, text);
  return JSON.parse(text);
}

export async function loadCircuit(key) {
  const spec = CIRCUITS[key];
  if (!spec) throw new Error(`unknown circuit ${key}; known: ${Object.keys(CIRCUITS).join(', ')}`);
  const blob = await loadBlob(spec.stem);
  return { spec, publicInputSize: blob.public_input_size, gates: blob.gates };
}

// ── The WRAP VK. openmina ships Mina's real wrap verifier indices as JSON (mina-rust/crates/ledger/
// src/proofs/data/devnet_{transaction,blockchain}_verifier_index.json); `fixtures/` holds a byte copy
// so this oracle does not require the co-tenant checkout. `vkChecks` is a genuine cross-source diff:
// `public` comes from openmina's VK, `public_input_size` from o1-labs' gate blob.
const VK_PINS = { // the wrap shape that is genuinely fixed, per mina/src/lib/pickles/common.ml + impls.ml:219
  public: 40, prev_challenges: 2, zk_rows: 3, max_poly_size: 32768, domain_log2: 14,
  sigma_comm: 7, coefficients_comm: 15, // + generic/psm/complete_add/mul/emul/endomul_scalar = 28 points
};
const VK_SHA256 = { // pinned so a silent upstream VK swap is RED, not invisible
  'mina-devnet-wrap-transaction-vk.json': 'a61a861a471f631ff176ef290921885400001be11e3ea4d49af0a0292ef5549f',
  'mina-devnet-wrap-blockchain-vk.json': '062b7183c4af80ab74cca9c9d0dd6f6031654d22ae94d6ce7310e66b72cdf626',
};
const MINA_RUST_VK = { // drift guard against the co-tenant checkout, when it is present
  'mina-devnet-wrap-transaction-vk.json': 'devnet_transaction_verifier_index.json',
  'mina-devnet-wrap-blockchain-vk.json': 'devnet_blockchain_verifier_index.json',
};

function loadVk(name) {
  const path = new URL(`../fixtures/${name}`, import.meta.url);
  const raw = readFileSync(path);
  const sha = createHash('sha256').update(raw).digest('hex');
  if (sha !== VK_SHA256[name]) throw new Error(`wrap VK ${name} sha256 ${sha} != pinned ${VK_SHA256[name]}`);
  const upstream = join(homedir(), 'dev', 'mina-rust', 'crates', 'ledger', 'src', 'proofs', 'data', MINA_RUST_VK[name]);
  if (existsSync(upstream)) {
    const up = createHash('sha256').update(readFileSync(upstream)).digest('hex');
    if (up !== sha) throw new Error(`wrap VK DRIFT: fixtures/${name} != ${upstream} (${sha} vs ${up})`);
  }
  const vk = JSON.parse(raw.toString('utf8'));
  // ark Radix2EvaluationDomain postcard/hex head: u64 size then u32 log_size_of_group.
  vk._domain_size = Number(BigInt('0x' + Buffer.from(vk.domain.slice(0, 16), 'hex').reverse().toString('hex')));
  vk._domain_log2 = Number(BigInt('0x' + Buffer.from(vk.domain.slice(16, 24), 'hex').reverse().toString('hex')));
  return vk;
}

// ── The gate-by-gate vector, for `--candidate` localization.
function gateVector(gates, limit = Infinity) {
  const v = [];
  for (let i = 0; i < gates.length && v.length < limit; i++) {
    const g = gates[i];
    v.push({ name: `g${i}.typ`, value: g.typ });
    for (let j = 0; j < g.wires.length; j++) v.push({ name: `g${i}.w${j}`, value: `${g.wires[j].row},${g.wires[j].col}` });
    for (let k = 0; k < g.coeffs.length; k++) v.push({ name: `g${i}.c${k}`, value: g.coeffs[k] });
  }
  return v;
}

// ── main
// `isMain` gates every ACTION below so that `import { loadCircuit } from './mina-canonical-circuit-
// oracle.mjs'` gets the blob resolver as a LIBRARY (stepmain-region-conformance.mjs uses it) instead
// of running the whole oracle — four blobs, 46 MB, and a `process.exit` — as an import side effect.
// Same pattern `diff-oracle.mjs` already uses for its CLI.
const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
const argv = process.argv.slice(2);
const arg = (flag) => { const i = argv.indexOf(flag); return i >= 0 ? argv[i + 1] : undefined; };
const only = arg('--circuit');
const candidatePath = arg('--candidate');
const dumpPath = arg('--dump');
const keys = only ? [only] : Object.keys(CIRCUITS);

if (isMain && dumpPath) {
  const { spec, publicInputSize, gates } = await loadCircuit(keys[0]);
  const d = circuitDigest(publicInputSize, gates);
  writeFileSync(dumpPath, JSON.stringify({ circuit: keys[0], stem: spec.stem, public_input_size: publicInputSize,
    gates: gates.length, digest_sha256: d.sha256, digest_md5: d.md5,
    histogram: Object.fromEntries([...histogram(gates)].sort((a, b) => b[1] - a[1])), gate_list: gates }, null, 0));
  process.stderr.write(`   dumped ${gates.length} gates -> ${dumpPath}\n`);
  process.exit(0);
}

if (isMain && candidatePath) {
  // Localizing mode: diff a candidate gate list (e.g. a Lean emission) against the canonical blob.
  const { publicInputSize, gates } = await loadCircuit(keys[0]);
  const cand = JSON.parse(readFileSync(candidatePath, 'utf8'));
  // Accept a raw kimchi blob (`{public_input_size, gates:[...]}`), this script's `--dump`
  // (`{gates: <count>, gate_list:[...]}`), or a bare array. `gates` is only the gate list when it IS
  // one — in a `--dump` it is the COUNT, and silently diffing a number against 199k entries is the
  // shape of an oracle that reports RED for the wrong reason.
  const candGates = Array.isArray(cand) ? cand
    : Array.isArray(cand.gate_list) ? cand.gate_list
    : Array.isArray(cand.gates) ? cand.gates
    : (() => { throw new Error(`${candidatePath}: no gate list (expected .gates[] or .gate_list[] or a bare array)`); })();
  await runOracle({
    shape: 'gates',
    label: `mina canonical ${keys[0]} vs ${candidatePath} (gate-by-gate)`,
    reference: () => [{ name: 'public_input_size', value: publicInputSize }, ...gateVector(gates)],
    candidate: () => [{ name: 'public_input_size', value: cand.public_input_size ?? publicInputSize }, ...gateVector(candGates)],
  });
}

// Default mode: recompute each pinned circuit's shape + digest from the blob bytes and diff against
// the o1-labs filename md5 + openmina's constants.rs rows/primary.
const loaded = [];
if (isMain) for (const k of keys) loaded.push([k, await loadCircuit(k)]);

const reference = () => {
  const v = [];
  for (const [k, { spec }] of loaded) {
    v.push({ name: `${k}.public_input_size`, value: spec.primary });
    v.push({ name: `${k}.gates`, value: spec.rows });
    v.push({ name: `${k}.digest_md5`, value: spec.md5 });
    if (spec.vk) { // openmina's shipped wrap VK is the SECOND source for the wrap's fixed shape
      v.push({ name: `${k}.vk.public`, value: VK_PINS.public });
      v.push({ name: `${k}.vk.prev_challenges`, value: VK_PINS.prev_challenges });
      v.push({ name: `${k}.vk.zk_rows`, value: VK_PINS.zk_rows });
      v.push({ name: `${k}.vk.max_poly_size`, value: VK_PINS.max_poly_size });
      v.push({ name: `${k}.vk.domain_log2`, value: VK_PINS.domain_log2 });
      v.push({ name: `${k}.vk.commitment_points`, value: 28 });
    }
  }
  return v;
};
const candidate = () => {
  const v = [];
  for (const [k, { spec, publicInputSize, gates }] of loaded) {
    v.push({ name: `${k}.public_input_size`, value: publicInputSize });
    v.push({ name: `${k}.gates`, value: gates.length });
    v.push({ name: `${k}.digest_md5`, value: circuitDigest(publicInputSize, gates).md5 });
    if (spec.vk) {
      const vk = loadVk(spec.vk);
      const points = vk.sigma_comm.length + vk.coefficients_comm.length +
        ['generic_comm', 'psm_comm', 'complete_add_comm', 'mul_comm', 'emul_comm', 'endomul_scalar_comm']
          .filter((c) => vk[c]).length;
      v.push({ name: `${k}.vk.public`, value: vk.public });
      v.push({ name: `${k}.vk.prev_challenges`, value: vk.prev_challenges });
      v.push({ name: `${k}.vk.zk_rows`, value: vk.zk_rows });
      v.push({ name: `${k}.vk.max_poly_size`, value: vk.max_poly_size });
      v.push({ name: `${k}.vk.domain_log2`, value: vk._domain_log2 });
      v.push({ name: `${k}.vk.commitment_points`, value: points });
      // the circuit must FIT its VK domain: rows + zk_rows <= 2^log2 (kimchi's own capacity rule)
      if (gates.length + vk.zk_rows > vk._domain_size) {
        throw new Error(`${k}: ${gates.length} gates + ${vk.zk_rows} zk_rows exceeds VK domain ${vk._domain_size}`);
      }
    }
  }
  return v;
};

// The falsifiers that make this a GATE and not a report: each one perturbs the canonical gate list by
// the smallest possible amount and DEMANDS the digest move. A digest insensitive to a bent coefficient,
// a moved wire, or a changed public-input count would be decoration.
const extra = () => {
  const [, { publicInputSize, gates }] = loaded[0];
  const good = circuitDigest(publicInputSize, gates).md5;
  const bite = (label, mutate) => {
    const copy = gates.map((g) => ({ typ: g.typ, wires: g.wires.map((w) => ({ ...w })), coeffs: [...g.coeffs] }));
    const pi = mutate(copy, publicInputSize);
    const got = circuitDigest(pi ?? publicInputSize, copy).md5;
    if (got === good) throw new Error(`RED-PATH FAILED: ${label} did not move the digest (${got})`);
    process.stdout.write(`   red-path OK: ${label} -> ${got.slice(0, 12)}… != ${good.slice(0, 12)}…\n`);
  };
  // one flipped bit in one coefficient of one gate
  bite('flip 1 bit of gates[0].coeffs[0]', (g) => {
    const i = g.findIndex((x) => x.coeffs.length > 0);
    const b = Buffer.from(g[i].coeffs[0], 'hex'); b[0] ^= 1; g[i].coeffs[0] = b.toString('hex');
  });
  // one moved wire
  bite('move gates[0].wires[0].row by 1', (g) => { g[0].wires[0].row += 1; });
  // one changed gate type
  bite('retype the last gate', (g) => { const l = g[g.length - 1]; l.typ = l.typ === 'Zero' ? 'Generic' : 'Zero'; });
  // one changed public-input count
  bite('public_input_size + 1', (_g, pi) => pi + 1);
  // one dropped gate
  bite('drop the last gate', (g) => { g.pop(); });

  for (const [k, { spec, publicInputSize, gates }] of loaded) {
    const h = [...histogram(gates)].sort((a, b) => b[1] - a[1]);
    const nonGeneric = gates.length - (histogram(gates).get('Generic') ?? 0);
    process.stdout.write(`   ${k}: pi=${publicInputSize} gates=${gates.length} nonGeneric=${nonGeneric} ` +
      `md5=${spec.md5}\n      ${h.map(([t, c]) => `${t}=${c}`).join(' ')}\n`);
  }
};

if (isMain) {
  await runOracle({
    shape: 'gates',
    label: `mina canonical circuits (${keys.join(', ')}) — recomputed digest vs o1-labs asset md5 + openmina constants.rs`,
    reference,
    candidate,
    extra,
  });
}
