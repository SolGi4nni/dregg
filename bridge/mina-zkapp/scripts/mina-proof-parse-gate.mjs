// MINA PROOF PARSE GATE — does Mina's OWN Pickles proof reader accept a proof object WE ENCODED?
//
// This is the proof-side twin of `mina-vk-parse-gate.mjs`. That one asked whether Mina's reader
// accepts a VERIFICATION KEY we derived; this one asks the same question of a PROOF OBJECT.
//
// WHAT A PICKLES PROOF IS ON THE WIRE — and there are TWO encodings, which is the thing to get
// right before anything else.
//
//   * **binprot.** What a block's `protocolStateProof` carries, what the p2p wire carries, what a
//     zkApp account update carries. Read by openmina's
//     `PicklesProofProofsVerified2ReprStableV2::binprot_read` and by Mina's OCaml `bin_read_t`.
//   * **sexp, base64'd.** What o1js `Proof.toJSON().proof` is and what `Proof.fromJSON` consumes.
//     `Pickles.proofOfBase64(str, maxProofsVerified)` (o1js `dist/node/lib/proof-system/proof.js:71`,
//     bindings `o1js_node.bc.cjs:427447`) dispatches to `Proof0/1/2[9]`, i.e.
//     `Pickles.Proof.Proofs_verified_{0,1,2}.of_base64` — Mina's OCaml sexp reader.
//
//   MEASURED, not assumed: base64-decoding the `proof` field of o1js's own
//   `bridge/mina-zkapp/.fullchain/proof-5.json` yields ASCII
//   `((statement((proof_state((deferred_values((plonk((alpha((inner(8e9cfc28d401d846 …`.
//   It is an S-expression. It is NOT binprot. The two encodings carry the SAME record — openmina's
//   `PicklesProofProofsVerified2ReprStableV2` (`generated.rs:1016-1020`: statement / prev_evals /
//   proof) — in two different grammars.
//
// WHAT THIS GATE IS FOR. `metatheory/fixtures/pickles-extractors/src/bin/pickles_proof_wire.rs`
// emits both. Its binprot half is judged by BYTE IDENTITY against seven real block proofs. Its
// sexp half cannot be judged that way (no real Mina proof reaches us in sexp), so it is judged
// HERE, by handing it to Mina's own reader.
//
// ⚑ WHAT A GREEN HERE DOES AND DOES NOT MEAN. `proofOfBase64` PARSES. It reconstructs the record,
// which means every field is present, in order, in range, and every curve point is ON THE CURVE
// (the OCaml reader rejects otherwise). It does NOT verify: no VK is consulted, no public input
// is checked, no pairing/IPA is run. A green here is "the object is well-formed Pickles", exactly
// as `vkToCircuit` returning was "the key is well-formed", and no more.
//
// USAGE
//   node scripts/mina-proof-parse-gate.mjs --proof <o1js-proof.json> [--proof …]   # the gate
//   node scripts/mina-proof-parse-gate.mjs --dir /tmp/pickles-proof-wire           # every one in a dir
//   node scripts/mina-proof-parse-gate.mjs --self-test                             # red path only
//
// A `--proof` file is `{ "maxProofsVerified": n, "proof": "<base64 sexp>" }`; extra keys ignored.

import { readFileSync, existsSync, readdirSync } from 'node:fs';
import { pathToFileURL, fileURLToPath } from 'node:url';
import path from 'node:path';

// o1js's package `exports` hides its internals and `Pickles` is one of them. Resolve the package
// directory by walking up, exactly as the VK gate does.
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

await imp('dist/node/index.js');
// ⚑ keep the NAMESPACE. `Pickles` is a module-scope `let` that `initializeBindings()` reassigns;
// a destructured copy snapshots `undefined` and every call then fails with the same shape a
// malformed proof produces — which would make the red path pass for the wrong reason.
const bindings = await imp('dist/node/bindings.js');
await bindings.initializeBindings();
if (typeof bindings.Pickles?.proofOfBase64 !== 'function') {
  throw new Error('o1js bindings did not expose Pickles.proofOfBase64; refusing to run a gate that cannot go green');
}

// ---- argv ----
const argv = process.argv.slice(2);
const proofPaths = [];
let selfTest = false;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '--proof') proofPaths.push(argv[++i]);
  else if (argv[i] === '--dir') {
    const d = argv[++i];
    for (const f of readdirSync(d).sort()) {
      if (f.endsWith('.o1js-proof.json')) proofPaths.push(path.join(d, f));
    }
  } else if (argv[i] === '--self-test') selfTest = true;
  else throw new Error('unknown argument ' + argv[i]);
}

/** Hand a base64 sexp to Mina's own reader. Returns {ok, proof} or {ok:false, err}. */
function parse(b64, maxProofsVerified) {
  try {
    const r = bindings.Pickles.proofOfBase64(b64, maxProofsVerified);
    return { ok: true, mlProof: r };
  } catch (e) {
    return { ok: false, err: String(e?.message ?? e) };
  }
}


// ─────────────────────────────────────────────────────────────────────────────────────────────
// ⚑ THE ON-CURVE PASS — the class NEITHER reader checks.
//
// `Pickles.proofOfBase64` and openmina's `binprot_read` both reconstruct a curve point from two
// bare `BigInt`s and never ask whether the pair is a POINT. This gate measured that itself, in the
// `curve-point-y-zeroed (off-curve)` line below, and then filed it as informative — a documented
// wound, not a detected one. It cost a real defect: our marshaller emitted
// `messages_for_next_wrap_proof.challenge_polynomial_commitment` as a PALLAS point where Mina reads
// VESTA, both readers passed it, and `verify_zkapp` ABORTED THE PROCESS on
// `Affine::<VestaParameters>::new`'s on-curve assertion (2026-08-05).
//
// So the check lives here now, and it is green-or-bust.
//
// WHICH CURVE EACH FIELD IS, measured against real block proofs (`mina_verdict`, on
// `metatheory/fixtures/mina-blocks/devnet-540890` and `mainnet-541858`):
//   * `statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment` — the
//     STEP proof's accumulator the next WRAP consumes, Tick ⇒ **VESTA**. openmina
//     `proofs/accumulator_check.rs:44-53` (`Vesta::of_coordinates`) and
//     `StatementProofState::try_from` (`proofs/step.rs`).
//   * every other point in a wrap proof — `w_comm`, `z_comm`, `t_comm`, `lr`, `delta`, `sg`, and
//     `messages_for_next_step_proof.challenge_polynomial_commitments` (`InnerCurve<Fp>`,
//     `proofs/verification.rs:444`) — Tock ⇒ **PALLAS**.
// Both curves are y^2 = x^3 + 5; only the base field differs, which is exactly why a wrong-group
// value is invisible to anything that does not do the arithmetic.
const PALLAS_P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001n;
const VESTA_Q  = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001n;
const onCurve = (x, y, m) => x < m && y < m && (y * y - (x * x * x + 5n)) % m === 0n;

/** Every `(0xHEX 0xHEX)` tuple in the sexp, with its offset. */
function tuplesOf(sexp) {
  const out = [];
  const re = /\(0x([0-9A-F]{64}) 0x([0-9A-F]{64})\)/g;
  let m;
  while ((m = re.exec(sexp)) !== null) {
    out.push({ at: m.index, x: BigInt('0x' + m[1]), y: BigInt('0x' + m[2]) });
  }
  return out;
}

/**
 * ⚠ A `(0xA 0xB)` tuple is NOT necessarily a point. `evaluations` prints every `PointEvaluations`
 * as the bare pair `(zeta zeta_omega)` — same grammar, two field elements, and the absent ones are
 * `(0 0)`, which is on neither curve. So the check is REGION-SCOPED and says how many tuples it
 * deliberately did not look at; a blanket sweep would be 100% false positives on a real proof, and
 * a gate that cries wolf is one nobody reads.
 *
 * Returns {checked, skipped, vestaFound, bad}.
 */
function curveCheck(b64) {
  const sexp = Buffer.from(b64, 'base64').toString('binary');
  const tuples = tuplesOf(sexp);
  const at = (needle, from = 0) => sexp.indexOf(needle, from);

  const mfnw = at('messages_for_next_wrap_proof');
  const mfns = at('messages_for_next_step_proof');
  const mfnsEnd = mfns < 0 ? -1 : at('old_bulletproof_challenges', mfns);
  const comms = at('(commitments(');
  const evals = at('(evaluations(');
  const bullet = at('(bulletproof(');

  // The single Vesta field: the first tuple at or after `messages_for_next_wrap_proof(`.
  const vestaAt = mfnw < 0 ? -1 : (tuples.find((t) => t.at > mfnw)?.at ?? -1);

  const region = (t) => {
    if (t.at === vestaAt) return ['Vesta', 'statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment'];
    if (mfns >= 0 && mfnsEnd > mfns && t.at > mfns && t.at < mfnsEnd)
      return ['Pallas', `statement.messages_for_next_step_proof.challenge_polynomial_commitments[] @${t.at}`];
    if (comms >= 0 && evals > comms && t.at > comms && t.at < evals)
      return ['Pallas', `proof.commitments.{w_comm,z_comm,t_comm} @${t.at}`];
    if (bullet >= 0 && t.at > bullet)
      return ['Pallas', `proof.bulletproof.{lr,delta,challenge_polynomial_commitment} @${t.at}`];
    return [null, null]; // an `evaluations` pair or a statement scalar — not a point
  };

  const bad = [];
  let checked = 0;
  let skipped = 0;
  for (const t of tuples) {
    const [expected, field] = region(t);
    if (expected === null) {
      skipped++;
      continue;
    }
    checked++;
    const onP = onCurve(t.x, t.y, PALLAS_P);
    const onV = onCurve(t.x, t.y, VESTA_Q);
    if (!(expected === 'Vesta' ? onV : onP)) {
      bad.push({ field, expected, onPallas: onP, onVesta: onV });
    }
  }
  return { checked, skipped, vestaFound: vestaAt >= 0, bad };
}

/** Mina's own PRINTER, the inverse of `proofOfBase64`. */
function print(mlProof) {
  return bindings.Pickles.proofToBase64(mlProof);
}

let failed = 0;

for (const p of proofPaths) {
  const j = JSON.parse(readFileSync(p, 'utf8'));
  const mpv = j.maxProofsVerified ?? 2;
  const b64 = j.proof;
  const r = parse(b64, mpv);
  const name = path.basename(p);
  if (!r.ok) {
    failed++;
    console.log(`[parse] ${name.padEnd(42)} mpv=${mpv} b64=${b64.length}  REFUSED: ${r.err}`);
    continue;
  }
  // ⚑ THE STRONGER MEASUREMENT. Parsing proves the object is well-formed. Re-PRINTING it with
  // Mina's own printer and comparing to what we handed in proves our printer IS Mina's printer,
  // character for character — the sexp-side analogue of the binprot byte-identity round-trip.
  let echo, threw = null;
  try {
    echo = print(r.mlProof);
  } catch (e) {
    echo = null;
    threw = (e && e.message) || String(e);
  }
  if (echo === null) {
    // ⚑ THIS USED TO BE `ACCEPTED (re-print threw)` WITH NO `failed++`, and the polarity was
    // INVERTED against the branch below: a re-print that merely DIFFERS counted as a failure, while
    // a re-print that THREW — the strictly worse outcome, our object is not printable by Mina's own
    // printer at all — was logged green. The header two lines up calls the re-print "THE STRONGER
    // MEASUREMENT"; the throw path deleted it. (2026-08-03)
    failed++;
    console.log(`[parse] ${name.padEnd(42)} mpv=${mpv} b64=${b64.length}  RE-PRINT THREW — Mina's own printer `
      + `cannot render the object it just parsed: ${String(threw).replace(/\s+/g, ' ').slice(0, 160)}`);
  } else if (echo === b64) {
    console.log(`[parse] ${name.padEnd(42)} mpv=${mpv} b64=${b64.length}  ACCEPTED + RE-PRINT BYTE-IDENTICAL`);
  } else {
    // Not a failure of the gate's stated milestone (it parsed), but it is the thing to look at.
    const a = Buffer.from(b64, 'base64').toString('binary');
    const c = Buffer.from(echo, 'base64').toString('binary');
    let at = 0;
    while (at < Math.min(a.length, c.length) && a[at] === c[at]) at++;
    failed++;
    console.log(
      `[parse] ${name.padEnd(42)} mpv=${mpv} b64=${b64.length}  ACCEPTED but RE-PRINT DIFFERS at sexp offset ${at}` +
      `\n         ours: ${JSON.stringify(a.slice(Math.max(0, at - 40), at + 60))}` +
      `\n         mina: ${JSON.stringify(c.slice(Math.max(0, at - 40), at + 60))}`
    );
  }

  // ⚑ green-or-bust, on every proof, whatever the re-print said
  const cc = curveCheck(b64);
  if (!cc.vestaFound) {
    failed++;
    console.log(`[curve] ${name.padEnd(42)} RED — no \`messages_for_next_wrap_proof\` in the record; cannot say which point is the Vesta one`);
  } else if (cc.bad.length === 0) {
    console.log(`[curve] ${name.padEnd(42)} ${String(cc.checked).padStart(3)} points ALL ON THEIR EXPECTED CURVE (1 Vesta, ${cc.checked - 1} Pallas); ${cc.skipped} evaluation pairs not points, not checked`);
  } else {
    failed++;
    console.log(`[curve] ${name.padEnd(42)} RED — ${cc.bad.length} of ${cc.checked} points are not on the curve Mina reads them as:`);
    for (const b of cc.bad) {
      console.log(`         ${b.field}`);
      console.log(`           expected ${b.expected};  on Pallas = ${b.onPallas}, on Vesta = ${b.onVesta}`);
    }
  }
}

// ---- the red path. A gate that cannot go red is not a gate. ----
if (selfTest || proofPaths.length > 0) {
  const must = [];
  // 1. garbage that is not even a sexp
  must.push(['not-a-sexp', Buffer.from('this is not an s-expression').toString('base64'), 2]);
  // 2. a well-formed sexp of the WRONG shape
  must.push(['wrong-shape', Buffer.from('((statement())(prev_evals())(proof()))').toString('base64'), 2]);
  const informative = [];
  if (proofPaths.length > 0) {
    const j = JSON.parse(readFileSync(proofPaths[0], 'utf8'));
    const mpv = j.maxProofsVerified ?? 2;
    const raw = Buffer.from(j.proof, 'base64').toString('binary');
    const b64of = (s) => Buffer.from(s, 'binary').toString('base64');
    // 3. the same proof read at the WRONG proofs_verified arity
    must.push(['real-proof-at-arity-0', j.proof, 0]);
    // 4. a STRUCTURAL bend: delete one closing paren
    const cut = raw.lastIndexOf(')', raw.length - 2);
    must.push(['one-paren-deleted', b64of(raw.slice(0, cut) + raw.slice(cut + 1)), mpv]);
    // 5. truncated at 80%
    must.push(['truncated-80pct', b64of(raw.slice(0, Math.floor(raw.length * 0.8))), mpv]);
    // 6. a record field RENAMED
    must.push(['field-renamed', b64of(raw.replace('(ft_eval1 ', '(ft_evalX ')), mpv]);

    // ── INFORMATIVE, not must-refuse: these say what the PARSER checks vs what only a
    // VERIFIER would. Reported literally either way; they do not decide the gate.
    // (a) a field element at exactly the Pallas base modulus p — non-canonical.
    const P = '0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001';
    const firstHex = raw.indexOf('0x', raw.indexOf('challenge_polynomial_commitment'));
    informative.push([
      'field-elt-set-to-p (non-canonical)',
      b64of(raw.slice(0, firstHex) + P + raw.slice(firstHex + 66)),
      mpv,
    ]);
    // (b) a curve point moved OFF the curve by zeroing its y coordinate.
    const ZERO = '0x' + '0'.repeat(64);
    const yAt = raw.indexOf('0x', firstHex + 66);
    informative.push([
      'curve-point-y-zeroed (off-curve)',
      b64of(raw.slice(0, yAt) + ZERO + raw.slice(yAt + 66)),
      mpv,
    ]);
  }
  console.log('\n-- RED PATH (each MUST be refused) --');
  for (const [label, b64, mpv] of must) {
    const r = parse(b64, mpv);
    if (r.ok) {
      failed++;
      console.log(`[red]   ${label.padEnd(42)} ACCEPTED — the gate cannot go red on this input`);
    } else {
      console.log(`[red]   ${label.padEnd(42)} refused: ${r.err.replace(/\s+/g, ' ').slice(0, 150)}`);
    }
  }
  if (informative.length) {
    console.log('\n-- WHAT THE PARSER CHECKS vs WHAT ONLY A VERIFIER WOULD (informative; does not decide the gate) --');
    for (const [label, b64, mpv] of informative) {
      const r = parse(b64, mpv);
      console.log(
        r.ok
          ? `[info]  ${label.padEnd(42)} ACCEPTED by the parser — the reader does not do this arithmetic`
          : `[info]  ${label.padEnd(42)} refused by the parser: ${r.err.replace(/\s+/g, ' ').slice(0, 150)}`
      );
      // ⚑ and the same input through OUR on-curve pass, which is the point of having one: whatever
      // the reader does, a bent point must not get past this script.
      const cc = curveCheck(b64);
      const caught = cc.bad.length > 0;
      if (label.startsWith('curve-point-y-zeroed')) {
        if (!caught) {
          failed++;
          console.log(`[red]   ${'on-curve pass vs the bent point'.padEnd(42)} MISSED IT — the on-curve pass cannot go red`);
        } else {
          console.log(`[red]   ${'on-curve pass vs the bent point'.padEnd(42)} CAUGHT it: ${cc.bad[0].field} (expected ${cc.bad[0].expected})`);
        }
      }
    }
  }
}

if (proofPaths.length === 0 && !selfTest) {
  console.error('nothing to do: pass --proof <file> or --dir <dir> or --self-test');
  process.exit(2);
}

console.log(failed === 0 ? '\nPROOF_PARSE_GATE=GREEN' : `\nPROOF_PARSE_GATE=RED (${failed} failures)`);
process.exit(failed === 0 ? 0 : 1);
