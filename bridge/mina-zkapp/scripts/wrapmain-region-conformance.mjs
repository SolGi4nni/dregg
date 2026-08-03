// wrapmain-region-conformance.mjs — the WRAP-side region diff: the Lean-assembled `wrap_main`
// sub-circuits against Mina's own compiled `wrap-transaction`, gate by gate.
//
// ⚑ WHAT THIS IS, AND WHY IT IS NOT `stepmain-region-conformance.mjs` WITH A DIFFERENT ARGUMENT.
// The step diff is hard-wired to `step-zkapp-proved`, to the Fp modulus (its line 126), and to a
// step-specific ledger. The wrap circuit lives in a DIFFERENT FIELD (`wrap_main_inputs.ml:4,6` —
// `Me = Tock`, `Impl = Impls.Wrap`, so coefficients are mod `qN`), on a DIFFERENT CURVE (Vesta as
// the inner curve; the proof itself is Pallas-committed), with a DIFFERENT PRIMARY_LEN (40), and its
// gadget anchors are different objects. All four are swapped here; the METHOD — base-free gadget
// signatures, so no alignment window and no pairing is ever chosen — is the step diff's and is
// reused deliberately.
//
// ⚑⚑ AND THE WRAP SIDE HAS A SECOND SOURCE THE STEP SIDE NEVER HAD. `wrap-blockchain` is an
// INDEPENDENTLY COMPILED `wrap_main` (a different step circuit, a different VK baked in by
// `wrap_main.ml:215-220`) whose NON-GENERIC gate stream is identical to `wrap-transaction`'s. So
// every non-Generic conformance fact below is checked against BOTH blobs, and a fact that holds for
// one and not the other is a RED — it would mean the fact is about one zkApp's wrap and not about
// `wrap_main`.
//
// ⚠ WRAP IS PER-ZKAPP, SO THE BLOB IS A SHAPE REFERENCE AND NOT A BYTE TARGET.
// `wrap_main.ml:215-219` bakes the per-branch step VK commitments in as `Inner_curve.constant`, so
// no Lean emission can be byte-equal to a particular zkApp's wrap. What CAN be compared, and is:
// which gadget bodies Snarky emits, in what run lengths, in what proportion — the ~95% of the
// circuit that is invariant across the two blobs.
//
// ⚠ AND THE HONEST HEADLINE: four sub-circuits of `wrap_main` are assembled today (the Fq
// transcript, `to_field_checked`, the branch selection, the public tie). The four gate FAMILIES
// that carry `wrap-transaction`'s curve work — VarBaseMul 2417, EndoMul 2528, CompleteAdd 492 and
// most of Generic 3521 — are W-XHAT / W-FTCOMM / W-COMBINE / W-BULLET and are NOT emitted. This
// diff reports that as ABSENT REGIONS with their measured Mina sizes, so the gap is a number in the
// report rather than a silence.
//
// USAGE
//   node scripts/wrapmain-region-conformance.mjs                 # green-or-bust
//   node scripts/wrapmain-region-conformance.mjs --report        # the per-region verdict, readable
//   node scripts/wrapmain-region-conformance.mjs --lean <path>   # a specific rung emission
//   node scripts/wrapmain-region-conformance.mjs --falsify       # prove the diff BITES
//
// The Lean side defaults to `/tmp/pickles-wrapmain/wrapmain_wrap_w4_bind.json`, produced by
//   (cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)

import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
const PERMUTS = 7;
// ⚑ Tock/Fq — the VESTA base / PALLAS scalar prime, the wrap circuit's own field
// (`curves/src/pasta/fields/fq.rs`). The step diff uses `pN`; using it here would silently
// re-interpret every negative coefficient.
const FQ = 28948022309329048855892746252171976963363056481941647379679742748393362948097n;
const FP = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;

const LEAN_DEFAULT = '/tmp/pickles-wrapmain/wrapmain_wrap_w4_bind.json';

const fq = (c) => { let v = BigInt(c) % FQ; if (v < 0n) v += FQ; return v.toString(); };
const leHex = (h) => BigInt('0x' + Buffer.from(h, 'hex').reverse().toString('hex')).toString();

const small = (v) => (v === 0n ? '0' : v < 100n ? v.toString() : v > FQ - 100n ? `-${FQ - v}` : 'K');
const famKey = (h) => {
  const v = h.map(BigInt);
  const lead = v.find((x) => x !== 0n);
  const n = lead !== undefined && lead > FQ / 2n ? v.map((x) => (x === 0n ? 0n : FQ - x)) : v;
  return n.map(small).join(' ');
};

// ── loading ───────────────────────────────────────────────────────────────────────────────────────
function normalizeMina(pi, gates) {
  return {
    pi,
    gates: gates.map((g) => ({
      typ: g.typ,
      wires: g.wires.map((w) => ({ row: w.row, col: w.col })),
      coeffs: g.coeffs.map(leHex),
    })),
  };
}

/** The Lean emission: ordinal→name, `[row,col]`→`{row,col}`, signed decimals→[0,q). `raw` keeps the
 *  σ-only probe rows; `gates` has them SPLICED OUT of the permutation cycles, because a probe row is
 *  this file's instrument and not a gadget Snarky emits — leaving them in would make every gadget
 *  signature that touches one diverge for a reason that is about the test. */
function normalizeLean(j) {
  const raw = j.gates.map((g) => ({
    typ: NAMES[g.typ],
    wires: g.wires.map(([row, col]) => ({ row, col })),
    coeffs: g.coeffs.map(fq),
  }));
  for (const g of raw) if (g.wires.length !== PERMUTS) throw new Error(`PERMUTS=${PERMUTS}, gate has ${g.wires.length} wires`);
  const probe = new Set(j.probe_rows ?? []);
  const remap = new Array(raw.length).fill(-1);
  let n = 0;
  const keep = [];
  for (let i = 0; i < raw.length; i++) if (!probe.has(i)) { remap[i] = n++; keep.push(i); }
  const gates = keep.map((r) => ({
    typ: raw[r].typ,
    coeffs: raw[r].coeffs,
    wires: raw[r].wires.map((w) => {
      let t = w;
      for (let guard = 0; probe.has(t.row); guard++) {
        t = raw[t.row].wires[t.col];
        if (guard > raw.length) throw new Error('permutation cycle is probes only');
      }
      return { row: remap[t.row], col: t.col };
    }),
  }));
  return { pi: j.public_input_size, gates, raw, probe, name: j.name };
}

function loadLeanSide(explicit) {
  const live = explicit ?? LEAN_DEFAULT;
  if (!existsSync(live))
    throw new Error(`no Lean wrap emission at ${live}. Produce it with\n` +
      '   (cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)');
  return { src: live, j: JSON.parse(readFileSync(live, 'utf8')) };
}

// ── gadget instances ──────────────────────────────────────────────────────────────────────────────
function runsOf(G, kind) {
  const o = []; let i = 0;
  while (i < G.length) {
    if (G[i].typ === kind) { let n = 0; while (G[i + n] && G[i + n].typ === kind) n++; o.push({ s: i, n }); i += n; }
    else i++;
  }
  return o;
}
function vbmLadders(G) {
  const o = []; let i = 0;
  while (i < G.length) {
    if (G[i].typ === 'VarBaseMul' && G[i + 1] && G[i + 1].typ === 'Zero') {
      let n = 0;
      while (G[i + 2 * n] && G[i + 2 * n].typ === 'VarBaseMul' && G[i + 2 * n + 1] && G[i + 2 * n + 1].typ === 'Zero') n++;
      o.push({ s: i, chunks: n, len: 2 * n }); i += 2 * n;
    } else i++;
  }
  return o;
}

/** THE SIGNATURE — base-free, so no alignment window and no pairing is ever chosen. Each of the 7·n
 *  permutation cells is classified SELF / IN r,c / EXT and no absolute row survives. */
function signature(G, base, len, withCoeffs) {
  const o = [];
  for (let d = 0; d < len; d++) {
    const r = base + d, g = G[r];
    o.push(g.typ);
    if (withCoeffs) o.push(g.coeffs.join(','));
    for (let j = 0; j < PERMUTS; j++) {
      const w = g.wires[j];
      o.push(w.row === r && w.col === j ? 'SELF' : (w.row >= base && w.row < base + len) ? `${w.row - base}.${w.col}` : 'EXT');
    }
  }
  return o.join('/');
}
const sigDigest = (s) => createHash('sha256').update(s).digest('hex').slice(0, 16);
const cellClass = (G, base, len, d, j) => {
  const r = base + d, w = G[r].wires[j];
  return w.row === r && w.col === j ? 'SELF' : (w.row >= base && w.row < base + len) ? `IN ${w.row - base},${w.col}` : 'EXT';
};
function localize(MG, mb, LG, lb, len, withCoeffs) {
  const out = [];
  for (let d = 0; d < len; d++) {
    if (MG[mb + d].typ !== LG[lb + d].typ) out.push(`+${d}.typ ${MG[mb + d].typ}→${LG[lb + d].typ}`);
    if (withCoeffs && MG[mb + d].coeffs.join(',') !== LG[lb + d].coeffs.join(','))
      out.push(`+${d}.coeffs DIFFER`);
    for (let j = 0; j < PERMUTS; j++) {
      const a = cellClass(MG, mb, len, d, j), b = cellClass(LG, lb, len, d, j);
      if (a !== b) out.push(`+${d}.w${j} ${a}→${b}`);
    }
  }
  return out;
}

// ── ⚑ THE DIVERGENCE LEDGER ───────────────────────────────────────────────────────────────────────
// One entry per difference between the Lean wrap assembly and Mina's own `wrap_main`.
//   `why`    — the `KimchiWrapMain.lean` §13 sub-circuit it belongs to, or `UNRECORDED`, which means
//              it is on NO list and is therefore an unrecorded simplification or a defect.
//   `expect` — the divergence's exact MEASURED FORM, so a divergence that grows, shrinks or changes
//              character is RED even though its key is still here.
// RED three ways: a divergence with no entry; an entry no longer observed (a stale allowance); an
// entry whose form moved.
const LEDGER = {
  'absent/VarBaseMul': {
    why: '§13 W-XHAT + W-FTCOMM',
    expect: 'mina 2417 rows / lean 0',
    note: "wrap's x_hat MSM is 67 scalars at widths 15×255 · 40×128 · 12×1 (the STEP statement's 57 "
      + 'packed words, with each of the 10 `Field` words split by `wrap_main.ml:69-81` into a 255-bit '
      + 'value and a 1-bit parity); plus `Common.ft_comm`\'s eight 51-chunk ladders.',
  },
  'absent/EndoMul': {
    why: '§13 W-COMBINE + W-BULLET',
    expect: 'mina 2528 rows / lean 0',
    note: '`Split_commitments.combine` over 47 commitments (N45 + prevs) and `bullet_reduce` over 16 '
      + 'rounds, each round an `endo_inv` AND an `endo` — two 32-block ladders (`scalar_challenge.ml:'
      + '343-354`).',
  },
  'absent/CompleteAdd': {
    why: '§13 W-XHAT + W-COMBINE + W-BULLET',
    expect: 'mina 492 rows / lean 0',
    note: 'every `Ops.add_fast` is one CompleteAdd row; all of them belong to the three absent MSM/fold regions.',
  },
  'poseidon/count': {
    why: '§13 W-KEY + W-FINALIZE + W-WRAPHACK',
    expect: 'mina 261 permutations / lean 61',
    note: "the transcript sponge of `wrap_verifier.ml:516-646` is assembled; `sponge_after_index` "
      + '(W-KEY, ~29), the two `finalize_other_proof` sponges (W-FINALIZE) and the two '
      + '`hash_messages_for_next_wrap_proof` sponges (W-WRAPHACK) are not.',
  },
  'ems/count': {
    why: '§13 W-FINALIZE + W-PREV + the 16-bit width',
    expect: 'mina 19 chains of 8 / lean 42',
    note: 'ours are `lowest_128_bits`\' two halves per challenge. Upstream also runs '
      + '`assert_n_bits ~n:16` (`wrap_main.ml:208`, a 1-row chain) and `finalize_other_proof`\'s own '
      + 'ξ′/r′ lifts, which are W-PREV and W-FINALIZE.',
  },
  'pi/width': {
    why: '§10 census — 22 of Mina\'s 40 wrap statement words are derived here',
    expect: 'mina 40 / lean 22',
    note: 'the 18 not exposed are wrap slots 0–4, 9 (W-FINALIZE), 11–12 (W-WRAPHACK) and 30–39 (the '
      + '8 feature-flag Bools and the lookup `Opt`\'s two words, which `spec.ml:190-195` lays out '
      + 'even at `Flag.No`). Exposing them as undERIVED witnesses would be a public vector of fixtures.',
  },
  'ems/seam': {
    why: "§13 \"two places this file is stricter than upstream\" — the to_field_checked seam",
    expect: '3 cells: +0.w2 IN 0,3->EXT   +7.w4 SELF->EXT   +7.w5 SELF->EXT',
    note: 'the BODY (rows 1..6) is byte-identical on 42/42 instances; the two seams are real and '
      + 'named. (a) upstream `a0` and `b0` are ONE cell — `scalar_challenge.ml:63-66` seeds both at '
      + '`Field.of_int 2`, so Snarky gives them one constant Cvar, where we pin two variables. '
      + '(b) upstream leaves `a8`/`b8` SELF, i.e. UNWIRED: `Field.(scale a endo + b)` '
      + '(`scalar_challenge.ml:136`) is a Cvar linear combination that Snarky folds into whatever '
      + 'consumes it and emits NO row, where we emit an explicit lift row. Both are "stricter than '
      + 'upstream", not less constrained — and neither may be claimed as row-count conformance.',
  },
  'generic/shape-families': {
    why: "§13 \"two places this file is stricter than upstream\" + row economy",
    expect: '381/528 match | x89 [0 0 0 0 0] | x46 [1 -1 0 0 0] | x4 [1 16 -1 0 0] '
      + '| x2 [0 0 1 1 -1] | x2 [1 4 -1 0 0] | x1 [1 0 -1 -1 0] | x1 [1 0 -1 0 -1] '
      + '| x1 [1 3 -1 0 0] | x1 [16 0 -1 0 0]',
    note: 'Generic selector halves this assembly emits whose SHAPE FAMILY (constants collapsed to K, '
      + 'sign-normalized) Snarky never emits in `wrap-transaction`, ATTRIBUTED ONE BY ONE: '
      + '[0 0 0 0 0] = the empty second half of an odd `packHalves` run (a row-economy cost, not a '
      + 'constraint); [1 -1 0 0 0] = our `cEq` ties, which Snarky expresses by UNIONING the two '
      + 'variables in one sigma class instead of spending a row; [1 16 -1 0 0] [1 3 -1 0 0] '
      + '[16 0 -1 0 0] [1 4 -1 0 0] = the two `Pseudo.choose` folds and `Branch_data.Checked.pack`, '
      + 'which upstream emits as ZERO rows because their coefficients are constants and '
      + '`Checked.mul` takes its `Constant` branch (`utils.ml:81-88`); [1 0 -1 0 -1] [1 0 -1 -1 0] = '
      + "`ones_vector`'s `value <- value && not (...)` recurrence (`util.ml:57-60`), likewise a Cvar "
      + 'linear combination upstream; [0 0 1 1 -1] = `Field.equal`\'s `z_inv*z = 1 - r` '
      + '(`utils.ml:44-48`), which Snarky DOES constrain but renders through `assert_r1cs` into a '
      + 'differently-arranged Generic half. Every one is this file being STRICTER or spending a row '
      + 'where Snarky spends none — none is a missing constraint. See §13\'s "stricter than '
      + 'upstream" note.',
  },
};

// ── the measurement ───────────────────────────────────────────────────────────────────────────────
function measure(M, M2, L) {
  const MG = M.gates, MG2 = M2.gates, LG = L.gates;
  const R = { conform: [], diverge: [], regions: [], absent: [] };
  const conform = (name, ref, cand) => R.conform.push({ name, ref, cand });
  const diverge = (key, form) => R.diverge.push({ key, form });

  // (0) ⚑ THE SECOND SOURCE. `wrap-blockchain` is an independently compiled `wrap_main`; its
  // NON-GENERIC stream must equal `wrap-transaction`'s or every fact below is about one zkApp.
  const nonGeneric = (G) => G.filter((g) => g.typ !== 'Generic');
  const ngA = nonGeneric(MG), ngB = nonGeneric(MG2);
  conform('two-blobs/non-generic-count', ngA.length, ngB.length);
  conform('two-blobs/non-generic-typ-stream',
    createHash('sha256').update(ngA.map((g) => g.typ).join(',')).digest('hex').slice(0, 16),
    createHash('sha256').update(ngB.map((g) => g.typ).join(',')).digest('hex').slice(0, 16));
  conform('two-blobs/non-generic-coeffs',
    createHash('sha256').update(ngA.map((g) => g.coeffs.join('|')).join(';')).digest('hex').slice(0, 16),
    createHash('sha256').update(ngB.map((g) => g.coeffs.join('|')).join(';')).digest('hex').slice(0, 16));
  conform('two-blobs/public-input-size', M.pi, M2.pi);

  // (0b) ⚑ THE FIELD. A wrap coefficient reduced mod p would be a different element; this is the
  // tripwire that the emission is Fq and not a step-side one relabelled. Every Lean coefficient that
  // is "small negative" must be small-negative in Fq, i.e. `q - c` and not `p - c`.
  // ⚠ THE HONEST FORM OF THIS CHECK. There is no intrinsic way to tell an Fq element from an Fp one
  // by looking at it — both primes are 255 bits — so "is this mod q" cannot be asserted directly.
  // What CAN be asserted is (a) every coefficient is in range, and (b) NO coefficient is the mod-p
  // image of a small negative, which is what a step-side emission relabelled as wrap would contain.
  // The bite that closes the rest is `--falsify`'s "a coefficient reduced mod p instead of mod q",
  // which moves the Generic family census; and the Poseidon whole-digest below is the positive
  // evidence, since it matches Mina's own fq_kimchi constants byte for byte.
  const allLean = LG.flatMap((g) => g.coeffs).map(BigInt);
  conform('field/coeffs-in-range', true, allLean.every((c) => c >= 0n && c < FQ));
  conform('field/no-mod-p-small-negatives', true,
    !allLean.some((c) => c > FP - 1000n && c < FP));
  conform('field/modulus', FQ.toString(), FQ.toString());

  // (1) the public input block — kimchi puts PRIMARY_LEN Generic rows first on both sides.
  conform('pi/rows-are-Generic',
    MG.slice(0, M.pi).every((g) => g.typ === 'Generic'),
    LG.slice(0, L.pi).every((g) => g.typ === 'Generic'));
  if (M.pi !== L.pi) diverge('pi/width', `mina ${M.pi} / lean ${L.pi}`);

  // (2) GADGET SIGNATURE SETS — alignment-free.
  const fams = [
    { key: 'Poseidon', co: true, core: null,
      m: runsOf(MG, 'Poseidon').map((r) => ({ s: r.s, len: 11, n: r.n })),
      l: runsOf(LG, 'Poseidon').map((r) => ({ s: r.s, len: 11, n: r.n })) },
    { key: 'EMS8', co: false, core: [1, 6],
      m: runsOf(MG, 'EndoMulScalar').filter((r) => r.n === 8).map((r) => ({ s: r.s, len: 8 })),
      l: runsOf(LG, 'EndoMulScalar').filter((r) => r.n === 8).map((r) => ({ s: r.s, len: 8 })) },
  ];
  for (const f of fams) {
    if (f.key === 'Poseidon') {
      // A Poseidon run that is not 11 rows would mean the permutation is not one gadget on one side.
      const bad = (G, w) => runsOf(G, 'Poseidon').filter((r) => r.n % 11 !== 0).length ? `${w} has a non-multiple-of-11 Poseidon run` : 'ok';
      conform('gadget/Poseidon/runs-are-permutations', 'ok', bad(LG, 'lean'));
      conform('gadget/Poseidon/runs-are-permutations-mina', 'ok', bad(MG, 'mina'));
      // ⚑ A kimchi Poseidon gate reads the NEXT row's cols 0,1,2 as its output state, so a
      // permutation is ELEVEN Poseidon rows plus a closing row that HOLDS that state. Pinning that
      // the closing row is a `Zero` on both sides is what makes the 11-row window a gadget and not
      // an arbitrary slice — and deleting the closing row reds here rather than silently merging
      // two permutations into one 22-row run.
      const closers = (G) => {
        const o = new Set();
        for (const r of runsOf(G, 'Poseidon')) for (let k = 11; k <= r.n; k += 11)
          o.add(G[r.s + k] ? G[r.s + k].typ : 'END');
        return [...o].sort().join(',');
      };
      conform('gadget/Poseidon/closing-row-type', closers(MG), closers(LG));
      // upstream packs consecutive permutations into one run; split them back into 11-row units
      f.m = runsOf(MG, 'Poseidon').flatMap((r) => Array.from({ length: r.n / 11 }, (_, k) => ({ s: r.s + 11 * k, len: 11 })));
      f.l = runsOf(LG, 'Poseidon').flatMap((r) => Array.from({ length: r.n / 11 }, (_, k) => ({ s: r.s + 11 * k, len: 11 })));
    }
    const ms = new Map(), ls = new Map();
    for (const u of f.m) { const k = signature(MG, u.s, u.len, f.co); ms.set(k, (ms.get(k) ?? 0) + 1); }
    for (const u of f.l) { const k = signature(LG, u.s, u.len, f.co); ls.set(k, (ls.get(k) ?? 0) + 1); }
    let hit = 0; for (const [k, c] of ls) if (ms.has(k)) hit += c;
    const rec = { key: f.key, mina: f.m.length, lean: f.l.length, mClasses: ms.size, lClasses: ls.size, hit, positions: [] };
    if (hit !== f.l.length && f.m.length && f.l.length) {
      const lRep = f.l[0];
      let best = null;
      for (const u of f.m) {
        const d = localize(MG, u.s, LG, lRep.s, lRep.len, f.co);
        if (!best || d.length < best.d.length) best = { u, d };
      }
      rec.positions = best.d.slice(0, 12);
      // ⚑ The WHOLE-instance mismatch is a first-class divergence, so the seam is LEDGERED and a
      // seam that moves is red — not a number that only appears in the readable report.
      if (f.key === 'EMS8')
        diverge('ems/seam', `${best.d.length} cells: ${best.d.join('   ').replace(/→/g, '->')}`);
    }
    if (f.core && f.m.length && f.l.length) {
      const [a, b] = f.core;
      const csig = (G, u) => { const o = []; for (let d = a; d <= b; d++) { const r = u.s + d, g = G[r]; o.push(g.typ); for (let j = 0; j < PERMUTS; j++) o.push(cellClass(G, u.s, u.len, d, j)); } return o.join('/'); };
      const mc = new Map(); for (const u of f.m) mc.set(csig(MG, u), (mc.get(csig(MG, u)) ?? 0) + 1);
      const lc = new Map(); for (const u of f.l) lc.set(csig(LG, u), (lc.get(csig(LG, u)) ?? 0) + 1);
      let ch = 0; for (const [k, c] of lc) if (mc.has(k)) ch += c;
      rec.coreHit = ch; rec.coreRows = `${a}..${b}`;
      const ours = [...lc.keys()].sort((x, y) => lc.get(y) - lc.get(x))[0];
      // ⚑ THE CROSS-SOURCE ENTRY: the digest of the MINA body class our body matches, against ours.
      // Byte-equal iff the gadget body Snarky emits and the one Lean emits are the same object.
      conform(`gadget/${f.key}/body-digest[rows ${a}..${b}]`,
        mc.has(ours) ? sigDigest(ours) : `NO MINA BODY CLASS MATCHES (mina has ${mc.size})`,
        sigDigest(ours));
      conform(`gadget/${f.key}/instances-with-that-body`, `${f.l.length}/${f.l.length}`, `${ch}/${f.l.length}`);
    } else if (f.m.length && f.l.length) {
      const ours = [...ls.keys()].sort((x, y) => ls.get(y) - ls.get(x))[0];
      conform(`gadget/${f.key}/whole-digest[11 rows + 15 coeffs/row]`,
        ms.has(ours) ? sigDigest(ours) : `NO MINA CLASS MATCHES (mina has ${ms.size})`, sigDigest(ours));
      conform(`gadget/${f.key}/instances-with-that-signature`, `${f.l.length}/${f.l.length}`, `${hit}/${f.l.length}`);
    }
    R.regions.push(rec);
  }

  // (3) ABSENT REGIONS — the families Mina spends rows on that this assembly does not emit at all.
  // Reported as a NUMBER, per the ledger, so the gap cannot read as a silence.
  const cen = (G) => { const h = {}; for (const g of G) h[g.typ] = (h[g.typ] ?? 0) + 1; return h; };
  const cm = cen(MG), cl = cen(LG);
  for (const k of ['VarBaseMul', 'EndoMul', 'CompleteAdd']) {
    R.absent.push({ family: k, mina: cm[k] ?? 0, lean: cl[k] ?? 0 });
    if ((cl[k] ?? 0) === 0 && (cm[k] ?? 0) > 0) diverge(`absent/${k}`, `mina ${cm[k]} rows / lean 0`);
  }
  R.census = { mina: cm, lean: cl };
  if ((cl.Poseidon ?? 0) !== (cm.Poseidon ?? 0))
    diverge('poseidon/count', `mina ${(cm.Poseidon ?? 0) / 11} permutations / lean ${(cl.Poseidon ?? 0) / 11}`);
  const mEms = runsOf(MG, 'EndoMulScalar').filter((r) => r.n === 8).length;
  const lEms = runsOf(LG, 'EndoMulScalar').filter((r) => r.n === 8).length;
  if (mEms !== lEms) diverge('ems/count', `mina ${mEms} chains of 8 / lean ${lEms}`);
  // Every EndoMulScalar run upstream, by width — the `to_field_checked` widths §13 names as missing.
  R.emsWidths = {
    mina: [...new Set(runsOf(MG, 'EndoMulScalar').map((r) => r.n))].sort((a, b) => a - b).join(','),
    lean: [...new Set(runsOf(LG, 'EndoMulScalar').map((r) => r.n))].sort((a, b) => a - b).join(','),
  };
  conform('gadget/EMS/lean-widths-are-a-subset-of-minas', true,
    [...new Set(runsOf(LG, 'EndoMulScalar').map((r) => r.n))]
      .every((n) => runsOf(MG, 'EndoMulScalar').some((r) => r.n === n)));

  // (4) GENERIC SELECTOR HALVES — the comparable unit is the HALF, because a kimchi Generic row is
  // double (`coeffs[0..4]` over cols 0,1,2 and `coeffs[5..9]` over 3,4,5).
  const halves = (G, from) => {
    const o = [];
    for (let r = from; r < G.length; r++) if (G[r].typ === 'Generic') {
      o.push(G[r].coeffs.slice(0, 5)); o.push(G[r].coeffs.slice(5, 10));
    }
    return o;
  };
  const mFam = new Set(halves(MG, M.pi).map(famKey));
  const lHalves = halves(LG, L.pi);
  const missing = new Map();
  let famIn = 0;
  for (const h of lHalves) {
    const k = famKey(h);
    if (mFam.has(k)) famIn++; else missing.set(k, (missing.get(k) ?? 0) + 1);
  }
  R.generic = { famIn, famOut: lHalves.length - famIn, total: lHalves.length,
    minaFamilies: mFam.size, missing: [...missing.entries()].sort((a, b) => b[1] - a[1]) };
  // ⚑ The form carries the COUNTS, not just the family keys: a Generic half that changes shape,
  // appears or disappears must move this entry, or the diff would be blind to Generic churn in the
  // regions Mina has no counterpart for.
  if (missing.size)
    diverge('generic/shape-families',
      `${famIn}/${lHalves.length} match | ` +
      [...missing.entries()].sort((a, b) => b[1] - a[1] || (a[0] < b[0] ? -1 : 1))
        .map(([k, c]) => `x${c} [${k}]`).join(' | '));

  return R;
}

// ── green-or-bust vectors ─────────────────────────────────────────────────────────────────────────
const referenceVector = (R) => [
  ...R.conform.map((c) => ({ name: `conform:${c.name}`, value: String(c.ref) })),
  ...Object.entries(LEDGER).map(([k, v]) => ({ name: `ledger:${k}`, value: `${v.why} :: ${v.expect}` })),
];
const candidateVector = (R) => {
  const seen = new Map(R.diverge.map((d) => [d.key, d.form]));
  const v = R.conform.map((c) => ({ name: `conform:${c.name}`, value: String(c.cand) }));
  for (const k of Object.keys(LEDGER))
    v.push({ name: `ledger:${k}`, value: seen.has(k) ? `${LEDGER[k].why} :: ${seen.get(k)}` : 'NOT OBSERVED — stale allowance, retire it' });
  for (const d of R.diverge) if (!(d.key in LEDGER)) v.push({ name: `UNLEDGERED:${d.key}`, value: d.form });
  return v;
};

// ── report ────────────────────────────────────────────────────────────────────────────────────────
function report(R, src, M, L) {
  const pct = (a, b) => (b ? `${(100 * a / b).toFixed(2)}%` : '—');
  console.log(`\n╔═ WRAP_MAIN REGION CONFORMANCE — Lean wrap assembly vs Mina wrap-transaction (Tock/Fq)`);
  console.log(`║  mina: ${M.gates.length} gates, PI ${M.pi}     lean: ${L.gates.length} probe-free rows (+${L.probe.size} σ-probes), PI ${L.pi}`);
  console.log(`║  lean source: ${src}   (${L.name})`);
  console.log(`║  ⚠ wrap is PER-ZKAPP (\`wrap_main.ml:215-219\` bakes the step VKs in), so this is a SHAPE`);
  console.log(`║    conformance, never a byte target. The second blob, wrap-blockchain, is the cross-check.`);
  console.log('╚═\n');

  console.log('── (0) TWO INDEPENDENTLY COMPILED wrap_main BLOBS');
  for (const c of R.conform.filter((c) => c.name.startsWith('two-blobs/')))
    console.log(`   ${String(c.ref) === String(c.cand) ? '✓' : '✗'} ${c.name.padEnd(38)} ${c.ref} vs ${c.cand}`);

  console.log('\n── (1) GATE CENSUS');
  console.log('   family           mina    lean   note');
  for (const k of NAMES) {
    const m = R.census.mina[k] ?? 0, l = R.census.lean[k] ?? 0;
    const note = l === 0 && m > 0 ? '⚠ ABSENT — see the ledger' : (l ? '' : '—');
    console.log(`   ${k.padEnd(14)} ${String(m).padStart(6)}  ${String(l).padStart(6)}   ${note}`);
  }

  console.log('\n── (2) GADGET SIGNATURE SETS — alignment-free: is the instance we emit one Mina emits?');
  console.log('   family    ours  mina | mina classes | WHOLE instance conforms | gadget BODY (seam excluded)');
  for (const f of R.regions) {
    console.log(`   ${f.key.padEnd(9)} ${String(f.lean).padStart(4)} ${String(f.mina).padStart(5)} | ${String(f.mClasses).padStart(12)} | ${String(`${f.hit}/${f.lean}  ${pct(f.hit, f.lean)}`).padStart(23)} | ${(f.coreRows ? `rows ${f.coreRows}` : 'whole, +coeffs').padEnd(14)} ${f.coreHit === undefined ? `${f.hit}/${f.lean}  ${pct(f.hit, f.lean)}` : `${f.coreHit}/${f.lean}  ${pct(f.coreHit, f.lean)}`}`);
    if (f.positions.length) console.log(`      SEAM (vs the closest Mina class): ${f.positions.join('   ')}`);
  }
  console.log(`   to_field_checked widths (EndoMulScalar run lengths)`);
  console.log(`              mina ${R.emsWidths.mina}`);
  console.log(`              lean ${R.emsWidths.lean}`);

  console.log('\n── (3) ABSENT REGIONS — what wrap_main spends rows on that this assembly does not emit');
  for (const a of R.absent)
    console.log(`   ${a.family.padEnd(14)} mina ${String(a.mina).padStart(5)} rows   lean ${a.lean}   → ${LEDGER[`absent/${a.family}`]?.why ?? 'UNRECORDED'}`);

  console.log('\n── (4) GENERIC SELECTOR HALVES (by SHAPE FAMILY: constants → K, sign-normalized)');
  console.log(`   ${R.generic.famIn}/${R.generic.total} of our halves match a family Snarky emits (${R.generic.minaFamilies} families upstream)`);
  for (const [k, c] of R.generic.missing) console.log(`      ×${String(c).padStart(4)}  [${k}]`);

  console.log('\n── (5) DIVERGENCES, classified against KimchiWrapMain.lean §13');
  const un = [];
  for (const d of R.diverge) {
    const l = LEDGER[d.key];
    if (!l || l.why === 'UNRECORDED') un.push(d.key);
    console.log(`   ${(l && l.why === 'UNRECORDED' ? '⚠ ' : '  ')}${d.key}`);
    console.log(`       ${l ? l.why : '⚠ NOT IN THE LEDGER'}`);
    console.log(`       measured: ${d.form}`);
    if (l) console.log(`       ${l.note}`);
  }
  if (un.length) {
    console.log(`\n   ⚑ ${un.length} DIVERGENCE(S) ARE NOT ATTRIBUTED TO A §13 SUB-CIRCUIT: ${un.join(', ')}`);
    console.log('     Each is either an unrecorded simplification (→ name it in §13) or a defect.');
  }
  console.log();
}

// ── the RED PATH: prove the diff bites ────────────────────────────────────────────────────────────
function falsify(M, M2, leanJson) {
  const bites = [];
  const run = (label, mutate) => {
    const j = JSON.parse(JSON.stringify(leanJson));
    mutate(j);
    let after;
    try { after = JSON.stringify(candidateVector(measure(M, M2, normalizeLean(j)))); }
    catch (e) { bites.push([label, `THREW: ${String(e.message).slice(0, 70)}`]); return; }
    bites.push([label, after !== base ? 'MOVED' : '⚠ DID NOT MOVE']);
  };
  const base = JSON.stringify(candidateVector(measure(M, M2, normalizeLean(leanJson))));

  run('a Poseidon round constant bent by one', (j) => {
    const g = j.gates.find((x) => x.typ === 2);
    g.coeffs[0] = (BigInt(g.coeffs[0]) + 1n).toString();
  });
  run('a Poseidon row re-wired to itself', (j) => {
    const i = j.gates.findIndex((x) => x.typ === 2);
    j.gates[i].wires[0] = [i, 0];
  });
  run('an EndoMulScalar chain broken (row 1 unhooked from row 0)', (j) => {
    const i = j.gates.findIndex((x, k) => x.typ === 6 && j.gates[k + 1]?.typ === 6);
    if (i < 0) throw new Error('no EndoMulScalar pair to break');
    j.gates[i + 1].wires[0] = [i + 1, 0];
  });
  run('one Generic half given a shape Snarky never emits', (j) => {
    // ⚠ PAST THE PUBLIC-INPUT BLOCK. The PI rows are excluded from the half census on both sides
    // (kimchi emits them itself), so a bite aimed there would be free.
    const i = j.gates.findIndex((x, k) => x.typ === 1 && k >= j.public_input_size + 2);
    if (i < 0) throw new Error('no circuit-body Generic row to bend');
    j.gates[i].coeffs[0] = '7'; j.gates[i].coeffs[1] = '9'; j.gates[i].coeffs[2] = '11';
  });
  run('the public input width changed', (j) => { j.public_input_size = j.public_input_size + 1; });
  run('a gate type changed (Generic → Zero): the half leaves the census', (j) => {
    const i = j.gates.findIndex((x, k) => x.typ === 1 && k > j.public_input_size + 5);
    j.gates[i].typ = 0;
  });
  run("a Poseidon permutation's closing Zero row deleted", (j) => {
    const i = j.gates.findIndex((x, k) => x.typ === 2 && j.gates[k + 11] && j.gates[k + 11].typ !== 2);
    if (i < 0) throw new Error('no Poseidon permutation with a closing row');
    j.gates.splice(i + 11, 1);
    j.num_rows -= 1;
    j.probe_rows = (j.probe_rows ?? []).filter((r) => r !== i + 11).map((r) => (r > i + 11 ? r - 1 : r));
    for (const g of j.gates) for (const w of g.wires) if (w[0] > i + 11) w[0] -= 1;
  });
  run('a coefficient reduced mod p instead of mod q', (j) => {
    const g = j.gates.find((x) => x.typ === 1 && x.coeffs.some((c) => BigInt(c) < 0n));
    if (!g) throw new Error('no negative Generic coefficient to re-reduce');
    const k = g.coeffs.findIndex((c) => BigInt(c) < 0n);
    g.coeffs[k] = (FP + BigInt(g.coeffs[k])).toString();
  });

  console.log('\n── RED PATH: does this diff bite?');
  let bad = 0;
  for (const [l, v] of bites) { console.log(`   ${v === 'MOVED' ? 'ok  ' : 'RED '} ${l.padEnd(58)} ${v}`); if (v !== 'MOVED') bad++; }
  if (bad) { console.log(`\nRED-PATH FAILED: ${bad} bite(s) did not move the vector.`); process.exitCode = 1; }
  else console.log(`\n   ${bites.length} bites, all MOVED the candidate vector.`);
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };

const a = await loadCircuit('wrap-transaction');
const b = await loadCircuit('wrap-blockchain');
const M = normalizeMina(a.publicInputSize, a.gates);
const M2 = normalizeMina(b.publicInputSize, b.gates);
const { src, j: leanJson } = loadLeanSide(arg('--lean'));
const L = normalizeLean(leanJson);
const R = measure(M, M2, L);

if (argv.includes('--report')) { report(R, src, M, L); if (argv.includes('--falsify')) falsify(M, M2, leanJson); process.exit(process.exitCode ?? 0); }

const ref = referenceVector(R), cand = candidateVector(R);
const byName = new Map(ref.map((e) => [e.name, e.value]));
let fails = 0;
for (const e of cand) {
  const r = byName.get(e.name);
  if (r === undefined) { console.log(`RED  ${e.name}\n     UNEXPECTED: ${e.value}`); fails++; }
  else if (r !== e.value) { console.log(`RED  ${e.name}\n     ref:  ${r}\n     cand: ${e.value}`); fails++; }
}
for (const e of ref) if (!cand.some((c) => c.name === e.name)) { console.log(`RED  ${e.name}\n     MISSING from the candidate vector`); fails++; }
if (argv.includes('--falsify')) falsify(M, M2, leanJson);
if (fails) { console.log(`\nwrapmain-region-conformance: ${fails} FAILURE(S) over ${cand.length} entries`); process.exit(1); }
console.log(`wrapmain-region-conformance: ${cand.length} entries conform (2 independently compiled wrap_main blobs cross-checked)`);
