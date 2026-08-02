// STEP_MAIN REGION CONFORMANCE — the Lean-assembled `verify_one` against Mina's own compiled step
// circuit, GATE BY GATE, not by run-length.
//
// ## WHAT THIS IS, AND WHAT `stepmain-shape-diff.mjs` COULD NOT SEE
//
// `stepmain-shape-diff.mjs` compares five run-length FAMILIES (Poseidon 11×207, EndoMul 32×76,
// EndoMulScalar 8×51, VarBaseMul 1×1448, CompleteAdd 1×138). A run length cannot see a wrong
// coefficient, a wrong wire, a right-shaped gadget in the wrong place, or a region emitted in the
// wrong order. This script sees all four, at the granularity of ONE GATE: `typ`, `coeffs`, and the
// intra-gadget copy-permutation.
//
// ## ⚑ THE ALIGNMENT, AND WHY IT IS TRUSTWORTHY
//
// Whole-circuit alignment is IMPOSSIBLE and is not attempted: ours is a SUBSET (10,342 rows against
// 20,023 gates), several sub-circuits are unassembled, and our rung order is our own scheduling
// choice, not Snarky's execution order. Subset-ness is a scope statement, never reported as failure.
//
// So the instrument is ALIGNMENT-FREE where it can be, and anchored where it cannot:
//
//   (A) GADGET SIGNATURE SETS — the primary instrument, and it assumes NO pairing at all. A gadget
//       instance (an 11-row Poseidon permutation, a k-chunk `var_base_mul` ladder, a 32-row
//       `Scalar_challenge.endo` block, an 8-row `to_field_checked` chain) is reduced to a SIGNATURE:
//       its gate types, its coefficients, and every one of its 7·n wires classified as
//       SELF (in no permutation class) / IN r,c (a cell of this same instance) / EXT (leaves it).
//       That signature is base-free and order-free. Then: is the signature of each instance WE emit
//       one that MINA also emits? Mina's own instances collapse to 1 signature class for Poseidon,
//       VBM51, VBM26 and EndoMul-32 and 3 for the 8-row EndoMulScalar chain, so the comparison is
//       determinate — there is no pairing to get wrong, and no window to pick.
//   (B) REGION ANCHORS, for the facts a per-gadget signature cannot carry (how many instances, at
//       which widths, in which order). Each anchor is a structurally UNIQUE motif and the script
//       ASSERTS its uniqueness on both sides — an ambiguous anchor is refused, not guessed:
//         * `ft_comm`  = the unique maximal run of EIGHT consecutive 51-chunk ladders (Mina's other
//                        51-chunk runs are of length 5, 3 and 4; ours is the only one at all).
//         * `x_hat`    = the ladder cluster immediately preceding it (gap ≤ 1000 rows).
//         * `ipa`      = the EndoMul-32 blocks, clustered at gap ≤ 100 rows — which on Mina's side
//                        splits exactly into `combine_split_commitments` (46) and `bullet_reduce`
//                        (30), the two upstream functions, summing to our 76.
//
// ## ⚑ THE σ-ONLY PROBE ROWS
//
// The Lean assembly places standalone `Zero` PROBE rows into σ classes so that flipping one isolates
// the wire (`KimchiStepMain.lean`, "THE σ-ONLY PROBES"). Mina has no such rows. A fair structural
// diff removes them — and removing a cell from a permutation CYCLE means RELINKING its predecessor
// to its successor, not dropping the wire. That splice is done here. ⚠ It can turn a cell whose only
// class-mate was a probe into a SELF, so every SELF this script reports as a divergence is
// RE-CONFIRMED against the UNSPLICED emission before it is counted.
//
// ## GREEN OR BUST
//
// The reference vector is (i) facts read off MINA'S blob and (ii) the DIVERGENCE LEDGER below — one
// entry per known-and-classified difference, each tagged with its `KimchiStepMain.lean` simplification
// number or `UNRECORDED`. The candidate vector is what this run MEASURES. It goes RED three ways:
//   * a divergence appears that the ledger does not carry  → an unrecorded simplification, or a bug;
//   * a ledger entry stops being observed                  → a stale allowance, retire it;
//   * a conformance fact moves                             → a gadget stopped matching Mina's.
//
// USAGE
//   node scripts/stepmain-region-conformance.mjs                  # green-or-bust
//   node scripts/stepmain-region-conformance.mjs --self-test      # + the harness red path
//   node scripts/stepmain-region-conformance.mjs --report         # the per-region verdict, readable
//   node scripts/stepmain-region-conformance.mjs --lean <path>    # a specific rung emission
//   node scripts/stepmain-region-conformance.mjs --falsify        # prove the diff bites (6 bites)
//   node scripts/stepmain-region-conformance.mjs --refresh-fixture
//
// The Lean side is `/tmp/pickles-stepmain/stepmain_step_r8_finalize.json` when a `lake env lean --run
// Dregg2/Circuit/Emit/EmitStepMainJson.lean` has been done, else the committed gzip fixture. When BOTH
// exist the LIVE one is measured — and if it differs from the fixture that is a RED of its own
// (`conform:fixture/in-sync-with-live-emission`), so a moved assembly is reported, never scored stale.
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import { runOracle } from './diff-oracle.mjs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`); the Lean emitter
// writes the ORDINAL, the o1-labs blob writes the NAME.
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
const PERMUTS = 7;
// Tick/Fp — the Pallas base field, the step circuit's own. The Lean emitter writes SIGNED decimals
// (`-1`), the blob writes 32-byte LE hex; both are normalized into [0,p) before any comparison.
const FP = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;

const LEAN_DEFAULT = '/tmp/pickles-stepmain/stepmain_step_r8_finalize.json';
const LEAN_FIXTURE = new URL('../fixtures/stepmain-step-r8-finalize-gates.json.gz', import.meta.url);

const fp = (c) => { let v = BigInt(c) % FP; if (v < 0n) v += FP; return v.toString(); };
const leHex = (h) => BigInt('0x' + Buffer.from(h, 'hex').reverse().toString('hex')).toString();

// ── loading ───────────────────────────────────────────────────────────────────────────────────────
function normalizeMina(pi, gates) {
  return { pi, gates: gates.map((g) => ({ typ: g.typ, wires: g.wires.map((w) => ({ row: w.row, col: w.col })), coeffs: g.coeffs.map(leHex) })) };
}

/** The Lean emission: ordinal→name, `[row,col]`→`{row,col}`, signed decimals→[0,p). `raw` keeps the
 *  probe rows; `gates` has them spliced out of the permutation cycles. */
function normalizeLean(j) {
  const raw = j.gates.map((g) => ({ typ: NAMES[g.typ], wires: g.wires.map(([row, col]) => ({ row, col })), coeffs: g.coeffs.map(fp) }));
  for (const g of raw) if (g.wires.length !== PERMUTS) throw new Error(`PERMUTS=${PERMUTS}, gate has ${g.wires.length} wires`);
  const probe = new Set(j.probe_rows ?? []);
  const remap = new Array(raw.length).fill(-1);
  let n = 0;
  const keep = [];
  for (let i = 0; i < raw.length; i++) if (!probe.has(i)) { remap[i] = n++; keep.push(i); }
  const gates = keep.map((r) => ({
    typ: raw[r].typ, coeffs: raw[r].coeffs,
    wires: raw[r].wires.map((w) => {
      let t = w;
      for (let guard = 0; probe.has(t.row); guard++) { // splice: relink through the removed cell
        t = raw[t.row].wires[t.col];
        if (guard > raw.length) throw new Error('permutation cycle is probes only');
      }
      return { row: remap[t.row], col: t.col };
    }),
  }));
  return { pi: j.public_input_size, gates, raw, probe, remap };
}

function loadLeanSide(explicit) {
  const live = explicit ?? LEAN_DEFAULT;
  const haveLive = existsSync(live);
  const haveFix = existsSync(LEAN_FIXTURE);
  if (!haveLive && !haveFix)
    throw new Error(`no Lean emission: neither ${live} nor the committed fixture. Produce it with\n` +
      '   (cd metatheory && lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean)');
  const slim = (j) => JSON.stringify({ name: j.name, public_input_size: j.public_input_size, num_rows: j.num_rows, probe_rows: j.probe_rows, gates: j.gates });
  let src, text;
  if (haveLive) { src = live; text = slim(JSON.parse(readFileSync(live, 'utf8'))); }
  else { src = 'fixture'; text = gunzipSync(readFileSync(LEAN_FIXTURE)).toString('utf8'); }
  // ⚠ NOT a fallback. When both exist the LIVE emission is the truth and is what gets measured — but
  // the two must AGREE, and if they do not the fixture is stale, which is a RED the caller must see
  // (`fixture` in the conform vector) rather than a silently-older shape being scored.
  let fixture = 'absent';
  if (haveLive && haveFix) {
    const a = createHash('sha256').update(text).digest('hex');
    const b = createHash('sha256').update(gunzipSync(readFileSync(LEAN_FIXTURE))).digest('hex');
    fixture = a === b ? 'in sync' :
      `STALE: live ${a.slice(0, 12)}… != fixture ${b.slice(0, 12)}… — the Lean assembly moved; refresh with --refresh-fixture`;
    src = a === b ? `${live} (== fixture)` : `${live} (⚠ FIXTURE STALE)`;
  }
  return { src, fixture, j: JSON.parse(text) };
}

// ── gadget instances ──────────────────────────────────────────────────────────────────────────────
/** maximal runs of one gate type */
function runsOf(G, kind) {
  const o = []; let i = 0;
  while (i < G.length) {
    if (G[i].typ === kind) { let n = 0; while (G[i + n] && G[i + n].typ === kind) n++; o.push({ s: i, n }); i += n; }
    else i++;
  }
  return o;
}
/** maximal runs of (VarBaseMul, Zero) pairs — ONE `var_base_mul` ladder of `chunks` 5-bit chunks
 *  (`plonk_curve_ops.ml:66`, `chunks_needed ~num_bits:(n-1)`). */
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
/** cluster instances by row gap — the region anchor primitive */
function cluster(units, maxGap) {
  const out = []; let cur = null;
  for (const u of units) {
    if (cur && u.s - (cur.at(-1).s + cur.at(-1).len) <= maxGap) cur.push(u);
    else { cur = [u]; out.push(cur); }
  }
  return out;
}

/** The signature: base-free, order-free, and the whole comparable content of one gadget instance. */
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
/** per-cell class, for localizing a signature divergence */
const cellClass = (G, base, len, d, j) => {
  const r = base + d, w = G[r].wires[j];
  return w.row === r && w.col === j ? 'SELF' : (w.row >= base && w.row < base + len) ? `IN ${w.row - base},${w.col}` : 'EXT';
};

/** Where two signature CLASSES differ, cell by cell. Both sides are single-class by construction. */
function localize(MG, mb, LG, lb, len, withCoeffs) {
  const out = [];
  for (let d = 0; d < len; d++) {
    if (MG[mb + d].typ !== LG[lb + d].typ) out.push({ at: `+${d}.typ`, ref: MG[mb + d].typ, cand: LG[lb + d].typ });
    if (withCoeffs && MG[mb + d].coeffs.join(',') !== LG[lb + d].coeffs.join(','))
      out.push({ at: `+${d}.coeffs`, ref: MG[mb + d].coeffs.join(',').slice(0, 40), cand: LG[lb + d].coeffs.join(',').slice(0, 40) });
    for (let j = 0; j < PERMUTS; j++) {
      const a = cellClass(MG, mb, len, d, j), b = cellClass(LG, lb, len, d, j);
      if (a !== b) out.push({ at: `+${d}.w${j}`, ref: a, cand: b });
    }
  }
  return out;
}

// ── ⚑ THE DIVERGENCE LEDGER ───────────────────────────────────────────────────────────────────────
// One entry per difference this diff finds between our emitted `verify_one` and Mina's own.
//   `why`    — the `KimchiStepMain.lean` NAMED SIMPLIFICATION it belongs to, or `UNRECORDED`, which
//              means it is NOT on that list and is therefore an unrecorded simplification or a defect.
//   `expect` — the divergence's exact MEASURED FORM. It is in the diff vector, so the ledger pins the
//              SHAPE of each known difference and not merely its existence: a divergence that grows,
//              shrinks or changes character is RED even though its key is still here.
// RED three ways: a divergence with no entry (an unrecorded one, or a bug); an entry no longer
// observed (a stale allowance); an entry whose form moved.
const LEDGER = {
  'xhat/scalar-widths': {
    why: '#2 per-word MSM scalar widths',
    expect: 'mina 2×1 26×22 51×8 (982 chunks) vs lean 26×38 52×1 (1040)',
    note: 'Mina scales Wrap statement word i by ITS OWN width (`Spec.pack`); ours is uniform `msmChunks`. '
      + "⚑ Mina's measured width vector 8×51 + 22×26 + 1×2 = 982 chunks is #2's transcribed table WORD FOR WORD.",
  },
  'xhat/ladder-seed-unwired': {
    why: 'UNRECORDED',
    expect: '228/228 cells SELF in the UNSPLICED emission (mina: 0)',
    note: "each x_hat ladder's accumulator seed (row+0 cols 2,3 = x0,y0), scalar seed (col 4 = n) and "
      + 'the two leading pad bits (row+1 cols 2,3,4) are in NO permutation class; Mina puts all six in one.',
  },
  'ftcomm/scalar-seed-unwired': {
    why: 'UNRECORDED',
    expect: '8/8 cells SELF in the UNSPLICED emission (mina: 0)',
    note: "each ft_comm ladder's scalar-accumulator seed (row+0 col 4 = n) is in no class; Mina wires it "
      + '(the POINT seed at cols 2,3 IS wired here — §6b does what R3 does not).',
  },
  'ipa/endo-seed-unwired': {
    why: 'UNRECORDED',
    expect: '228/228 cells SELF in the UNSPLICED emission (mina: 0)',
    note: "each `Scalar_challenge.endo` block's accumulator seed (row+0 cols 4,5 = xP,yP) and scalar seed "
      + '(col 6 = n) are in no class; Mina wires 4,5 to the preceding `add_fast` and closes 6 on the block.',
  },
  'tfc/chain-endpoints': {
    why: '#7 endo lift / #1 the `lowest_128_bits` split',
    expect: "51/51 chains outside Mina's 3 classes; core rows 1..6 match 51/51",
    note: "our 8-row `to_field_checked` chain enters and leaves through different cells than Snarky's three "
      + 'chain classes — the (n,a,b) hop pattern matches, the endpoints do not. Mina\'s 18-instance class '
      + 'leaves a₈/b₈ UNWIRED, which is `assert_n_bits` discarding the returned field element (#1).',
  },
  'tfc/widths': {
    why: '#6 one challenge width',
    expect: 'mina 1×2 2×42 4×25 8×28 9×1 12×2 16×3 19×1 22×1 24×1 28×1 32×2 128×1 vs lean 8×51',
    note: 'Mina emits `to_field_checked` at 1/2/4/8/9/12/16/19/22/24/28/32/128 rows; we emit only 8.',
  },
  'generic/selector-shapes-absent-upstream': {
    why: 'UNRECORDED',
    expect: '550/2951 halves in 172 shapes Snarky never emits [3959ab25d543ca45]; top: ×164 [0 0 0 0 0] '
      + '×114 [1 -1 0 0 0] ×55 [0 0 -1 1 -5] ×24 [1 -34028236… -1 0 0] ×16 [0 0 -1 1 1] ×9 [1 1 0 0 0]',
    note: 'Generic selector halves we emit that Snarky NEVER emits — headed by the all-zero half (a row half '
      + 'that constrains nothing) and `1 -1 0 0 0` (equality, which Snarky does by copy-permutation, not a row). '
      + 'The digest covers the WHOLE miss list, so one bent selector coefficient moves it.',
  },
  'probe-rows': {
    why: 'header "THE σ-ONLY PROBES" (not on the #1–#11 list)',
    expect: '399 standalone Zero rows (mina: 0)',
    note: 'standalone `Zero` rows placed into σ classes so a flip isolates the wire. Mina has none. Spliced out here.',
  },
  'scope/unassembled-subcircuits': {
    why: '#5 group_map · equal_g · check_bulletproof `scale_fast` of sg · rule.main',
    expect: 'Poseidon 207/572 VBM51 8/20 ENDO32 76/77',
    note: 'Mina gadget instances with no counterpart here. SUBSET-NESS, not failure — counted so a shrinkage is visible.',
  },
};

// ── the measurement ───────────────────────────────────────────────────────────────────────────────
function measure(M, L, fixture = 'absent') {
  const MG = M.gates, LG = L.gates;
  const R = { conform: [], diverge: [], regions: [] };
  const conform = (name, ref, cand) => R.conform.push({ name, ref, cand });
  const diverge = (key, form) => R.diverge.push({ key, form });

  // the committed fixture must track the live emission, or this run scored a shape nobody ships
  conform('fixture/in-sync-with-live-emission', fixture === 'absent' ? 'absent' : 'in sync', fixture);

  // (0) the public input block — kimchi puts PRIMARY_LEN Generic rows first on both sides.
  conform('pi/size', M.pi, L.pi);
  conform('pi/rows-are-Generic', MG.slice(0, M.pi).every((g) => g.typ === 'Generic'), LG.slice(0, L.pi).every((g) => g.typ === 'Generic'));
  conform('pi/coeffs', MG.slice(0, M.pi).map((g) => g.coeffs.join(',')).join(';'), LG.slice(0, L.pi).map((g) => g.coeffs.join(',')).join(';'));

  // (A) GADGET SIGNATURE SETS — alignment-free.
  const fams = [
    { key: 'Poseidon', co: true, m: runsOf(MG, 'Poseidon').map((r) => ({ s: r.s, len: 11, w: r.n })), l: runsOf(LG, 'Poseidon').map((r) => ({ s: r.s, len: 11, w: r.n })), core: null },
    { key: 'VBM51', co: false, m: vbmLadders(MG).filter((x) => x.chunks === 51), l: vbmLadders(LG).filter((x) => x.chunks === 51), core: [2, 99] },
    { key: 'VBM26', co: false, m: vbmLadders(MG).filter((x) => x.chunks === 26), l: vbmLadders(LG).filter((x) => x.chunks === 26), core: [2, 49] },
    { key: 'ENDO32', co: false, m: runsOf(MG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s, len: 32 })), l: runsOf(LG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s, len: 32 })), core: [1, 30] },
    { key: 'EMS8', co: false, m: runsOf(MG, 'EndoMulScalar').filter((r) => r.n === 8).map((r) => ({ s: r.s, len: 8 })), l: runsOf(LG, 'EndoMulScalar').filter((r) => r.n === 8).map((r) => ({ s: r.s, len: 8 })), core: [1, 6] },
  ];
  for (const f of fams) {
    const ms = new Map(), ls = new Map();
    for (const u of f.m) { const k = signature(MG, u.s, u.len, f.co); ms.set(k, (ms.get(k) ?? 0) + 1); }
    for (const u of f.l) { const k = signature(LG, u.s, u.len, f.co); ls.set(k, (ls.get(k) ?? 0) + 1); }
    if (f.key === 'Poseidon' && runsOf(MG, 'Poseidon').some((r) => r.n !== 11)) throw new Error('a Mina Poseidon run is not 11 rows');
    if (f.key === 'Poseidon' && runsOf(LG, 'Poseidon').some((r) => r.n !== 11)) throw new Error('a Lean Poseidon run is not 11 rows');
    let hit = 0; for (const [k, c] of ls) if (ms.has(k)) hit += c;
    const rec = { key: f.key, mina: f.m.length, lean: f.l.length, mClasses: ms.size, lClasses: ls.size, hit, positions: [], mSpread: [...ms.values()].sort((a, b) => b - a).join('/') };
    // The whole-instance signature either matches or it does not; when it does not, localize against
    // the CLOSEST Mina class (fewest differing cells), not the most common — the closest one is the
    // gadget Snarky emits for the same job, and naming the wrong one mis-attributes the seam.
    if (hit !== f.l.length && f.m.length && f.l.length) {
      const lRep = f.l[0];
      let best = null;
      for (const u of f.m) {
        const d = localize(MG, u.s, LG, lRep.s, lRep.len, f.co);
        if (!best || d.length < best.d.length) best = { u, d };
      }
      rec.positions = best.d.map((d) => `${d.at} ${d.ref}→${d.cand}`);
    }
    // The CORE (interior rows) — the gadget BODY, with its seam rows excluded. This is the part that
    // is purely Snarky's emission pattern and owes nothing to where the instance is attached.
    if (f.core) {
      const [a, b] = f.core;
      const csig = (G, u) => { const o = []; for (let d = a; d <= b; d++) { const r = u.s + d, g = G[r]; o.push(g.typ); for (let j = 0; j < PERMUTS; j++) o.push(cellClass(G, u.s, u.len, d, j)); } return o.join('/'); };
      const mc = new Map(); for (const u of f.m) mc.set(csig(MG, u), (mc.get(csig(MG, u)) ?? 0) + 1);
      const lc = new Map(); for (const u of f.l) lc.set(csig(LG, u), (lc.get(csig(LG, u)) ?? 0) + 1);
      let ch = 0; for (const [k, c] of lc) if (mc.has(k)) ch += c;
      rec.coreHit = ch; rec.coreRows = `${a}..${b}`; rec.mCoreClasses = mc.size; rec.lCoreClasses = lc.size;
      // ⚑ THE REAL CROSS-SOURCE ENTRY. Reference = the digest of the MINA core class our body matches
      // (looked up in the blob); candidate = the digest of OUR body. Byte-equal iff the body Snarky
      // emits and the body Lean emits are the same object. Our body moves → RED; the blob moves → RED.
      const ours = [...lc.keys()].sort((x, y) => lc.get(y) - lc.get(x))[0];
      conform(`gadget/${f.key}/body-digest[rows ${a}..${b}]`,
        mc.has(ours) ? sigDigest(ours) : `NO MINA BODY CLASS MATCHES (mina has ${mc.size}: ${[...mc.keys()].map(sigDigest).join(' ')})`,
        sigDigest(ours));
      conform(`gadget/${f.key}/instances-with-that-body`, `${f.l.length}/${f.l.length}`, `${ch}/${f.l.length}`);
    } else {
      // Poseidon: no seam to exclude — the WHOLE 11-row permutation, coefficients included, is the unit.
      const ours = [...ls.keys()].sort((x, y) => ls.get(y) - ls.get(x))[0];
      conform(`gadget/${f.key}/whole-digest[11 rows + 15 coeffs/row]`,
        ms.has(ours) ? sigDigest(ours) : `NO MINA CLASS MATCHES (mina has ${ms.size})`, sigDigest(ours));
      conform(`gadget/${f.key}/instances-with-that-signature`, `${f.l.length}/${f.l.length}`, `${hit}/${f.l.length}`);
    }
    R.regions.push(rec);
  }

  // (B) REGION ANCHORS — each asserted UNIQUE.
  const mLad = vbmLadders(MG), lLad = vbmLadders(LG);
  const run51 = (lad) => { const o = []; let i = 0; while (i < lad.length) { if (lad[i].chunks === 51 && (i === 0 || lad[i - 1].chunks !== 51 || lad[i].s - (lad[i - 1].s + lad[i - 1].len) > 200)) { let n = 0; while (lad[i + n] && lad[i + n].chunks === 51 && (n === 0 || lad[i + n].s - (lad[i + n - 1].s + lad[i + n - 1].len) <= 200)) n++; o.push({ i, n }); i += n; } else i++; } return o; };
  const mFt = run51(mLad).filter((x) => x.n === 8), lFt = run51(lLad).filter((x) => x.n === 8);
  if (mFt.length !== 1) throw new Error(`ft_comm anchor NOT UNIQUE on Mina: ${mFt.length} runs of eight 51-chunk ladders`);
  if (lFt.length !== 1) throw new Error(`ft_comm anchor NOT UNIQUE on the Lean side: ${lFt.length}`);
  const mFtL = mLad.slice(mFt[0].i, mFt[0].i + 8), lFtL = lLad.slice(lFt[0].i, lFt[0].i + 8);
  conform('region/ft_comm/ladders', mFtL.length, lFtL.length);
  conform('region/ft_comm/chunks-each', mFtL.map((x) => x.chunks).join(','), lFtL.map((x) => x.chunks).join(','));

  // x_hat = the ladder cluster immediately before ft_comm's first ladder (gap ≤ 1000 rows)
  const before = (lad, stop) => { const pre = lad.filter((x) => x.s < stop); const out = []; for (let i = pre.length - 1; i >= 0; i--) { if (out.length && out[0].s - (pre[i].s + pre[i].len) > 1000) break; out.unshift(pre[i]); } return out; };
  const mX = before(mLad, mFtL[0].s), lX = before(lLad, lFtL[0].s);
  const widths = (ls) => { const h = {}; for (const x of ls) h[x.chunks] = (h[x.chunks] ?? 0) + 1; return Object.entries(h).sort((a, b) => a[0] - b[0]).map(([k, v]) => `${k}×${v}`).join(' '); };
  const chunkSum = (ls) => ls.reduce((a, x) => a + x.chunks, 0);
  R.xhat = { mina: { n: mX.length, widths: widths(mX), chunks: chunkSum(mX) }, lean: { n: lX.length, widths: widths(lX), chunks: chunkSum(lX) } };
  if (R.xhat.mina.widths !== R.xhat.lean.widths) diverge('xhat/scalar-widths', `mina ${R.xhat.mina.widths} (${R.xhat.mina.chunks} chunks) vs lean ${R.xhat.lean.widths} (${R.xhat.lean.chunks})`);

  // ipa = the EndoMul-32 clusters (gap ≤ 100). Mina's split is combine_split_commitments | bullet_reduce.
  const mEc = cluster(runsOf(MG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s, len: 33 })), 100);
  const lEc = cluster(runsOf(LG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s, len: 33 })), 100);
  R.ipa = { mina: mEc.map((c) => c.length), lean: lEc.map((c) => c.length) };
  const mIpa = mEc.filter((c) => c.length >= 10).flat();
  conform('region/ipa/endo-blocks', mIpa.length, lEc.flat().length);

  // (C) the DIVERGENCE set from the gadget signatures, RE-CONFIRMED against the unspliced emission.
  const rawSelf = (leanRawRow, j) => { const w = L.raw[leanRawRow].wires[j]; return w.row === leanRawRow && w.col === j; };
  const rawRowOf = (spliced) => { let n = -1; for (let i = 0; i < L.raw.length; i++) { if (L.remap[i] >= 0) n++; if (n === spliced) return i; } throw new Error('remap'); };
  const seedCheck = (units, cols, off) => { let n = 0; for (const u of units) { const rr = rawRowOf(u.s + off); for (const j of cols) if (rawSelf(rr, j)) n++; } return n; };
  const lVbm26 = lLad.filter((x) => x.chunks === 26), lVbm51 = lLad.filter((x) => x.chunks === 51);
  const lEndo = runsOf(LG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s }));
  const xhatSeed = seedCheck(lVbm26, [2, 3, 4], 0) + seedCheck(lVbm26, [2, 3, 4], 1);
  const ftSeed = seedCheck(lVbm51, [4], 0);
  const ipaSeed = seedCheck(lEndo, [4, 5, 6], 0);
  if (xhatSeed) diverge('xhat/ladder-seed-unwired', `${xhatSeed}/${lVbm26.length * 6} cells SELF in the UNSPLICED emission (mina: 0)`);
  if (ftSeed) diverge('ftcomm/scalar-seed-unwired', `${ftSeed}/${lVbm51.length} cells SELF in the UNSPLICED emission (mina: 0)`);
  if (ipaSeed) diverge('ipa/endo-seed-unwired', `${ipaSeed}/${lEndo.length * 3} cells SELF in the UNSPLICED emission (mina: 0)`);

  const emsFam = R.regions.find((r) => r.key === 'EMS8');
  if (emsFam.hit !== emsFam.lean) diverge('tfc/chain-endpoints', `${emsFam.lean - emsFam.hit}/${emsFam.lean} chains outside Mina's ${emsFam.mClasses} classes; core rows ${emsFam.coreRows} match ${emsFam.coreHit}/${emsFam.lean}`);
  const emsW = (G) => { const h = {}; for (const r of runsOf(G, 'EndoMulScalar')) h[r.n] = (h[r.n] ?? 0) + 1; return Object.entries(h).sort((a, b) => a[0] - b[0]).map(([k, v]) => `${k}×${v}`).join(' '); };
  R.emsWidths = { mina: emsW(MG), lean: emsW(LG) };
  if (R.emsWidths.mina !== R.emsWidths.lean) diverge('tfc/widths', `mina ${R.emsWidths.mina} vs lean ${R.emsWidths.lean}`);

  // Generic SELECTOR HALVES. A kimchi Generic row is DOUBLE: coeffs[0..4] and [5..9] are two
  // independent (l,r,o,m,c) operations. Which half pairs with which is OUR packing choice, so the
  // comparable unit is the HALF, not the row.
  const halves = (G) => { const m = new Map(); for (const g of G) if (g.typ === 'Generic') { m.set(g.coeffs.slice(0, 5).join('|'), (m.get(g.coeffs.slice(0, 5).join('|')) ?? 0) + 1); if (g.coeffs.length >= 10) m.set(g.coeffs.slice(5, 10).join('|'), (m.get(g.coeffs.slice(5, 10).join('|')) ?? 0) + 1); } return m; };
  const MH = halves(MG), LH = halves(LG);
  let hIn = 0, hOut = 0; const hMiss = [];
  for (const [k, c] of LH) { if (MH.has(k)) hIn += c; else { hOut += c; hMiss.push([k, c]); } }
  hMiss.sort((a, b) => b[1] - a[1]);
  // ⚑ the digest covers the WHOLE miss list (every shape and every count), so ONE bent selector
  // coefficient anywhere in the 1509 Generic rows moves it. A top-6 summary alone could not see that.
  const missDigest = createHash('sha256').update([...hMiss].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([k, c]) => `${k}=${c}`).join(';')).digest('hex').slice(0, 16);
  R.generic = { minaDistinct: MH.size, leanDistinct: LH.size, in: hIn, out: hOut, digest: missDigest, top: hMiss.slice(0, 6).map(([k, c]) => `×${c} [${k.split('|').map((s) => { const v = BigInt(s); return v > FP / 2n ? `-${FP - v}` : s; }).map((s) => (s.length > 12 ? `${s.slice(0, 9)}…` : s)).join(' ')}]`) };
  if (hOut) diverge('generic/selector-shapes-absent-upstream', `${hOut}/${hIn + hOut} halves in ${hMiss.length} shapes Snarky never emits [${missDigest}]; top: ${R.generic.top.join(' ')}`);

  if (L.probe.size) diverge('probe-rows', `${L.probe.size} standalone Zero rows (mina: 0)`);

  const scope = [];
  for (const f of R.regions) if (f.mina > f.lean) scope.push(`${f.key} ${f.lean}/${f.mina}`);
  if (scope.length) diverge('scope/unassembled-subcircuits', scope.join(' '));

  return R;
}

// ── vectors ───────────────────────────────────────────────────────────────────────────────────────
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
  console.log(`\n╔═ STEP_MAIN REGION CONFORMANCE — gate-by-gate, Lean \`verify_one\` vs Mina step-zkapp-proved`);
  console.log(`║  mina: ${M.gates.length} gates, PI ${M.pi}     lean: ${L.gates.length} probe-free rows (+${L.probe.size} σ-probes), PI ${L.pi}`);
  console.log(`║  lean source: ${src}`);
  console.log('╚═\n');
  console.log('── (A) GADGET SIGNATURE SETS — alignment-free: is the instance we emit one Mina emits?');
  console.log('   family    ours  mina | mina classes | WHOLE instance conforms | gadget BODY (seam excluded)');
  for (const f of R.regions) {
    console.log(`   ${f.key.padEnd(9)} ${String(f.lean).padStart(4)} ${String(f.mina).padStart(5)} | ${String(`${f.mClasses} (${f.mSpread})`).padStart(12)} | ${String(`${f.hit}/${f.lean}  ${pct(f.hit, f.lean)}`).padStart(23)} | ${(f.coreRows ? `rows ${f.coreRows}` : 'whole, +coeffs').padEnd(14)} ${f.coreHit === undefined ? `${f.hit}/${f.lean}  ${pct(f.hit, f.lean)}` : `${f.coreHit}/${f.lean}  ${pct(f.coreHit, f.lean)}`}`);
    if (f.positions.length) console.log(`      SEAM (vs the closest Mina class): ${f.positions.join('   ')}`);
  }
  console.log('\n── (B) REGION ANCHORS (uniqueness asserted on both sides; a ladder = a maximal (VarBaseMul,Zero) run)');
  console.log(`   ft_comm  anchor = the unique run of EIGHT consecutive 51-chunk ladders`);
  console.log(`              mina 8 ladders × 51 chunks   |   lean 8 × 51        ✓ COUNT AND WIDTH ALIGNED`);
  console.log(`   x_hat    anchor = the ladder cluster immediately before ft_comm (gap ≤ 1000 rows)`);
  console.log(`              mina ${String(R.xhat.mina.n).padStart(2)} ladders  ${R.xhat.mina.widths.padEnd(18)} = ${R.xhat.mina.chunks} chunks  (40 Wrap statement words, 9 of them Bool → 0 chunks)`);
  console.log(`              lean ${String(R.xhat.lean.n).padStart(2)} ladders  ${R.xhat.lean.widths.padEnd(18)} = ${R.xhat.lean.chunks} chunks  (40 terms × 26, uniform; adjacent terms merge into one run)`);
  console.log(`   ipa      anchor = EndoMul-32 blocks clustered at gap ≤ 100 rows`);
  console.log(`              mina ${R.ipa.mina.join(' + ')}  — combine_split_commitments ${R.ipa.mina[0]} | bullet_reduce ${R.ipa.mina[1]} | check_bulletproof ${R.ipa.mina.slice(2).join('+') || 0}`);
  console.log(`              lean ${R.ipa.lean.join(' + ')}  — one contiguous cluster; ${R.ipa.mina[0]} + ${R.ipa.mina[1]} = ${R.ipa.mina[0] + R.ipa.mina[1]} matches ours EXACTLY`);
  console.log(`   to_field_checked widths (EndoMulScalar run lengths)`);
  console.log(`              mina ${R.emsWidths.mina}`);
  console.log(`              lean ${R.emsWidths.lean}`);
  console.log(`   Generic selector halves  ${R.generic.in}/${R.generic.in + R.generic.out} of ours use a shape Snarky also emits (${R.generic.leanDistinct} distinct here, ${R.generic.minaDistinct} upstream)`);
  console.log('\n── (C) DIVERGENCES, classified against KimchiStepMain.lean\'s NAMED SIMPLIFICATIONS');
  const un = [];
  for (const d of R.diverge) {
    const l = LEDGER[d.key];
    const tag = l ? l.why : '⚠ NOT IN THE LEDGER';
    if (!l || l.why === 'UNRECORDED') un.push(d.key);
    console.log(`   ${(l && l.why === 'UNRECORDED' ? '⚠ ' : '  ')}${d.key}`);
    console.log(`       ${tag}`);
    console.log(`       measured: ${d.form}`);
    if (l) console.log(`       ${l.note}`);
  }
  if (un.length) {
    console.log(`\n   ⚑ ${un.length} DIVERGENCE(S) ARE NOT ON THE #1–#11 LIST: ${un.join(', ')}`);
    console.log('     Each is either an unrecorded simplification (→ give it a numbered entry) or a defect.');
  }
  console.log();
}

// ── falsifiers: the diff must MOVE when the candidate is bent ─────────────────────────────────────
function falsify(M, leanJson) {
  const good = JSON.stringify(candidateVector(measure(M, normalizeLean(leanJson))));
  const bite = (label, mutate) => {
    const copy = JSON.parse(JSON.stringify(leanJson));
    mutate(copy);
    let got;
    try { got = JSON.stringify(candidateVector(measure(M, normalizeLean(copy)))); }
    catch (e) { process.stdout.write(`   red-path OK: ${label} -> REFUSED (${String(e.message).slice(0, 60)}…)\n`); return; }
    if (got === good) throw new Error(`RED-PATH FAILED: ${label} did not move the conformance vector`);
    process.stdout.write(`   red-path OK: ${label} -> conformance vector MOVED\n`);
  };
  const find = (typ) => leanJson.gates.findIndex((g) => NAMES[g.typ] === typ);
  // 1. one bent Poseidon round constant — the 100%-conforming gadget must stop conforming
  bite('bend 1 Poseidon round constant', (j) => { const i = find('Poseidon'); j.gates[i].coeffs[0] = String(BigInt(j.gates[i].coeffs[0]) + 1n); });
  // 2. one moved wire INSIDE a Poseidon permutation body
  bite('move 1 wire inside a Poseidon permutation', (j) => { const i = find('Poseidon'); j.gates[i + 3].wires[2] = [j.gates[i + 3].wires[2][0] + 1, j.gates[i + 3].wires[2][1]]; });
  // 3. one retyped gate — a gadget run length changes and the family census moves
  bite('retype one VarBaseMul row to Zero', (j) => { const i = find('VarBaseMul'); j.gates[i].typ = 0; });
  // 4. one bent Generic selector — the shared-shape census moves
  bite('bend 1 Generic selector coefficient', (j) => { const i = j.gates.findIndex((g) => NAMES[g.typ] === 'Generic' && g.coeffs.length === 10); j.gates[i].coeffs[3] = '7'; });
  // 5. one wire inside an EndoMul block body
  bite('move 1 wire inside an EndoMul-32 body', (j) => { const i = find('EndoMul'); j.gates[i + 5].wires[0] = [j.gates[i + 5].wires[0][0] + 1, j.gates[i + 5].wires[0][1]]; });
  // 6. the OTHER leg of the ledger: a divergence that STOPS being observed must also be RED, or a
  //    retired simplification would leave a dead allowance sitting in the ledger forever.
  bite('drop every σ-probe row → the `probe-rows` ledger entry goes unobserved', (j) => { j.probe_rows = []; });
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };
const { spec, publicInputSize, gates } = await loadCircuit('step-zkapp-proved');
const M = normalizeMina(publicInputSize, gates);
const { src, fixture, j: leanJson } = loadLeanSide(arg("--lean"));
const L = normalizeLean(leanJson);
const R = measure(M, L, fixture);

if (argv.includes('--refresh-fixture')) {
  const { gzipSync } = await import('node:zlib');
  const { writeFileSync } = await import('node:fs');
  const slim = JSON.stringify({ name: leanJson.name, public_input_size: leanJson.public_input_size, num_rows: leanJson.num_rows, probe_rows: leanJson.probe_rows, gates: leanJson.gates });
  writeFileSync(LEAN_FIXTURE, gzipSync(Buffer.from(slim), { level: 9 }));
  console.log(`refreshed fixtures/stepmain-step-r8-finalize-gates.json.gz from ${src} (${leanJson.gates.length} gates)`);
  process.exit(0);
}
if (argv.includes('--report')) { report(R, src, M, L); process.exit(0); }

await runOracle({
  shape: 'gates',
  label: `verify_one region conformance — Lean ${leanJson.name} vs mina ${spec.stem.slice(0, 44)}… (gate-by-gate)`,
  reference: () => referenceVector(R),
  candidate: () => candidateVector(R),
  extra: () => {
    report(R, src, M, L);
    if (argv.includes('--falsify')) falsify(M, leanJson);
  },
});
