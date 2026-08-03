// STEP_MAIN REGION CONFORMANCE — the Lean-assembled `verify_one` against Mina's own compiled step
// circuit, GATE BY GATE, not by run-length.
//
// ## WHAT THIS IS, AND WHAT `stepmain-shape-diff.mjs` COULD NOT SEE
//
// `stepmain-shape-diff.mjs` compares five run-length FAMILIES (Poseidon 11, EndoMul 32,
// EndoMulScalar 8, VarBaseMul 1, CompleteAdd 1 — the LENGTHS, whose instance COUNTS move with every
// sub-circuit the assembly gains and are therefore not written down here). A run length cannot see a wrong
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
// ## ⚑ THE GENERIC SELECTOR HALVES, AND THE TWO NORMALIZATIONS THE CENSUS NEEDS
//
// A kimchi `Generic` row is DOUBLE: `coeffs[0..4]` and `[5..9]` are two independent
// `(l, r, o, m, c)` operations over cols 0,1,2 and 3,4,5. Which half pairs with which is OUR packing
// choice, so the comparable unit is the HALF. Comparing halves by EXACT COEFFICIENT VECTOR — which
// is what this script did until 2026-08-02 — over-counts the divergence two ways, and both are
// artifacts of the instrument rather than facts about the circuit:
//
//   * **A DIFFERENT CONSTANT IS NOT A DIFFERENT SHAPE.** `[1,0,0,0,-k]` is Snarky's own
//     `Equal (var, constant)` row (`plonk_constraint_system.ml:1668-1678`) and it emits ~250 of
//     them; ours pin OUR constants. Exact-value matching scored 185 such halves as "a shape Snarky
//     never emits". Collapsing every constant outside ±100 to `K` is the FAMILY key.
//   * **A HALF IS HOMOGENEOUS.** `Σ cᵢ·termᵢ = 0` and its negation are the SAME constraint. Mina
//     emits `[-1,-1,0,0,0]` ×60 where we emit `[1,1,0,0,0]` ×9 — one equation, opposite global
//     sign, because `reduce_lincom` happened to fold the other way. The FAMILY key is therefore also
//     sign-normalized (negate when the leading nonzero coefficient is > p/2).
//
// Both censuses are reported. The EXACT one is the byte-level tripwire — one bent coefficient moves
// its digest. The FAMILY one is the fidelity statement: which SHAPES we emit that Snarky does not.
//
// ## ⚑ THE ALL-ZERO HALF, AND WHY IT IS GATED AND NOT MERELY COUNTED
//
// A half whose five coefficients are all zero constrains NOTHING. Mina emits zero of them in 12,423
// halves, because `add_generic_constraint` queues ONE `pending_generic_gate` for the WHOLE system
// (`:1449-1458`) and finalization flushes at most one (`:1296-1299`) — an odd half from one gadget
// pairs with the next generic constraint wherever in the circuit it comes from. Ours pack per
// EMISSION SITE (`packHalves`, `aRows`), so every site with an odd half leaves a tail.
//
// That is waste, not a defect — but the SAME symptom would also be produced by a defect: an operand
// dropped into a half that carries no equation, which is a constraint the assembly meant to enforce
// and does not. The two are told apart by CONSTRUCTION, and the three facts that tell them apart are
// CONFORM ENTRIES (`generic/zero-half/…`), not commentary:
//
//   (1) every all-zero half is a SECOND half — a first half means the packer mis-ordered;
//   (2) its three permutation columns are SELF in the UNSPLICED emission — a σ-classed cell in a
//       half with no equation is a variable the circuit believes is wired and that this row does not
//       constrain;
//   (3) its row's OTHER half carries a real equation — an all-zero ROW is a row emitted for nothing.
//
// (2) is the dropped-constraint detector and it is the reason this is a gate. A fourth check — that
// the witness columns under an all-zero half are zero, which catches a DEAD variable occurring
// exactly once and therefore SELF — needs the witness and so runs only against a live emission,
// where it THROWS rather than scoring.
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
// ## ⚑ THE FRESHNESS FLOOR — WHAT THIS GATE READ, UNTIL 2026-08-02, WITHOUT LOOKING
//
// This script read `/tmp/pickles-stepmain/stepmain_step_r8_finalize.json` with `existsSync` +
// `readFileSync` AND NOTHING ELSE. MEASURED: a copy of that artifact back-dated to `Jul 29 03:15`
// — four days older than the Lean sources it claims to come from — scored **GREEN, exit 0**, printed
// the whole verdict below and reported `fixture: in sync`. Every "conformance GREEN byte-exact, ten
// falsifiers biting, EndoMul 32×77 intact" statement made through this instrument was, until that
// floor existed, a statement about WHATEVER FILE HAPPENED TO BE IN `/tmp`.
//
// It is closed at the floor and not by a warning (a warning inside a green run is invisible):
//
//   * `--emit` makes the gate EMIT ITS OWN INPUT first, so there is no stale path to read;
//   * every input — live artifact AND committed fixture — carries a PROVENANCE STAMP naming the
//     source cone it came from, and this gate recomputes that cone's digest FROM THE CURRENT TREE
//     and REFUSES on any difference (`emit-provenance.mjs`, two independent legs: content + clock);
//   * there is NO unstamped path. An artifact with no stamp is refused, not scored.
//
// USAGE — ⚠ EVERY invocation is green-or-bust. There is no non-gating mode in this file.
//   node scripts/stepmain-region-conformance.mjs                  # green-or-bust
//   node scripts/stepmain-region-conformance.mjs --emit           # ⚑ emit the input first, then grade
//   node scripts/stepmain-region-conformance.mjs --self-test      # + the harness red path
//   node scripts/stepmain-region-conformance.mjs --stale-self-test # ⚑ prove the freshness floor bites
//   node scripts/stepmain-region-conformance.mjs --report         # ACCEPTED, INERT. See below.
//   node scripts/stepmain-region-conformance.mjs --lean <path>    # a specific rung emission
//   node scripts/stepmain-region-conformance.mjs --falsify        # prove the diff bites (10 bites)
//   node scripts/stepmain-region-conformance.mjs --refresh-fixture
//
// ⚑ `--report` WAS A MODE THAT COULD NOT FAIL, and it is now inert (2026-08-03). It read
//     if (argv.includes('--report')) { report(...); process.exit(0); }
// placed immediately BEFORE `runOracle`, so it printed every divergence in the per-region dump and
// then exited 0 — a GREEN that was a formatting success and no verdict at all. It bought nothing
// even as a dump: `runOracle`'s `extra` callback below calls the SAME `report(...)` on every
// invocation, so the flag's only effect in this file's whole history was to skip the grade. It is
// kept as an accepted no-op (it appears in prose and in shell history) and it now falls straight
// through to the same green-or-bust verdict as a bare run.
//
// The Lean side is `/tmp/pickles-stepmain/stepmain_step_r8_finalize.json` when a `lake env lean --run
// Dregg2/Circuit/Emit/EmitStepMainJson.lean` has been done, else the committed gzip fixture. When BOTH
// exist the LIVE one is measured — and if it differs from the fixture that is a RED of its own
// (`conform:fixture/in-sync-with-live-emission`), so a moved assembly is reported, never scored stale.
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { gunzipSync } from 'node:zlib';
import { runOracle } from './diff-oracle.mjs';
import {
  isStale, leanConeDigest, requireFreshArtifact, requireFreshFixture, runLeanEmit, writeFixtureSidecar,
} from './emit-provenance.mjs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`); the Lean emitter
// writes the ORDINAL, the o1-labs blob writes the NAME.
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
const PERMUTS = 7;
// Tick/Fp — the Pallas base field, the step circuit's own. The Lean emitter writes SIGNED decimals
// (`-1`), the blob writes 32-byte LE hex; both are normalized into [0,p) before any comparison.
const FP = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;

// ⚑ SETTABLE, and the SAME variable the Lean driver reads. The dir was a hardcoded global on both
// sides, so two lanes emitting the `step` shape wrote byte-different `stepmain_step_r8_finalize.json`
// to one path and the later writer silently won. `DREGG_SM_OUT=<dir>` now gives a lane its own.
const LEAN_DIR = process.env.DREGG_SM_OUT ?? '/tmp/pickles-stepmain';
const LEAN_DEFAULT = `${LEAN_DIR}/stepmain_step_r8_finalize.json`;
const LEAN_FIXTURE = new URL('../fixtures/stepmain-step-r8-finalize-gates.json.gz', import.meta.url);
const LEAN_FIXTURE_PROV = new URL('../fixtures/stepmain-step-r8-finalize-gates.provenance.json', import.meta.url);
// ⚑ The emit driver, and therefore the ROOT of the freshness cone. Its transitive `import Dregg2.*`
// closure is what decides the emitted bytes; the thirteen `KimchiStepMainPins*` guard modules are
// NOT in it (the driver imports `KimchiStepMainCore`, not the umbrella) and so cannot invalidate an
// emission by being edited.
const EMIT_DRIVER = 'Dregg2/Circuit/Emit/EmitStepMainJson.lean';
// ⚑ ASK FOR THE RUNG THIS GATE GRADES, AND ONLY THAT RUNG. `LEAN_DEFAULT` is `r8_finalize` and
// nothing here ever reads another rung, but the driver used to emit all nine unconditionally — so
// `--emit` blocked on ~10 hours of work to produce one artifact, and in practice never finished.
// Measured on the `step` shape from artifact mtimes: consecutive rungs landed 68–69 min apart, and
// the gap did not grow with the rung, because `rungRows` evaluates every sub-list before it matches
// on the rung. `DREGG_SM_RUNGS=all` is still there for a sweep that genuinely wants the nine.
const EMIT_RUNG = 'r8_finalize';
const EMIT_ENV = { DREGG_SM: 'step', DREGG_SM_RUNGS: EMIT_RUNG, DREGG_SM_OUT: LEAN_DIR };
const EMIT_CMD = `(cd metatheory && DREGG_SM=step DREGG_SM_RUNGS=${EMIT_RUNG} lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean)`
  + '   — or let the gate do it:  node scripts/stepmain-region-conformance.mjs --emit';
const REFRESH_CMD = 'node scripts/stepmain-region-conformance.mjs --emit --refresh-fixture';

const fp = (c) => { let v = BigInt(c) % FP; if (v < 0n) v += FP; return v.toString(); };
const leHex = (h) => BigInt('0x' + Buffer.from(h, 'hex').reverse().toString('hex')).toString();

// ── Generic selector-half KEYS (see the header). `exactKey` is the byte tripwire; `famKey` is the
// SHAPE: constants outside ±100 collapse to `K`, and the half is negated when its leading nonzero
// coefficient is > p/2, because `Σ cᵢ·termᵢ = 0` and its negation are one constraint.
const exactKey = (h) => h.join('|');
const small = (v) => (v === 0n ? '0' : v < 100n ? v.toString() : v > FP - 100n ? `-${FP - v}` : 'K');
const famKey = (h) => {
  const v = h.map(BigInt);
  const lead = v.find((x) => x !== 0n);
  const n = lead !== undefined && lead > FP / 2n ? v.map((x) => (x === 0n ? 0n : FP - x)) : v;
  return n.map(small).join(' ');
};
const EQ_KEY = [1n, FP - 1n, 0n, 0n, 0n].join('|');
/** ⚑ The SET of shape families we emit and Snarky does not — count-free, so assembly growth does not
 *  move it and a genuinely NEW shape is the only thing that does. Each is classified in the LEDGER. */
const FAM_SET_EXPECTED = [
  '[0 0 0 0 0]',       // the empty second half        → generic/empty-second-half
  '[1 -1 0 0 0]',      // a row where Snarky unions    → generic/row-equality-not-sigma-tie
  '[K 0 1 0 0]',       // the endo seed scale          → generic/unfused-scale
  '[0 0 1 -1 5]',      // assert_on_curve, fused       → generic/fused-halves
  '[0 0 1 -1 -1]',     // b_poly Horner, fused         → generic/fused-halves
  '[1 -2 -1 0 0]', '[1 2 -1 0 0]',                  // small arithmetic, fused
  '[1 0 0 0 1]', '[1 0 0 0 -3]', '[1 0 0 0 -6]', '[1 0 0 0 -11]', // constant pins at values Mina lacks
].sort().join(' ');

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
  return { pi: j.public_input_size, gates, raw, probe, remap, keep };
}

/**
 * ⚑ THE FRESHNESS FLOOR. Every path out of this function has had its input's provenance CHECKED
 * against the emit cone as the tree stands right now, or has thrown. There is no unstamped path:
 * an artifact that cannot say which source produced it is refused, because an artifact left over
 * from an earlier session is otherwise indistinguishable from one emitted a second ago — and that
 * indistinguishability is the whole defect (a `Jul 29` artifact scored GREEN on `Aug 2` sources).
 */
function loadLeanSide(explicit, cone) {
  const live = explicit ?? LEAN_DEFAULT;
  const haveLive = existsSync(live);
  const haveFix = existsSync(LEAN_FIXTURE);
  if (!haveLive && !haveFix)
    throw new Error(`no Lean emission: neither ${live} nor the committed fixture. Produce it with\n   ${EMIT_CMD}`);
  const slim = (j) => JSON.stringify({ name: j.name, public_input_size: j.public_input_size, num_rows: j.num_rows, probe_rows: j.probe_rows, gates: j.gates });
  let src, text, witness = null, prov;
  // ⚠ `slim` drops the `witness` field (the fixture carries gates only). It is kept ASIDE here for
  // the dead-variable check, which is live-only BY CONSTRUCTION and says so rather than falling back.
  if (haveLive) {
    prov = requireFreshArtifact({ artifact: live, cone, emitCmd: EMIT_CMD });
    const f = JSON.parse(readFileSync(live, 'utf8'));
    witness = f.witness ?? null; src = live; text = slim(f);
  } else {
    // The fixture is a SNAPSHOT of an emission and goes stale exactly the same way — the committed
    // `.gz` that made two ledger entries read 8/8 and 228/228 falsely predated the fix, and nothing
    // looked. Its sidecar carries the cone it was emitted from, and it is checked here.
    prov = requireFreshFixture({ fixture: LEAN_FIXTURE, sidecar: LEAN_FIXTURE_PROV, cone, emitCmd: EMIT_CMD, refreshCmd: REFRESH_CMD });
    src = 'fixture'; text = gunzipSync(readFileSync(LEAN_FIXTURE)).toString('utf8');
  }
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
  return { src, fixture, witness, prov, j: JSON.parse(text) };
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
  // ⚑⚑ RETIRED 2026-08-03 — `xhat/scalar-widths` stopped being observed. It read "mina 2×1 26×22
  // 51×8 (982 chunks) vs lean 26×40 (1040)": Mina scales Wrap statement word `i` by ITS OWN width
  // (`Spec.pack`, `spec.ml:305-395`) and ours was a uniform `StepShape.msmChunks`. `KimchiStepMain`
  // §20 (`…Pins15`) deleted that field and gave each word `msmChunksAt i`, so the emitted x_hat
  // cluster is now **31 ladders, 2×1 26×22 51×8, 982 chunks** — Mina's own vector, element for
  // element, and 58 chunks FEWER than the uniform 26 it replaced. The gate is what noticed the
  // allowance had gone stale; this comment is the retirement.
  // ⚑⚑ AND THE OTHER HALF OF #2 CLOSED THE SAME DAY (§21, `…Pins16`): term `i`'s scalar IS Wrap
  // statement word `i` now, not a shared transcript challenge. ⚠ **THIS INSTRUMENT CANNOT SEE THAT
  // AND MUST NOT BE QUOTED AS EVIDENCE FOR IT** — a signature set is base-free and a σ class is
  // compared by CLASSIFICATION (SELF / IN r,c / EXT), so re-pointing a ladder's terminal counter at
  // a different EXT variable leaves every key here identical. The provenance is exhibited in Lean
  // (bend the word → `x_hat` moves; bend an unread challenge → it does not); the width is what this
  // gate sees. What §21 DID move here: the nine constant words' base pins and probes left the
  // circuit, which is `probe-rows` 488→470 and `generic/exact-value-census` 696/3301→678/3283.
  'xhat/ladder-seed-unwired': {
    why: 'UNRECORDED — ALLOCATION, classified 2026-08-03',
    expect: '93/186 cells SELF (acc/scalar seed 0, chunk bits 93) in the UNSPLICED emission (mina: 0)',
    note: '⚑ THE SEED HALF IS CLOSED AND THIS ENTRY SAID OTHERWISE. It read "the accumulator seed '
      + '(row+0 cols 2,3 = x0,y0) and scalar seed (col 4 = n) are in NO permutation class". MEASURED '
      + '2026-08-03 over the whole x_hat cluster: that leg is 0/93 at every width — §12f\'s '
      + '`msmDblRow` defines `pAcc i 0` and §12g\'s `msmNZeroRows` pins `vSN i 0`, and both cells are '
      + 'σ-classed. What remains is ENTIRELY row+1 cols 2,3,4: the first three of the five chunk BITS. '
      + 'Those are ADVICE cells here and `Boolean.var`s upstream (`exists (Typ.array ~length:num_bits '
      + 'Field.typ)`, `plonk_curve_ops.ml:155-160`), so Snarky gives each one a variable and hence a '
      + 'permutation class. ⚠ NOT A DROPPED CONSTRAINT: kimchi\'s `VarBaseMul` gate body reads exactly '
      + 'those next-row cells, constrains each boolean, and ties their weighted sum to `n\' = 32n + Σ` '
      + '— the ladder\'s own arithmetic, cross-checked against an independent Jacobian oracle in '
      + '`KimchiStepMainPins01`. It is an ALLOCATION difference: same constraint set, no variable. '
      + 'Nothing in the assembly needs to σ-tie a chunk bit to anything, which is why it costs zero.',
  },
  // ⚑ RETIRED 2026-08-02 — `ftcomm/scalar-seed-unwired` stopped being observed (0/8, was 8/8). The
  // Lean side has pinned that cell as WIRED all along (`KimchiStepMain` §12f,
  // `#guard (classCells posS (ftcN k 0)).length == 2` — the `n_acc = Field.zero` pin row plus the
  // ladder's first `VarBaseMul`), so the two sources now agree; the probe used to land on a
  // different row because the 51-chunk ladder boundaries shifted with the R1 interleaving.
  // ⚑ RETIRED 2026-08-02 — `ipa/endo-seed-unwired` stopped being observed (0/231, was 228/228). Each
  // `Scalar_challenge.endo` block's accumulator seed (row+0 cols 4,5) is now the output of the two
  // `Ops.add_fast`s `scalar_challenge.ml:230-234` emits and its scalar seed (col 6) is pinned to
  // `Field.zero` (`:235`) — `KimchiStepMain` §12g, landed in `4de44340f`. ⚠ It read 228/228 until
  // today because the COMMITTED gz fixture predated that commit and no live emission was present;
  // refreshing the fixture is what surfaced the retirement. Same for `ftcomm/scalar-seed-unwired`,
  // and it is why `xhat/ladder-seed-unwired` fell 228/228 → 120/240 (§12f pinned three of its six
  // cells; the two leading pad bits remain).
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
  // ── the Generic selector halves, CLASSIFIED. One entry per mechanism, each naming the upstream
  // code that makes the difference, so a NEW shape family cannot hide inside a count that was going
  // to move anyway. `generic/exact-value-census` is the byte tripwire; the rest are the fidelity
  // statement. ⚑ 2026-08-02: this replaced ONE opaque entry ("550 halves in 172 shapes").
  'generic/exact-value-census': {
    why: 'INSTRUMENT — the byte tripwire, not a divergence claim',
    // ⚑ MOVED 2026-08-03 by §20 (per-word MSM widths): 695/3309 [0a02613d9570c5af] → this. The eight
    // halves are `msmNZeroRows`' — the nine one-bit statement words no longer run a ladder, so they no
    // longer own an `n_acc = 0` half, and `packHalves` re-pairs the remaining 31. The digest moved
    // because the circuit did; a digest that moved on its own would be the tripwire firing.
    // ⚑ MOVED AGAIN 2026-08-03 by §21 (`multiscale_known`'s CONSTANT PARTITION): 696/3301
    // [e46bba1943a6acd0] → this. Exactly 18 halves left, all of them exact-misses and all of them
    // family-MATCHES (194 → 176, while the 502 family-misses are unchanged): they are the NINE
    // constant statement words' `Inner_curve.constant` base pins, two halves each, which upstream
    // never emits because it folds those bases into `constant_part` outside the circuit
    // (`step_verifier.ml:133-152`). The circuit moved; the instrument did not.
    // ⚑ MOVED AGAIN 2026-08-03 by §22 (the fr-sponge's SEED ABSORB): 678/3283 [daacc3a37f552f8b] →
    // this. Segment B's 91st absorbed word is a 46th block, which brings its `cAdd ++ cAdd` addend
    // row (two halves, both matching Snarky) and the pad lane's `cConst 0 ++ cNil` pin (two halves,
    // the `cNil` one all-zero). Total 3283 → 3287, exact-misses 678 → 679 and family-misses 502 →
    // 503 — the SAME one half, the all-zero tail, which `generic/empty-second-half` also counts.
    // Family-MATCHES are 176, unchanged: nothing new here is a Snarky shape carrying our constants.
    expect: '679/3287 halves differ by EXACT coefficient vector [a8dcbafea71719d8]; 503 of those differ '
      + 'by SHAPE FAMILY (constants→K, sign-normalized), so 176 are the same family carrying our constants',
    note: 'The digest covers the WHOLE exact-value miss list, so ONE bent selector coefficient anywhere in '
      + 'the Generic rows moves it. The gap between the two numbers is the instrument, not the circuit: '
      + "`[1,0,0,0,-k]` is Snarky's own `Equal (var, constant)` row (`plonk_constraint_system.ml:1668-1678`).",
  },
  'generic/empty-second-half': {
    why: 'UNRECORDED — COMPILER WASTE, classified 2026-08-02',
    // ⚑ 165 → 166 on 2026-08-03: §20 left `msmNZeroRows` with 31 halves to pack instead of 40, and
    // an odd count leaves one more tail. The mechanism this entry describes, one instance larger.
    // ⚑ 166 → 167 later the same day (§22): segment B's rate-2 PAD LANE gets a `w = 0` pin row, and
    // a one-cell pin is `cConst 0 ++ cNil` — the `cNil` is the empty half. Same mechanism again.
    expect: '167 halves, all SECOND halves, 0 σ-classed cells, 0 all-zero rows (mina: 0 of 12423)',
    note: 'A half constraining nothing. NOT a dropped constraint and NOT padding of an operand — measured by '
      + 'construction: no permutation-classed cell, no live witness value, and every host row carries a real '
      + "equation in its first half. It is our per-site packing (`packHalves`, `aRows`) against Snarky's ONE "
      + '`pending_generic_gate` for the whole system (`:1449-1458`, flushed once at `:1296-1299`), which is why '
      + 'Mina has none. Cost: 82 rows a global pairing pass would recover.',
  },
  'generic/row-equality-not-sigma-tie': {
    why: 'UNRECORDED — a ROW where upstream unions, classified 2026-08-02',
    expect: '114 halves [1 -1 0 0 0] (mina: 0); a global pending_generic_gate would save 83 rows, and '
      + 'converting these to σ-ties a further 57',
    note: '`Field.Assert.equal x y` on two plain variables is `Union_find.union` and emits NO ROW at all '
      + '(`plonk_constraint_system.ml:1650-1653`); only unequal SCALES fall through to a generic row (`:1655`). '
      + 'Ours spends a half. Sites: `closingRows` (67 — every public word tied to its computed variable), '
      + "`tfcRows` split=false (30), the `AOp` compiler's `.aeq` and two one-offs. Converting saves 57 rows.",
  },
  'generic/fused-halves': {
    why: 'UNRECORDED — a TIGHTER encoding of the same equation, classified 2026-08-02',
    expect: '58 [0 0 -1 1 -5] (assert_on_curve) + 80 [0 0 -1 1 1] (b_poly Horner) + 3 small-arith = 141',
    note: 'One half carrying a multiply AND its additive constant, where Snarky spends two because '
      + '`reduce_lincom` (`:1498`) folds the linear part into the CONSUMER instead. `y·y − x³ − b = 0` with '
      + 'b = PALLAS_B = 5 is one half here and `[0 0 -1 1 0]` + `[1 0 -1 0 5]` upstream (Mina emits 129 of the '
      + 'latter). These are GATES — the on-curve half is what refuses an off-curve absorbed commitment.',
  },
  'generic/unfused-scale': {
    why: 'UNRECORDED — the MIRROR of the above, classified 2026-08-02',
    expect: '77 halves [endo 0 -1 0 0] (mina: 0; its nearest by support: [1 0 -1 0 0] ×3)',
    note: "`Scalar_challenge.endo`'s seed pin `endo·xt − xq = 0` (`scalar_challenge.ml:232`), materialised as "
      + 'its own half. Snarky never materialises a bare scale: `Cvar` is a LAZY linear combination, so '
      + '`Field.scale` folds into whichever row consumes it. ⚑ This is a GATE and must not be "converted away" '
      + '— both its cells were FREE WITNESSES until 2026-08-02, and `endo` is cross-checked by the `EndoMul` '
      + "gate body, which is byte-identical to Mina's 76/76.",
  },
  'probe-rows': {
    why: 'header "THE σ-ONLY PROBES" (not on the #1–#11 list)',
    // ⚑ 488 → 470 on 2026-08-03 (§21): the nine constant statement words lost their per-term probe
    // and their fold-add probe along with the rows those probes were about.
    expect: '470 standalone Zero rows (mina: 0)',
    note: 'standalone `Zero` rows placed into σ classes so a flip isolates the wire. Mina has none. Spliced out here.',
  },
  'scope/unassembled-subcircuits': {
    why: '#5 group_map · equal_g · check_bulletproof `scale_fast` of sg · rule.main',
    // ⚑⚑ Poseidon 207 → 179 on 2026-08-03 (§23), and THE DROP IS THE FIX. This entry's prose used to
    // say "our count RISING is the direction this entry wants — it is the subset closing, not a
    // shrinkage." That is the wrong instrument for a FIDELITY fix: the 28 permutations that left are
    // ones Mina's sponge does not perform (a squeeze from `Absorbed _` supplies the pending block's
    // permutation instead of adding one, `sponge.ml:322-325`), so counting them was counting rows
    // upstream has no counterpart for. A subset closes by emitting Mina's gadgets, not by emitting
    // MORE of ours. Read the number as "179 of Mina's 572 permutations are ones we also perform".
    expect: 'Poseidon 179/572 VBM51 16/20',
    note: 'Mina gadget instances with no counterpart here. SUBSET-NESS, not failure — counted so a shrinkage is visible.',
  },
};

// ── the measurement ───────────────────────────────────────────────────────────────────────────────
function measure(M, L, fixture = 'absent', witness = null) {
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
  // ⚑ ALL of Mina's EndoMul-32 blocks, singleton cluster included. It used to be `c.length >= 10`,
  // which dropped Mina's lone `check_bulletproof` block (`Scalar_challenge.endo q c`,
  // `step_verifier.ml:326`) because we had no counterpart for it. We do since 2026-08-02, so the
  // reference is 77 and the filter would now be hiding the very block that closed `delta`.
  const mIpa = mEc.flat();
  conform('region/ipa/endo-blocks', mIpa.length, lEc.flat().length);

  // (C) the DIVERGENCE set from the gadget signatures, RE-CONFIRMED against the unspliced emission.
  const rawSelf = (leanRawRow, j) => { const w = L.raw[leanRawRow].wires[j]; return w.row === leanRawRow && w.col === j; };
  const rawRowOf = (spliced) => { let n = -1; for (let i = 0; i < L.raw.length; i++) { if (L.remap[i] >= 0) n++; if (n === spliced) return i; } throw new Error('remap'); };
  const seedCheck = (units, cols, off) => { let n = 0; for (const u of units) { const rr = rawRowOf(u.s + off); for (const j of cols) if (rawSelf(rr, j)) n++; } return n; };
  const lVbm26 = lLad.filter((x) => x.chunks === 26), lVbm51 = lLad.filter((x) => x.chunks === 51);
  const lEndo = runsOf(LG, 'EndoMul').filter((r) => r.n === 32).map((r) => ({ s: r.s }));
  // ⚑ OVER THE WHOLE x_hat CLUSTER, not just its 26-chunk ladders. Since §20 gave each Wrap
  // statement word its own width the cluster carries 51/26/2-chunk ladders together, and keying on
  // `lVbm26` would have measured 22 of the 31 and silently stopped seeing the rest.
  const xhatSeedAcc = seedCheck(lX, [2, 3, 4], 0), xhatSeedBits = seedCheck(lX, [2, 3, 4], 1);
  const xhatSeed = xhatSeedAcc + xhatSeedBits;
  const ftSeed = seedCheck(lVbm51, [4], 0);
  const ipaSeed = seedCheck(lEndo, [4, 5, 6], 0);
  if (xhatSeed) diverge('xhat/ladder-seed-unwired', `${xhatSeed}/${lX.length * 6} cells SELF (acc/scalar seed ${xhatSeedAcc}, chunk bits ${xhatSeedBits}) in the UNSPLICED emission (mina: 0)`);
  if (ftSeed) diverge('ftcomm/scalar-seed-unwired', `${ftSeed}/${lVbm51.length} cells SELF in the UNSPLICED emission (mina: 0)`);
  if (ipaSeed) diverge('ipa/endo-seed-unwired', `${ipaSeed}/${lEndo.length * 3} cells SELF in the UNSPLICED emission (mina: 0)`);

  const emsFam = R.regions.find((r) => r.key === 'EMS8');
  if (emsFam.hit !== emsFam.lean) diverge('tfc/chain-endpoints', `${emsFam.lean - emsFam.hit}/${emsFam.lean} chains outside Mina's ${emsFam.mClasses} classes; core rows ${emsFam.coreRows} match ${emsFam.coreHit}/${emsFam.lean}`);
  const emsW = (G) => { const h = {}; for (const r of runsOf(G, 'EndoMulScalar')) h[r.n] = (h[r.n] ?? 0) + 1; return Object.entries(h).sort((a, b) => a[0] - b[0]).map(([k, v]) => `${k}×${v}`).join(' '); };
  R.emsWidths = { mina: emsW(MG), lean: emsW(LG) };
  if (R.emsWidths.mina !== R.emsWidths.lean) diverge('tfc/widths', `mina ${R.emsWidths.mina} vs lean ${R.emsWidths.lean}`);

  // ── ⚑ GENERIC SELECTOR HALVES, classified. See the header for the two normalizations.
  const halvesOf = (G, key) => { const m = new Map(); for (const g of G) if (g.typ === 'Generic') for (const h of [g.coeffs.slice(0, 5), g.coeffs.length >= 10 ? g.coeffs.slice(5, 10) : null]) if (h) { const k = key(h); m.set(k, (m.get(k) ?? 0) + 1); } return m; };
  const census = (key) => {
    const mh = halvesOf(MG, key), lh = halvesOf(LG, key);
    let inn = 0, out = 0; const miss = [];
    for (const [k, c] of lh) { if (mh.has(k)) inn += c; else { out += c; miss.push([k, c]); } }
    miss.sort((a, b) => b[1] - a[1] || (a[0] < b[0] ? -1 : 1));
    return { mh, lh, in: inn, out, miss };
  };
  const EX = census(exactKey), FA = census(famKey);
  // The digest covers the WHOLE exact-value miss list, so ONE bent coefficient moves it.
  const missDigest = createHash('sha256').update([...EX.miss].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([k, c]) => `${k}=${c}`).join(';')).digest('hex').slice(0, 16);
  R.generic = { minaDistinct: EX.mh.size, leanDistinct: EX.lh.size, in: EX.in, out: EX.out, digest: missDigest,
    famIn: FA.in, famOut: FA.out, famMiss: FA.miss, minaFams: FA.mh.size, leanFams: FA.lh.size };
  // ⚑ THE STABLE KEY: the SET of shape families we emit and Snarky does not. Growing more of the same
  // gadgets moves every count in this block and does NOT move this set — so a genuinely new shape is
  // the one thing that shows here, instead of hiding inside a count that was going to move anyway.
  conform('generic/family-set-absent-upstream', FAM_SET_EXPECTED, FA.miss.map(([k]) => `[${k}]`).sort().join(' '));
  diverge('generic/exact-value-census', `${EX.out}/${EX.in + EX.out} halves differ by EXACT coefficient vector `
    + `[${missDigest}]; ${FA.out} of those differ by SHAPE FAMILY (constants→K, sign-normalized), so `
    + `${EX.out - FA.out} are the same family carrying our constants`);

  // ── ⚑ THE ALL-ZERO HALF: classified by CONSTRUCTION, and the classification is the gate.
  // Checked against the UNSPLICED emission — the probe splice can only turn a σ-classed cell SELF, so
  // the spliced view would UNDER-report exactly the thing (2) is looking for.
  const rawOf = new Array(LG.length); { let n = 0; for (let i = 0; i < L.raw.length; i++) if (L.remap[i] >= 0) rawOf[n++] = i; }
  const zeroHalves = [];
  for (let r = 0; r < LG.length; r++) {
    const g = LG[r];
    if (g.typ !== 'Generic' || g.coeffs.length < 10) continue;
    for (const w of [0, 1]) if (g.coeffs.slice(5 * w, 5 * w + 5).every((c) => c === '0')) zeroHalves.push({ r, w });
  }
  const zFirstHalf = zeroHalves.filter((z) => z.w === 0).length;
  const zClassed = zeroHalves.filter((z) => { const rr = rawOf[z.r]; return [0, 1, 2].some((k) => { const j = 3 * z.w + k, wr = L.raw[rr].wires[j]; return !(wr.row === rr && wr.col === j); }); });
  const zDeadRow = zeroHalves.filter((z) => LG[z.r].coeffs.slice(5 * (1 - z.w), 5 * (1 - z.w) + 5).every((c) => c === '0'));
  conform('generic/zero-half/all-are-second-halves', 0, zFirstHalf);
  conform('generic/zero-half/no-sigma-classed-cell', 0, zClassed.length ? `${zClassed.length} ⚑ DROPPED CONSTRAINT: ${zClassed.slice(0, 4).map((z) => `row ${z.r} half ${z.w}`).join(', ')}` : 0);
  conform('generic/zero-half/host-row-carries-an-equation', 0, zDeadRow.length);
  // (4) the DEAD-VARIABLE check. A variable occurring exactly once is SELF, so (2) cannot see it; the
  // witness can. Live-only BY CONSTRUCTION — the fixture carries gates alone — and it THROWS rather
  // than scoring, so it is never a quiet pass when the witness is absent.
  if (witness) for (const z of zeroHalves) for (const k of [0, 1, 2]) {
    const v = witness[3 * z.w + k]?.[rawOf[z.r]];
    if (v !== undefined && String(v) !== '0')
      throw new Error(`⚑ DEAD VARIABLE: row ${rawOf[z.r]} col ${3 * z.w + k} carries ${String(v).slice(0, 24)} under an all-zero Generic half`);
  }
  if (zeroHalves.length) diverge('generic/empty-second-half', `${zeroHalves.length} halves, all SECOND halves, ${zClassed.length} σ-classed cells, ${zDeadRow.length} all-zero rows (mina: 0 of ${[...halvesOf(MG, exactKey).values()].reduce((a, b) => a + b, 0)})`);

  // ── ROW ECONOMY: what the two conversions are worth, measured off the emitted object rather than
  // estimated. `pending_generic_gate` pairing recovers the empty halves; the σ-tie conversion removes
  // the equality halves outright. Both numbers move as the assembly grows — that is the point.
  let gRows = 0, fiveCo = 0, eqHalves = 0;
  for (let r = L.pi; r < LG.length; r++) { const g = LG[r]; if (g.typ !== 'Generic') continue; gRows++; if (g.coeffs.length < 10) { fiveCo++; continue; } for (const w of [0, 1]) if (g.coeffs.slice(5 * w, 5 * w + 5).join('|') === EQ_KEY) eqHalves++; }
  const live = 2 * gRows - fiveCo - zeroHalves.length;
  R.economy = { gRows, live, empty: zeroHalves.length, eq: eqHalves,
    packed: Math.ceil(live / 2), bothWays: Math.ceil((live - eqHalves) / 2) };
  if (eqHalves) diverge('generic/row-equality-not-sigma-tie', `${eqHalves} halves [1 -1 0 0 0] (mina: 0); a global pending_generic_gate would save ${gRows - R.economy.packed} rows, and converting these to σ-ties a further ${R.economy.packed - R.economy.bothWays}`);

  // the remaining families, split by whether they FUSE what Snarky spreads or SPREAD what it fuses
  const famCount = (k) => FA.miss.find(([f]) => f === k)?.[1] ?? 0;
  const fused = famCount('0 0 1 -1 5') + famCount('0 0 1 -1 -1') + famCount('1 -2 -1 0 0') + famCount('1 2 -1 0 0');
  const scaled = famCount('K 0 1 0 0');
  if (fused) diverge('generic/fused-halves', `${famCount('0 0 1 -1 5')} [0 0 -1 1 -5] (assert_on_curve) + ${famCount('0 0 1 -1 -1')} [0 0 -1 1 1] (b_poly Horner) + ${famCount('1 -2 -1 0 0') + famCount('1 2 -1 0 0')} small-arith = ${fused}`);
  // Mina's nearest neighbours are looked up by SUPPORT (which coefficient positions are nonzero),
  // never hardcoded — a family name written into prose here would be a pin against this file.
  const support = (k) => k.split(' ').map((c) => (c === '0' ? '.' : '#')).join('');
  const near = [...FA.mh].filter(([k]) => support(k) === support('K 0 1 0 0')).sort((a, b) => b[1] - a[1]).slice(0, 2);
  if (scaled) diverge('generic/unfused-scale', `${scaled} halves [endo 0 -1 0 0] (mina: 0; its nearest by support: ${near.map(([k, c]) => `[${k}] ×${c}`).join(' ') || 'none'})`);

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
function report(R, src, M, L, prov, cone) {
  const pct = (a, b) => (b ? `${(100 * a / b).toFixed(2)}%` : '—');
  console.log(`\n╔═ STEP_MAIN REGION CONFORMANCE — gate-by-gate, Lean \`verify_one\` vs Mina step-zkapp-proved`);
  console.log(`║  mina: ${M.gates.length} gates, PI ${M.pi}     lean: ${L.gates.length} probe-free rows (+${L.probe.size} σ-probes), PI ${L.pi}`);
  console.log(`║  lean source: ${src}`);
  // ⚑ The provenance is printed on the verdict itself, not only checked. A reader quoting "GREEN"
  // needs the emission it graded to be quotable in the same breath.
  if (prov && cone) {
    console.log(`║  emitted:     ${prov.emitted_at ?? prov.refreshed_at}  by  ${prov.command ?? `--refresh-fixture from ${prov.refreshed_from}`}`);
    console.log(`║  cone:        ${cone.files.length} Dregg2 modules under ${cone.root}, digest ${cone.digest.slice(0, 16)}… (VERIFIED against this tree)`);
    // ⚠ This is the HEAD AT EMIT TIME, recorded in the stamp — say so. "git HEAD: <sha>" beside a
    // green reads as CURRENT head, and a provenance line that can be misread is how a stale claim
    // gets born from an honest record.
    if (prov.git?.head) console.log(`║  emitted at:  HEAD ${prov.git.head.slice(0, 12)} (the commit checked out WHEN IT WAS EMITTED)`
      + `${prov.git.cone_dirty_at_head?.length ? `  ⚠ ${prov.git.cone_dirty_at_head.length} cone file(s) were dirty vs it: ${prov.git.cone_dirty_at_head.slice(0, 3).join(', ')}` : '  — emit cone CLEAN at that commit'}`);
  }
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
  console.log(`              lean ${String(R.xhat.lean.n).padStart(2)} ladders  ${R.xhat.lean.widths.padEnd(18)} = ${R.xhat.lean.chunks} chunks  (Spec.pack per-word widths, KimchiStepMainCore §1b; the 9 Bool words emit no ladder)`);
  console.log(`   ipa      anchor = EndoMul-32 blocks clustered at gap ≤ 100 rows`);
  console.log(`              mina ${R.ipa.mina.join(' + ')}  — combine_split_commitments ${R.ipa.mina[0]} | bullet_reduce ${R.ipa.mina[1]} | check_bulletproof ${R.ipa.mina.slice(2).join('+') || 0}`);
  console.log(`              lean ${R.ipa.lean.join(' + ')}  — one contiguous cluster; ${R.ipa.mina[0]} + ${R.ipa.mina[1]} = ${R.ipa.mina[0] + R.ipa.mina[1]} matches ours EXACTLY`);
  console.log(`   to_field_checked widths (EndoMulScalar run lengths)`);
  console.log(`              mina ${R.emsWidths.mina}`);
  console.log(`              lean ${R.emsWidths.lean}`);
  console.log(`   Generic selector halves`);
  console.log(`              by EXACT coefficient vector   ${R.generic.in}/${R.generic.in + R.generic.out} match a Snarky half (${R.generic.leanDistinct} distinct here, ${R.generic.minaDistinct} upstream)`);
  console.log(`              by SHAPE FAMILY (K, ±)        ${R.generic.famIn}/${R.generic.famIn + R.generic.famOut} match  — ${R.generic.out - R.generic.famOut} of the exact misses are the same family with our constants`);
  for (const [k, c] of R.generic.famMiss) console.log(`                 ×${String(c).padStart(4)}  [${k}]`);
  const e = R.economy;
  console.log(`   Generic ROW ECONOMY (circuit rows, PI block excluded)`);
  console.log(`              ${e.gRows} rows carry ${e.live} halves that constrain something + ${e.empty} that do not`);
  console.log(`              one global pending_generic_gate  → ${e.packed} rows   (${e.gRows - e.packed} saved)`);
  console.log(`              + the ${e.eq} equalities as σ-ties → ${e.bothWays} rows   (${e.gRows - e.bothWays} saved in total)`);
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
function falsify(M, leanJson, witness) {
  const good = JSON.stringify(candidateVector(measure(M, normalizeLean(leanJson))));
  const bite = (label, mutate) => {
    const copy = JSON.parse(JSON.stringify(leanJson));
    mutate(copy);
    let got;
    try { got = JSON.stringify(candidateVector(measure(M, normalizeLean(copy), 'absent', witness))); }
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
  // ⚑ 7-9. THE DROPPED-CONSTRAINT GATE. An operand wired into a half that carries no equation is the
  //    defect the all-zero census exists to tell apart from waste, and the three checks that tell
  //    them apart must each be able to go red on their own.
  const zeroRow = (j) => j.gates.findIndex((g) => NAMES[g.typ] === 'Generic' && g.coeffs.length === 10
    && g.coeffs.slice(5, 10).every((c) => fp(c) === '0'));
  bite('wire an operand into an all-zero half → a σ-classed cell with no equation', (j) => {
    const i = zeroRow(j); j.gates[i].wires[3] = [j.gates[i].wires[0][0], j.gates[i].wires[0][1]];
  });
  bite('move an all-zero half to the FIRST position', (j) => {
    const i = zeroRow(j); j.gates[i].coeffs = [...j.gates[i].coeffs.slice(5), ...j.gates[i].coeffs.slice(0, 5)];
  });
  bite('blank a whole Generic row → an all-zero ROW, emitted for nothing', (j) => {
    const i = zeroRow(j); j.gates[i].coeffs = j.gates[i].coeffs.map(() => '0');
  });
  // 10. a NEW shape family must move the count-free family SET, not merely a count.
  bite('bend one selector into a family Snarky never emits', (j) => {
    const i = j.gates.findIndex((g) => NAMES[g.typ] === 'Generic' && g.coeffs.length === 10);
    j.gates[i].coeffs[0] = '3'; j.gates[i].coeffs[1] = '7';
  });
}

// ── the freshness red path ────────────────────────────────────────────────────────────────────────
/**
 * ⚑ PROVE THE FLOOR BITES, and prove it bites for the RIGHT REASON. Three stale shapes, each of
 * which scored GREEN before 2026-08-02, must now REFUSE — and the refusal must name STALENESS, not
 * a content divergence, or the reader goes hunting for a circuit bug that is not there. Plus the
 * ANCHOR: the honest artifact must still be ACCEPTED by the same floor, because a gate that reds on
 * everything proves nothing.
 */
async function staleSelfTest(cone, honest) {
  const { mkdtempSync, copyFileSync, writeFileSync, utimesSync, readFileSync: rd } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { join } = await import('node:path');
  let bad = 0;
  const leg = (label, run) => {
    try { run(); console.log(`  RED  ${label} — was ACCEPTED; the freshness floor does NOT bite here`); bad++; }
    catch (e) {
      if (!isStale(e)) { console.log(`  RED  ${label} — refused, but NOT as staleness: ${String(e.message).slice(0, 90)}`); bad++; return; }
      console.log(`  ok   ${label} -> REFUSED as STALE`);
      console.log(`         ${String(e.message).split('\n')[1]?.trim().slice(0, 150)}`);
    }
  };
  console.log('── stepmain-region-conformance --stale-self-test (the freshness floor) ──');

  // (F0) THE ANCHOR. The artifact this run is actually about must PASS the floor.
  try {
    requireFreshArtifact({ artifact: honest, cone, emitCmd: EMIT_CMD });
    console.log(`  ok   F0 anchor: the honest emission at ${honest} is ACCEPTED (the floor is not red-on-everything)`);
  } catch (e) { console.log(`  RED  F0 anchor: the honest emission was REFUSED — ${String(e.message).slice(0, 200)}`); bad++; }

  const d = mkdtempSync(join(tmpdir(), 'stepmain-stale-'));
  const art = join(d, 'stepmain_step_r8_finalize.json');
  copyFileSync(honest, art);

  // (F1) THE MEASURED DEFECT: an artifact with no provenance at all — a `/tmp` survivor from an
  //      earlier session. This is the exact shape that scored GREEN with a `Jul 29` mtime.
  leg('F1 unstamped artifact (a /tmp survivor from a previous session)',
    () => requireFreshArtifact({ artifact: art, cone, emitCmd: EMIT_CMD }));

  // (F2) STAMPED, BUT FROM A SOURCE CONE THAT HAS SINCE MOVED — the assembly changed and nobody
  //      re-emitted. Content leg, and it survives any amount of `touch`ing.
  const stamp = JSON.parse(rd(join(LEAN_DIR, 'EMIT-PROVENANCE.json'), 'utf8'));
  const moved = JSON.parse(JSON.stringify(stamp));
  moved.cone.digest = `${'0'.repeat(63)}1`;
  moved.cone.files_detail = (moved.cone.files_detail ?? []).map((f, i) => (i === 0 ? { ...f, sha: 'deadbeef' } : f));
  moved.artifacts = { 'stepmain_step_r8_finalize.json': createHash('sha256').update(rd(art)).digest('hex') };
  writeFileSync(join(d, 'EMIT-PROVENANCE.json'), JSON.stringify(moved));
  leg('F2 stamped from a cone that has since moved (the assembly changed, nobody re-emitted)',
    () => requireFreshArtifact({ artifact: art, cone, emitCmd: EMIT_CMD }));

  // (F3) A CORRECT STAMP AND THE WRONG ARTIFACT — leg 2. The stamp's cone is right, but the file
  //      under the stamped name is not the one that emission produced: a rung swapped in from a
  //      different `DREGG_SM` shape, a truncated write, a stamp carried over from another run.
  const good = JSON.parse(JSON.stringify(stamp));
  good.cone = { ...good.cone, digest: cone.digest, files_detail: cone.files.map((f) => ({ rel: f.rel, sha: f.sha })) };
  good.artifacts = { 'stepmain_step_r8_finalize.json': createHash('sha256').update(rd(art)).digest('hex') };
  writeFileSync(join(d, 'EMIT-PROVENANCE.json'), JSON.stringify(good));
  const swapped = JSON.parse(rd(art, 'utf8'));
  swapped.num_rows = (swapped.num_rows ?? 0) + 1;
  writeFileSync(art, JSON.stringify(swapped));
  leg('F3 correct stamp, but the artifact under the stamped name is NOT the one it vouches for',
    () => requireFreshArtifact({ artifact: art, cone, emitCmd: EMIT_CMD }));

  // ⚑ (F3b) THE ANCHOR THAT PAID FOR F3's PREDECESSOR. A fresh `git` checkout stamps checkout-time
  //      mtimes on every source, so an honest artifact is ALWAYS "older than its own cone" there.
  //      The mtime leg this replaced refused exactly that, MEASURED from a clean `git worktree add
  //      HEAD` extract — every CI clone would have read STALE. This leg keeps the retirement
  //      answerable: back-date the artifact four days, leave the content legs satisfied, and it must
  //      still be ACCEPTED.
  copyFileSync(honest, art);
  good.artifacts = { 'stepmain_step_r8_finalize.json': createHash('sha256').update(rd(art)).digest('hex') };
  writeFileSync(join(d, 'EMIT-PROVENANCE.json'), JSON.stringify(good));
  const old = new Date('2026-07-29T03:15:00Z');
  utimesSync(art, old, old);
  try {
    requireFreshArtifact({ artifact: art, cone, emitCmd: EMIT_CMD });
    console.log('  ok   F3b fresh-checkout anchor: a correct emission with an ANCIENT mtime is ACCEPTED (mtime is not a leg)');
  } catch (e) { console.log(`  RED  F3b: mtime alone refused a correct emission — every fresh clone would read STALE: ${String(e.message).slice(0, 120)}`); bad++; }

  // (F4) THE FIXTURE LEG: the committed `.gz` whose sidecar names a cone the tree no longer has.
  //      This is the sibling defect — a fixture that predated a fix read 8/8 and 228/228 falsely.
  const sidecar = join(d, 'fixture.provenance.json');
  const fixProv = JSON.parse(rd(fileURLToPath(LEAN_FIXTURE_PROV), 'utf8'));
  writeFileSync(sidecar, JSON.stringify({ ...fixProv, cone: { ...fixProv.cone, digest: `${'f'.repeat(63)}0` } }));
  leg('F4 committed fixture whose sidecar names a cone the tree no longer has',
    () => requireFreshFixture({ fixture: LEAN_FIXTURE, sidecar, cone, emitCmd: EMIT_CMD, refreshCmd: REFRESH_CMD }));

  console.log();
  if (bad) { console.log(`stepmain-region-conformance --stale-self-test: ${bad} LEG(S) FAILED`); process.exit(1); }
  console.log('stepmain-region-conformance --stale-self-test: 6 legs green (2 anchors + 4 stale shapes REFUSED, each naming staleness)');
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };

// ⚑ OPTION (a), FIRST: emit the input, so for this run there is no stale path to read at all. Done
// BEFORE the cone is hashed for grading so the stamp and the check see the same tree.
if (argv.includes('--emit')) {
  const { readdirSync } = await import('node:fs');
  runLeanEmit({
    driver: EMIT_DRIVER, dir: LEAN_DIR, env: EMIT_ENV, label: 'stepmain step rungs',
    glob: () => readdirSync(LEAN_DIR).filter((f) => f.endsWith('.json') && f.startsWith('stepmain_')).map((f) => `${LEAN_DIR}/${f}`),
  });
}

const cone = leanConeDigest(EMIT_DRIVER);
const { spec, publicInputSize, gates } = await loadCircuit('step-zkapp-proved');
const M = normalizeMina(publicInputSize, gates);
let loaded;
try {
  loaded = loadLeanSide(arg('--lean'), cone);
} catch (e) {
  // ⚠ REFUSE, DO NOT WARN. A warning inside a green run is invisible, so a stale input exits
  // NON-ZERO here and never reaches the conformance verdict at all.
  console.error(`\n${e.message}\n`);
  console.error(`   cone: ${cone.files.length} Dregg2 modules under ${cone.root}, digest ${cone.digest.slice(0, 16)}…`);
  process.exit(3);
}
const { src, fixture, witness, prov, j: leanJson } = loaded;
const L = normalizeLean(leanJson);
const R = measure(M, L, fixture, witness);

if (argv.includes('--stale-self-test')) {
  if (!existsSync(LEAN_DEFAULT)) { console.error('--stale-self-test needs a live emission to use as the ANCHOR; run --emit first'); process.exit(2); }
  await staleSelfTest(cone, arg('--lean') ?? LEAN_DEFAULT);
  if (!argv.includes('--self-test') && !argv.includes('--falsify')) process.exit(0);
}

if (argv.includes('--refresh-fixture')) {
  const { gzipSync } = await import('node:zlib');
  const { writeFileSync } = await import('node:fs');
  const slim = JSON.stringify({ name: leanJson.name, public_input_size: leanJson.public_input_size, num_rows: leanJson.num_rows, probe_rows: leanJson.probe_rows, gates: leanJson.gates });
  writeFileSync(LEAN_FIXTURE, gzipSync(Buffer.from(slim), { level: 9 }));
  // ⚑ The sidecar is written in the SAME action, never as a follow-up step somebody can forget: a
  // fixture and a sidecar that disagree is the fail-open wearing the fix's clothes.
  const rec = writeFixtureSidecar(LEAN_FIXTURE_PROV, {
    fixture: LEAN_FIXTURE, cone, from: src,
    extra: { gates: leanJson.gates.length, probe_rows: (leanJson.probe_rows ?? []).length,
             num_rows: leanJson.num_rows, public_input_size: leanJson.public_input_size },
  });
  console.log(`refreshed fixtures/stepmain-step-r8-finalize-gates.json.gz from ${src} (${leanJson.gates.length} gates)`);
  console.log(`   + sidecar stepmain-step-r8-finalize-gates.provenance.json — cone ${rec.cone.digest.slice(0, 16)}… over ${rec.cone.files} modules, HEAD ${String(rec.git.head).slice(0, 9)}`);
  process.exit(0);
}
// ⚑ NO `--report` BRANCH HERE. What stood here exited 0 before the verdict; see the header. The
// dump it wanted is printed unconditionally by `extra` below, so the flag is announced and inert.
if (argv.includes('--report'))
  console.log('   ⚠ `--report` is INERT: the per-region dump below is printed on EVERY invocation, and this run GRADES.\n'
    + '     (Until 2026-08-03 this flag exited 0 here, before the conformance verdict.)');

await runOracle({
  shape: 'gates',
  label: `verify_one region conformance — Lean ${leanJson.name} vs mina ${spec.stem.slice(0, 44)}… (gate-by-gate)`,
  reference: () => referenceVector(R),
  candidate: () => candidateVector(R),
  extra: () => {
    report(R, src, M, L, prov, cone);
    if (argv.includes('--falsify')) falsify(M, leanJson, witness);
  },
});
