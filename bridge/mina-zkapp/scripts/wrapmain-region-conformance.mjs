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
// ⚠ AND THE HONEST HEADLINE: five sub-circuits of `wrap_main` are assembled today (the Fq
// transcript, `to_field_checked`, the branch selection, the public tie, and W-KEY — `choose_key`
// plus the index sponge, which is what makes `index_digest` DERIVED). The four gate FAMILIES
// that carry `wrap-transaction`'s curve work — VarBaseMul 2417, EndoMul 2528, CompleteAdd 492 and
// most of Generic 3521 — are W-XHAT / W-FTCOMM / W-COMBINE / W-BULLET and are NOT emitted. This
// diff reports that as ABSENT REGIONS with their measured Mina sizes, so the gap is a number in the
// report rather than a silence.
//
// USAGE — ⚠ EVERY invocation is green-or-bust. There is no non-gating mode in this file.
//   node scripts/wrapmain-region-conformance.mjs                 # green-or-bust
//   node scripts/wrapmain-region-conformance.mjs --report        # …+ the per-region dump. STILL GRADES.
//   node scripts/wrapmain-region-conformance.mjs --lean <path>   # a specific rung emission
//   node scripts/wrapmain-region-conformance.mjs --falsify       # prove the diff BITES
//   node scripts/wrapmain-region-conformance.mjs --emit          # ⚑ emit the input first, then grade
//   node scripts/wrapmain-region-conformance.mjs --emit --refresh-fixture   # ⚑ re-snapshot the gz
//
// ⚑ EXIT CODES.  0 conform · 1 divergence (blob facts or the conformance vector) · 3 stale Lean input.
// ⚠ 2026-08-03: `--report` used to `exit(process.exitCode ?? 0)` BEFORE the vector diff, so it
// printed every divergence and exited 0 — a GREEN that was a formatting success. Fixed; and the
// blob-only legs now grade before the Lean side is loaded at all, so a stale tree no longer means
// this file measured nothing.
//
// The Lean side defaults to `/tmp/pickles-wrapmain/wrapmain_wrap_<TOP_RUNG>.json`, and the emission's
// own `name` is CHECKED against `TOP_RUNG` — a lower rung REFUSES (exit 3) instead of grading. Produced by
//   (cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)

// ⚑ FRESHNESS (2026-08-02). This read `/tmp/pickles-wrapmain/…json` with `existsSync` +
// `readFileSync` and nothing else — the WRAP half of the fail-open MEASURED on the step half, where a
// four-day-old artifact scored GREEN, exit 0. Same floor now applies: the emission must carry an
// `EMIT-PROVENANCE.json` stamp naming the Lean source cone, that cone is re-hashed FROM THE CURRENT
// TREE, and a mismatch REFUSES (exit 3) naming staleness. `--emit` makes the gate emit its own input
// so there is no stale path to read at all. See `emit-provenance.mjs`.
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { gunzipSync } from 'node:zlib';
import {
  isStale, leanConeDigest, requireFreshArtifact, requireFreshFixture, runLeanEmit, writeFixtureSidecar,
} from './emit-provenance.mjs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

const WRAP_DIR = '/tmp/pickles-wrapmain';
const WRAP_DRIVER = 'Dregg2/Circuit/Emit/EmitWrapMainJson.lean';
const WRAP_EMIT_ENV = { DREGG_WM: 'wrap' };
const WRAP_EMIT_CMD = '(cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)'
  + '   — or let the gate do it:  node scripts/wrapmain-region-conformance.mjs --emit';

const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
const PERMUTS = 7;
// ⚑ Tock/Fq — the VESTA base / PALLAS scalar prime, the wrap circuit's own field
// (`curves/src/pasta/fields/fq.rs`). The step diff uses `pN`; using it here would silently
// re-interpret every negative coefficient.
const FQ = 28948022309329048855892746252171976963363056481941647379679742748393362948097n;
const FP = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;

// ⚑⚑ THE TOP RUNG IS A CONSTANT, AND READING ANY OTHER ONE IS A REFUSAL.
// ⚠ 2026-08-03, MEASURED AND FIXED HERE. This file's default was `…_w5_key.json` while the Lean
// assembly's top rung had moved TWO rungs past it. Unattended, the gate then read a rung that has
// no curve work in it at all, printed `VarBaseMul  mina 2417  lean 0  ⚠ ABSENT`, matched that
// against a LEDGER entry which still said `lean 0`, and EXITED 0. A green that measured the wrong
// object. Two structural changes stop it recurring, and neither is a warning:
//   (1) `TOP_RUNG` derives the default path, the fixture name and the sidecar name from ONE string,
//       so re-pointing is one edit and a half-re-pointed gate cannot exist;
//   (2) the emission's own `name` field is CHECKED against `TOP_RUNG` and a mismatch REFUSES
//       (exit 3, `isStale`), so pointing `--lean` at a lower rung is a refusal rather than a grade;
//   (3) `EMITTED_FAMILIES` names the gate families the top rung is known to emit, and ANY of them
//       measuring zero is a hard exit-1 BEFORE the vector diff — an ABSENT verdict for a family the
//       assembly actually emits can no longer be laundered through the ledger.
// ⚑⚑ AND `rungsUpto` IS A TREE, SO "THE TOP RUNG" IS A CHOICE — MADE HERE, NOT INHERITED.
// ⚠ 2026-08-04, MEASURED AND RE-POINTED. This constant read `w8_ftcomm` while the assembly had
// grown SIX rungs past it, so the gate graded 7120 of the 10593 probe-free rows the deepest rung
// emits and called the missing curve work an "absent region".
// `KimchiWrapMain.lean:5132`'s `rungsUpto` branches THREE ways off `.prev` (w9_prev), and each
// branch has its own tip — there is no single maximum:
//     w9_prev ─┬─ w10_finalize ── w11_finsponge   (W-FINALIZE, W-FINSPONGE)
//              ├─ w11_wraphack ── w12_close       (W-WRAPHACK, W-CLOSE)
//              └─ w10_combine  ── w11_bullet      (W-COMBINE, W-BULLET)
// THE CHOICE IS `w11_bullet`, and the reason is what this file measures. This gate is a GADGET
// diff — it grades curve-ladder bodies and Generic selector halves — and `w11_bullet` is the only
// rung on which all three curve families reach Mina's own count exactly: VarBaseMul 2417/2417,
// EndoMul 2528/2528, CompleteAdd 492/492. The other two tips carry no curve work at all past the
// trunk (w12_close adds 640 rows, w10_finalize 1008, both Poseidon/Generic), so pointing here loses
// nothing this file can see and gains every ladder it exists to grade.
// ⚠ WHAT THIS RUNG DOES NOT COVER, said rather than implied: W-FINALIZE's and W-WRAPHACK's four
// sponges. That is the `poseidon/count` ledger row (mina 261 permutations / lean 89) and it is
// UNCHANGED by the re-point — both `w8_ftcomm` and `w11_bullet` carry 979 Poseidon rows. The rung
// UNION is the object `wrapmain-shape-diff.mjs` grades, by prefix-stripping the three branches and
// verifying the prefix relation on the emitted rows; a single-rung gate cannot be the union and
// does not pretend to be.
// ⚑ 2026-08-05: `w11_finsponge` IS emitted now — `EmitWrapMainJson`'s loop runs all FIFTEEN rungs
// and the harness proves it — so the sentence that used to sit here ("a `Rung` constructor with a
// `rungOwn` arm and NO emitted artifact") is retired. It is still not the TOP RUNG for THIS gate,
// and that is a deliberate choice with the same reason as before: `w11_finsponge` adds two Fq
// sponges (122 `(Poseidon × 11, Zero)` blocks at `prevs = 2`) and no curve ladder, so it carries
// nothing this gadget-diff grades. The rung UNION — where those 122 blocks DO count — is
// `wrapmain-shape-diff.mjs`'s object, and that file assembles all fifteen.
const TOP_RUNG = 'w11_bullet';
const LEAN_DEFAULT = `/tmp/pickles-wrapmain/wrapmain_wrap_${TOP_RUNG}.json`;
// ⚑ THE COMMITTED FIXTURE. ⚠ 2026-08-03: the comment that used to sit here announced this fixture
// as "added 2026-08-03" and explained why an unreproducible gate is a bad gate — and the `.gz` was
// NEVER COMMITTED, in this branch or any other (`git log --all -- 'fixtures/wrapmain*'` is empty).
// So `haveFix` was permanently false, `requireFreshFixture` was unreachable, and the
// `fixture/in-sync-with-live-emission` leg could never fire. A documented fixture is not a
// committed one. It is committed now, under the top rung's name, and the freshness floor applies to
// it exactly as to a live emission — two content legs plus the git leg.
const FIXTURE_STEM = `wrapmain-wrap-${TOP_RUNG.replace(/_/g, '-')}-gates`;
const LEAN_FIXTURE = new URL(`../fixtures/${FIXTURE_STEM}.json.gz`, import.meta.url);
const LEAN_FIXTURE_PROV = new URL(`../fixtures/${FIXTURE_STEM}.provenance.json`, import.meta.url);
const WRAP_REFRESH_CMD = 'node scripts/wrapmain-region-conformance.mjs --emit --refresh-fixture';
// ⚑ Families the TOP RUNG emits. Zero for any of these means the gate is reading a lower rung (or
// the assembly regressed); either way it is a RED, never an "absent region" the ledger may excuse.
// ⚠ 2026-08-04: EndoMul USED to be excluded here with the note "it is genuinely absent (W-COMBINE,
// W-BULLET) and the ledger is the right home for a gap that is real." W-COMBINE and W-BULLET landed
// (`37abfb884`), and at `w11_bullet` EndoMul measures 2528 against Mina's 2528. The exclusion is
// retired with the gap.
const EMITTED_FAMILIES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
// Which §13 sub-circuits each curve family's rows belong to — carried here now that the three
// `absent/…` ledger rows (which used to hold this attribution) have retired at parity.
const WHERE_EMITTED = {
  VarBaseMul: '§13 W-XHAT + W-FTCOMM',
  EndoMul: '§13 W-COMBINE + W-BULLET',
  CompleteAdd: '§13 W-XHAT + W-COMBINE + W-BULLET',
};

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

/** The gz fixture carries GATES ONLY — the same slim shape the step half commits. */
const slimWrap = (j) => JSON.stringify({ name: j.name, public_input_size: j.public_input_size,
  num_rows: j.num_rows, probe_rows: j.probe_rows, gates: j.gates });

function loadLeanSide(explicit, cone) {
  const live = explicit ?? LEAN_DEFAULT;
  const haveLive = existsSync(live);
  const haveFix = existsSync(LEAN_FIXTURE);
  if (!haveLive && !haveFix)
    throw new Error(`no Lean wrap emission: neither ${live} nor the committed fixture. Produce it with\n   ${WRAP_EMIT_CMD}`);
  // ⚑ REFUSE, DO NOT WARN. Two CONTENT legs, both from `emit-provenance.mjs`: an unstamped
  // artifact, one stamped from a cone that has since moved (SOURCE), or one whose own sha256 is not
  // the sha256 the stamp recorded (ARTIFACT) is REFUSED here — not read and scored. Plus the GIT
  // leg: a stamp whose emit cone was uncommitted at its own HEAD is not reproducible by anyone.
  // ⚠ There is deliberately NO mtime leg. One was written and RETIRED the same night (`7d9a20bef`,
  // `31b12026f`): it refused an honest artifact from a clean `git worktree` extract, because git
  // stamps checkout-time mtimes, so every CI clone would have read STALE. This comment used to
  // claim that leg; it does not exist, and `emit-provenance.mjs`'s F3b reds if anyone re-adds it.
  let src, text, prov;
  if (haveLive) {
    prov = requireFreshArtifact({ artifact: live, cone, emitCmd: WRAP_EMIT_CMD });
    src = live; text = slimWrap(JSON.parse(readFileSync(live, 'utf8')));
  } else {
    prov = requireFreshFixture({ fixture: LEAN_FIXTURE, sidecar: LEAN_FIXTURE_PROV, cone,
      emitCmd: WRAP_EMIT_CMD, refreshCmd: WRAP_REFRESH_CMD });
    src = 'fixture'; text = gunzipSync(readFileSync(LEAN_FIXTURE)).toString('utf8');
  }
  // ⚠ NOT a fallback. When both exist the LIVE emission is what gets measured — but the two must
  // AGREE, and a disagreement is a RED of its own (`conform:fixture/in-sync-with-live-emission`)
  // rather than a silently-older shape being scored.
  let fixture = 'absent';
  if (haveLive && haveFix) {
    const a = createHash('sha256').update(text).digest('hex');
    const b = createHash('sha256').update(gunzipSync(readFileSync(LEAN_FIXTURE))).digest('hex');
    fixture = a === b ? 'in sync'
      : `STALE: live ${a.slice(0, 12)}… != fixture ${b.slice(0, 12)}… — the wrap assembly moved; refresh with --refresh-fixture`;
    src = a === b ? `${live} (== fixture)` : `${live} (⚠ FIXTURE STALE)`;
  }
  // ⚑ THE RUNG CHECK. The emission NAMES itself (`renderWrapCircuit`'s `name`), so the gate can
  // refuse an artifact for a rung it was not written to grade instead of scoring it. This is the
  // leg that would have caught the `w5_key` default: a lower rung is `isStale`, exit 3, named.
  const j = JSON.parse(text);
  const want = `wrapmain_wrap_${TOP_RUNG}`;
  if (j.name !== want) {
    const e = new Error(`STALE Lean emission: this gate grades ${want}, and ${src} names itself `
      + `"${j.name}". Re-emit the top rung and re-point, do not grade a lower one.\n   ${WRAP_EMIT_CMD}`);
    e.stale = true;
    throw e;
  }
  return { src, fixture, prov, j };
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
// ⚑ 2026-08-04 — THREE `absent/…` ROWS RETIRED, AND NOT BY DELETION. `absent/VarBaseMul`
// (§13 W-XHAT + W-FTCOMM), `absent/EndoMul` (§13 W-COMBINE + W-BULLET) and `absent/CompleteAdd`
// (§13 W-XHAT + W-COMBINE + W-BULLET) each said `lean 0`. All three regions have landed, and at
// `w11_bullet` all three measure Mina's own count EXACTLY — 2417/2417, 2528/2528, 492/492.
// An allowance whose gap has closed is not deleted into a silence here: the three families now
// carry POSITIVE `conform:curve-family/…` legs (see `measure`), so a regression from parity is a
// red on the family itself rather than the reappearance of a ledger row nobody would re-add.
const LEDGER = {
  'poseidon/count': {
    why: '§13 W-FINALIZE + W-WRAPHACK',
    expect: 'mina 261 permutations / lean 89',
    note: 'the transcript sponge of `wrap_verifier.ml:516-646` is assembled (61 permutations), and '
      + 'so is W-KEY\'s INDEX SPONGE (`:521-530`) — 56 coordinates at rate 2 plus the squeeze, '
      + 'exactly 28 more. What is not: the two `finalize_other_proof` sponges (W-FINALIZE) and the '
      + 'two `hash_messages_for_next_wrap_proof` sponges (W-WRAPHACK).',
  },
  'ems/count': {
    why: '§13 W-FINALIZE + W-PREV + the 16-bit width',
    expect: 'mina 19 chains of 8 / lean 42',
    note: 'ours are `lowest_128_bits`\' two halves per challenge. Upstream also runs '
      + '`assert_n_bits ~n:16` (`wrap_main.ml:208`, a 1-row chain) and `finalize_other_proof`\'s own '
      + 'ξ′/r′ lifts, which are W-PREV and W-FINALIZE.',
  },
  'pi/width': {
    why: '§10 census — 23 of Mina\'s 40 wrap statement words are derived here',
    // ⚠ 2026-08-04: was `lean 22`, which was `w8_ftcomm`'s width. `w9_prev` exposes ONE more word
    // (`messages_for_next_step_proof`, KimchiWrapMain.lean:1245-1248), and every rung above it —
    // including this gate's `w11_bullet` — carries it. `w11_wraphack` adds a 24th; that branch is
    // not this rung's, so 23 is the number here and 24 is the union's.
    expect: 'mina 40 / lean 23',
    note: 'the 17 not exposed are wrap slots 0–4, 9 (W-FINALIZE), 11–12 (W-WRAPHACK) and 30–39 (the '
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
    // ⚠ 2026-08-04, RE-MEASURED AT `w11_bullet`. Was `664/926` — `w8_ftcomm`'s halves. The three
    // new families are W-COMBINE/W-BULLET's: [0 0 1 -1 5] x51 and [0 0 1 -1 -5] x3 are `add_fast`'s
    // slope rows, [0 0 1 4 0] / [5 1 -1 0 0] / [1 1 0 0 -1] the fold seams. They are counted, not
    // excused — a family that GROWS here is red exactly as one that appears.
    expect: '1885/2466 match | x163 [0 0 0 0 0] | x138 [1 -1 0 0 0] | x135 [K 0 -1 0 0] '
      + '| x65 [1 -2 -1 0 0] | x51 [0 0 1 -1 5] | x4 [1 16 -1 0 0] | x3 [0 0 1 -1 -5] '
      + '| x3 [0 0 1 4 0] | x3 [5 1 -1 0 0] | x2 [0 0 1 1 -1] | x2 [1 0 -1 -1 0] '
      + '| x2 [1 1 0 0 -1] | x2 [1 4 -1 0 0] | x1 [1 -1 0 0 6] | x1 [1 0 -1 0 -1] '
      + '| x1 [1 1 0 0 1] | x1 [1 1 1 -1 -1] | x1 [1 3 -1 0 0] | x1 [16 0 -1 0 0] '
      + '| x1 [K -1 0 0 1] | x1 [K 1 0 0 K]',
    note: 'Generic selector halves this assembly emits whose SHAPE FAMILY (constants collapsed to K, '
      + 'sign-normalized) Snarky never emits in `wrap-transaction`, ATTRIBUTED ONE BY ONE: '
      + '[0 0 0 0 0] = the empty second half of an odd `packHalves` run (a row-economy cost, not a '
      + 'constraint); [1 -1 0 0 0] = our `cEq` ties, which Snarky expresses by UNIONING the two '
      + 'variables in one sigma class instead of spending a row; [1 16 -1 0 0] [1 3 -1 0 0] '
      + '[16 0 -1 0 0] [1 4 -1 0 0] = the two `Pseudo.choose` folds and `Branch_data.Checked.pack`, '
      + 'which upstream emits as ZERO rows because their coefficients are constants and '
      + '`Checked.mul` takes its `Constant` branch (`utils.ml:81-88`); [K 0 -1 0 0] = W-KEY\'s '
      + '`choose_key` fold — SAME cause, and it is the biggest single instance of it: '
      + '`wrap_main.ml:218-219` passes the step keys through `Inner_curve.constant`, so every '
      + '`b * coordinate` is `Cvar.scale` and every reduce is Cvar addition, and upstream pays only '
      + '`Util.seal`\'s ONE row per coordinate (`util.ml:65-76`) — 56 rows against our 56 x branches '
      + 'fold halves; [1 0 -1 0 -1] [1 0 -1 -1 0] = '
      + "`ones_vector`'s `value <- value && not (...)` recurrence (`util.ml:57-60`), likewise a Cvar "
      + 'linear combination upstream; [0 0 1 1 -1] = `Field.equal`\'s `z_inv*z = 1 - r` '
      + '(`utils.ml:44-48`), which Snarky DOES constrain but renders through `assert_r1cs` into a '
      + 'differently-arranged Generic half. Every one is this file being STRICTER or spending a row '
      + 'where Snarky spends none — none is a missing constraint. See §13\'s "stricter than '
      + 'upstream" note.',
  },
};

// ── ⚑ THE BLOB FACTS — every leg that reads MINA'S BLOBS ALONE ───────────────────────────────────
// Split out of `measure` deliberately. Not one of these reads the Lean emission, so they are
// gradeable when the Lean input is stale — and until 2026-08-03 a stale input meant this file
// measured NOTHING AT ALL, because the freshness floor exits 3 before `measure` is ever called.
// `measure` folds them back into `R.conform` so the report and the green-or-bust vector are
// unchanged; `main` grades them BEFORE the Lean side loads.
function blobFacts(M, M2) {
  const F = [];
  const add = (name, ref, cand) => F.push({ name, ref, cand });
  const MG = M.gates, MG2 = M2.gates;

  // (0) ⚑ THE SECOND SOURCE. `wrap-blockchain` is an independently compiled `wrap_main`; its
  // NON-GENERIC stream must equal `wrap-transaction`'s or every fact below is about one zkApp.
  const nonGeneric = (G) => G.filter((g) => g.typ !== 'Generic');
  const ngA = nonGeneric(MG), ngB = nonGeneric(MG2);
  add('two-blobs/non-generic-count', ngA.length, ngB.length);
  add('two-blobs/non-generic-typ-stream',
    createHash('sha256').update(ngA.map((g) => g.typ).join(',')).digest('hex').slice(0, 16),
    createHash('sha256').update(ngB.map((g) => g.typ).join(',')).digest('hex').slice(0, 16));
  add('two-blobs/non-generic-coeffs',
    createHash('sha256').update(ngA.map((g) => g.coeffs.join('|')).join(';')).digest('hex').slice(0, 16),
    createHash('sha256').update(ngB.map((g) => g.coeffs.join('|')).join(';')).digest('hex').slice(0, 16));
  add('two-blobs/public-input-size', M.pi, M2.pi);

  // (0b) ⚑ THE FIELD, RECOVERED FROM THE BLOB RATHER THAN RESTATED.
  //
  // ⚠ WHAT THIS BLOCK USED TO BE, and why it is being replaced rather than adjusted:
  //     conform('field/modulus', FQ.toString(), FQ.toString());
  // The constant against itself. It is green for ANY value of `FQ` — including `FP`, including a
  // typo — so the one line in this file that claims "the wrap side is in Fq" carried no measurement
  // behind it at all. The comment above it conceded "there is no intrinsic way to tell an Fq element
  // from an Fp one by looking at it", which is true of ONE element and false of a whole blob:
  //
  //   q - p = 86663725065984043395317760, so [p, q) is a WINDOW no Fp-encoded value can land in.
  //
  // MEASURED (2026-08-03, `loadCircuit` blobs at their pinned md5):
  //   wrap-transaction   78075 coeffs, max = q-1 exactly,  8022 of them in [p, q)
  //   wrap-blockchain    73425 coeffs, max = q-1 exactly,  6754 of them in [p, q)
  //   step-zkapp-proved 156495 coeffs, max = p-1 exactly,     0 of them in [p, q)
  //
  // So the modulus is RECOVERABLE: `-1` is a Generic selector coefficient Snarky emits everywhere,
  // no coefficient can exceed the modulus, hence `max + 1` IS the modulus. The step blob recovers
  // `p` by the same arithmetic — which is exactly the confusion the old line pretended to guard.
  // Both wrap blobs are recovered independently, so this is two sources against one constant.
  const recover = (X) => {
    const cs = X.gates.flatMap((g) => g.coeffs).map(BigInt);
    const max = cs.reduce((a, b) => (b > a ? b : a), 0n);
    return { q: (max + 1n).toString(), aboveP: cs.filter((c) => c >= FP && c < FQ).length, n: cs.length };
  };
  const rA = recover(M), rB = recover(M2);
  add('field/modulus-recovered-from-wrap-transaction', FQ.toString(), rA.q);
  add('field/modulus-recovered-from-wrap-blockchain', FQ.toString(), rB.q);
  // …and the positive half, which does not depend on `-1` being present: a blob carrying ANY
  // coefficient in [p, q) cannot be an Fp encoding. Stated as `> 0` and not as the count, so a blob
  // refresh that moves 8022 does not red, but a step-side blob relabelled as wrap does.
  add('field/wrap-transaction-carries-values-no-Fp-encoding-can', true, rA.aboveP > 0);
  add('field/wrap-blockchain-carries-values-no-Fp-encoding-can', true, rB.aboveP > 0);
  return F;
}

// ── the measurement ───────────────────────────────────────────────────────────────────────────────
function measure(M, M2, L, fixture = 'absent') {
  const MG = M.gates, LG = L.gates;
  const R = { conform: [], diverge: [], regions: [], absent: [] };
  const conform = (name, ref, cand) => R.conform.push({ name, ref, cand });
  const diverge = (key, form) => R.diverge.push({ key, form });

  for (const e of blobFacts(M, M2)) conform(e.name, e.ref, e.cand);

  // the committed fixture must track the live emission, or this run scored a shape nobody ships
  conform('fixture/in-sync-with-live-emission', fixture === 'absent' ? 'absent' : 'in sync', fixture);

  // (0c) ⚑ THE FIELD, LEAN SIDE. Every Lean coefficient that is "small negative" must be
  // small-negative in Fq, i.e. `q - c` and not `p - c` — a step-side emission relabelled as wrap is
  // what leg two catches. The bite that closes the rest is `--falsify`'s "a coefficient reduced mod
  // p instead of mod q", which moves the Generic family census; and the Poseidon whole-digest below
  // is the positive evidence, since it matches Mina's own fq_kimchi constants byte for byte.
  const allLean = LG.flatMap((g) => g.coeffs).map(BigInt);
  conform('field/coeffs-in-range', true, allLean.every((c) => c >= 0n && c < FQ));
  conform('field/no-mod-p-small-negatives', true,
    !allLean.some((c) => c > FP - 1000n && c < FP));

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

  // (3) THE THREE CURVE FAMILIES — at parity, partially emitted, or absent. THREE STATES, NOT TWO.
  // ⚠ 2026-08-04. This block used to fire `absent/${k}` only when lean measured EXACTLY 0, so the
  // middle state was SILENT: at `w8_ftcomm` VarBaseMul measured 2213 against Mina's 2417 and
  // CompleteAdd 248 against 492, and neither the ledger nor the vector said a word — the 204- and
  // 244-row gaps appeared only in a report section headed "what this assembly does not emit",
  // beside the number that proved it did. A family that is PARTIALLY emitted is now `partial/${k}`,
  // which is unledgered and therefore red, and a family AT PARITY gets a positive conform leg that
  // reds if it ever falls back.
  const cen = (G) => { const h = {}; for (const g of G) h[g.typ] = (h[g.typ] ?? 0) + 1; return h; };
  const cm = cen(MG), cl = cen(LG);
  for (const k of ['VarBaseMul', 'EndoMul', 'CompleteAdd']) {
    const m = cm[k] ?? 0, l = cl[k] ?? 0;
    R.absent.push({ family: k, mina: m, lean: l, state: l === m ? 'parity' : l === 0 ? 'absent' : 'partial' });
    if (l === m) conform(`curve-family/${k}`, `${m} rows, at parity`, `${l} rows, at parity`);
    else if (l === 0 && m > 0) diverge(`absent/${k}`, `mina ${m} rows / lean 0`);
    else diverge(`partial/${k}`, `mina ${m} rows / lean ${l}`);
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

  console.log('\n── (3) THE THREE CURVE FAMILIES — at parity / partial / absent');
  for (const a of R.absent) {
    const mark = a.state === 'parity' ? '✓ AT PARITY' : a.state === 'absent' ? '⚠ ABSENT' : `⚠ PARTIAL — ${a.mina - a.lean} rows short`;
    const why = LEDGER[`absent/${a.family}`]?.why ?? LEDGER[`partial/${a.family}`]?.why ?? WHERE_EMITTED[a.family] ?? 'UNRECORDED';
    console.log(`   ${a.family.padEnd(14)} mina ${String(a.mina).padStart(5)} rows   lean ${String(a.lean).padStart(5)}   ${mark}   → ${why}`);
  }

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

// ── ⚑ THE RED PATH FOR THE BLOB FACTS, and for `--report`'s exit code ─────────────────────────────
// `--falsify` bends the LEAN side and needs a fresh emission. This one bends the MINA side, so it
// runs in any tree and covers exactly the two things repaired on 2026-08-03: the recovered modulus
// (which replaced `FQ.toString()` vs `FQ.toString()`) and `--report`'s exit code.
//
// ⚠ THE BEND HOOK IS FAIL-CLOSED. `DREGG_WRAPMAIN_BEND` can only substitute a WRONG reference blob,
// so the only thing it can do to a run is make it RED. There is no env var in this file that can
// make a run green.
const BEND = process.env.DREGG_WRAPMAIN_BEND ?? '';
async function bentReference() {
  switch (BEND) {
    // The exact confusion the old `field/modulus` line pretended to guard: the STEP circuit, which
    // is Fp, loaded where `wrap_main` belongs.
    case 'step-blob': return await loadCircuit('step-zkapp-proved');
    // The minimal bend: drop every `q-1` coefficient to `q-2`, so `max + 1` recovers `q-1`.
    case 'shave-max': {
      const c = await loadCircuit('wrap-transaction');
      const gates = c.gates.map((g) => ({ ...g, coeffs: g.coeffs.map((h) => {
        const v = BigInt('0x' + Buffer.from(h, 'hex').reverse().toString('hex'));
        if (v !== FQ - 1n) return h;
        const w = (FQ - 2n).toString(16).padStart(64, '0');
        return Buffer.from(w, 'hex').reverse().toString('hex');
      }) }));
      return { ...c, gates };
    }
    default: return null;
  }
}

async function selfTest() {
  const { execFileSync } = await import('node:child_process');
  const self = fileURLToPath(import.meta.url);
  console.log('── wrapmain-region-conformance --self-test (the blob-fact red path + `--report`\'s exit code) ──\n');
  const legs = [];
  const leg = (name, ok, detail) => { legs.push({ name, ok, detail }); console.log(`   ${ok ? 'ok  ' : 'RED '} ${name.padEnd(56)} ${detail}`); };

  // (1) THE HONEST ANCHOR. A red path that reds on everything proves nothing.
  const honest = blobFacts(M, M2);
  const hBad = honest.filter((e) => String(e.ref) !== String(e.cand));
  leg('anchor: the honest blobs conform', hBad.length === 0, `${honest.length - hBad.length}/${honest.length} legs`);

  // (2) THE LINE THIS REPLACED COULD NOT HAVE CAUGHT ANY OF IT. Stated as a measurement, so the
  //     claim "it was decoration" is checked here and not only asserted in a comment.
  leg('the retired `FQ.toString() vs FQ.toString()` is green under EVERY bend',
    FQ.toString() === FQ.toString(), 'true — it never read a blob at all');

  // (3) + (4) the two bends, each as a CHILD PROCESS with `--report`, so what is measured is the
  //     script's real exit code under the flag that used to excuse it.
  for (const [bend, why] of [['step-blob', 'the Fp step circuit loaded as the wrap reference'],
                             ['shave-max', 'every q-1 coefficient shaved to q-2']]) {
    let code = 0, out = '';
    try {
      out = execFileSync(process.execPath, [self, '--report'],
        { env: { ...process.env, DREGG_WRAPMAIN_BEND: bend }, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    } catch (e) { code = e.status ?? -1; out = `${e.stdout ?? ''}${e.stderr ?? ''}`; }
    const named = /RED  blob:field\/modulus-recovered-from-wrap-transaction/.test(out);
    leg(`--report + ${bend}`, code === 1 && named,
      `exit ${code}${named ? ', and it NAMES field/modulus-recovered-from-wrap-transaction' : ', but the modulus leg did not name itself'} — ${why}`);
  }

  const bad = legs.filter((l) => !l.ok).length;
  console.log(bad
    ? `\nwrapmain-region-conformance --self-test: ${bad} LEG(S) FAILED`
    : `\nwrapmain-region-conformance --self-test: ${legs.length} legs green (1 honest anchor + 2 bends that exit 1 under --report)`);
  process.exit(bad ? 1 : 0);
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };

const bent = await bentReference();
const a = bent ?? await loadCircuit('wrap-transaction');
if (bent) console.log(`⚠ DREGG_WRAPMAIN_BEND=${BEND} — the reference blob is DELIBERATELY WRONG. This run must be RED.`);
const b = await loadCircuit('wrap-blockchain');
const M = normalizeMina(a.publicInputSize, a.gates);
const M2 = normalizeMina(b.publicInputSize, b.gates);

if (argv.includes('--self-test')) await selfTest();

// ⚑ THE BLOB FACTS ARE GRADED HERE — before the Lean side is even looked for. The freshness floor
// below exits 3 on a stale emission, which is right, but it meant that in a tree whose Lean cone had
// moved this file measured NOTHING: not the two-blob cross-check, not the field. These legs read
// only Mina's own compiled blobs, so they are answerable in any tree, and a run that cannot reach
// the conformance verdict still reds if one of them breaks.
{
  const bf = blobFacts(M, M2);
  const bad = bf.filter((e) => String(e.ref) !== String(e.cand));
  for (const e of bad) console.log(`RED  blob:${e.name}\n     ref:  ${e.ref}\n     cand: ${e.cand}`);
  if (bad.length) {
    console.log(`\nwrapmain-region-conformance: ${bad.length} BLOB FACT(S) RED over ${bf.length} — the reference side is wrong, so nothing below is worth grading`);
    process.exit(1);
  }
  console.log(`   blob facts: ${bf.length}/${bf.length} (2 wrap_main blobs cross-checked; Fq recovered from both as max-coefficient + 1)`);
}

// ⚑ Emit the input FIRST when asked, so for that run there is no stale path to read.
if (argv.includes('--emit')) {
  const { readdirSync } = await import('node:fs');
  runLeanEmit({
    driver: WRAP_DRIVER, dir: WRAP_DIR, env: WRAP_EMIT_ENV, label: 'wrapmain wrap rungs',
    glob: () => readdirSync(WRAP_DIR).filter((f) => f.endsWith('.json') && f.startsWith('wrapmain_')).map((f) => `${WRAP_DIR}/${f}`),
  });
}
const wrapCone = leanConeDigest(WRAP_DRIVER);
let leanSide;
try {
  leanSide = loadLeanSide(arg('--lean'), wrapCone);
} catch (e) {
  console.error(`\n${e.message}\n`);
  if (isStale(e)) console.error(`   cone: ${wrapCone.files.length} Dregg2 modules under ${wrapCone.root}, digest ${wrapCone.digest.slice(0, 16)}…`);
  process.exit(isStale(e) ? 3 : 1);
}
const { src, fixture: wrapFixture, prov: wrapProv, j: leanJson } = leanSide;
if (wrapProv) console.log(`   lean emission: ${src}\n   emitted ${wrapProv.emitted_at ?? wrapProv.refreshed_at} · cone ${wrapCone.digest.slice(0, 16)}… over ${wrapCone.files.length} modules (VERIFIED)`
  + (wrapProv.git?.head ? ` · HEAD ${wrapProv.git.head.slice(0, 12)}${wrapProv.git.cone_dirty_at_head?.length ? ` ⚠ ${wrapProv.git.cone_dirty_at_head.length} cone file(s) dirty: ${wrapProv.git.cone_dirty_at_head.slice(0, 3).join(', ')}` : ' (cone CLEAN at HEAD)'}` : ''));

// ⚑ REFRESH THE COMMITTED FIXTURE, sidecar written in the SAME action. A fixture and a sidecar that
// disagree is the fail-open wearing the fix's clothes; and `writeFixtureSidecar` REFUSES outright
// when the emit cone was dirty at HEAD, so an unreproducible snapshot cannot be created here at all.
if (argv.includes('--refresh-fixture')) {
  const { gzipSync } = await import('node:zlib');
  const { writeFileSync } = await import('node:fs');
  writeFileSync(LEAN_FIXTURE, gzipSync(Buffer.from(slimWrap(leanJson)), { level: 9 }));
  const rec = writeFixtureSidecar(LEAN_FIXTURE_PROV, {
    fixture: LEAN_FIXTURE, cone: wrapCone, from: src,
    extra: { gates: leanJson.gates.length, probe_rows: (leanJson.probe_rows ?? []).length,
             num_rows: leanJson.num_rows, public_input_size: leanJson.public_input_size },
  });
  console.log(`refreshed fixtures/${FIXTURE_STEM}.json.gz from ${src} (${leanJson.gates.length} gates)`);
  console.log(`   + sidecar ${FIXTURE_STEM}.provenance.json — cone ${rec.cone.digest.slice(0, 16)}… over ${rec.cone.files} modules, HEAD ${String(rec.git.head).slice(0, 9)}`);
  process.exit(0);
}
const L = normalizeLean(leanJson);
const R = measure(M, M2, L, wrapFixture);

// ⚑ `--report` PRINTS, IT DOES NOT EXCUSE. It used to `process.exit(process.exitCode ?? 0)` right
// here, skipping the vector diff entirely: every divergence in the report below was rendered and
// then discarded, so a `--report` run reported GREEN for a FORMATTING success. It is now a
// PRINTING MODIFIER on the one gating path — the dump happens first, then the same green-or-bust
// verdict every other invocation gets. There is deliberately NO non-gating mode in this file: a
// reader who wants the dump of a red state gets the dump AND the non-zero exit, which is correct.
if (argv.includes('--report')) report(R, src, M, L);

const ref = referenceVector(R), cand = candidateVector(R);
const byName = new Map(ref.map((e) => [e.name, e.value]));
let fails = 0;
// ⚑ THE ABSENT-FAMILY FLOOR, AND IT IS NOT LEDGERABLE. A family the top rung is known to emit
// measuring ZERO is the exact shape of the failure this file shipped: `VarBaseMul mina 2417 /
// lean 0 ⚠ ABSENT`, matched against a ledger entry that still said `lean 0`, exit 0. The ledger
// exists for gaps that are REAL (EndoMul is one); it may not excuse a family the assembly emits.
for (const k of EMITTED_FAMILIES) {
  if ((R.census.lean[k] ?? 0) === 0) {
    console.log(`RED  absent-family/${k}\n     ${k} measured 0 on the Lean side while ${TOP_RUNG} emits it`
      + ` (mina ${R.census.mina[k] ?? 0}).\n     This is a gate reading the wrong rung or an assembly regression — NOT a ledgerable absence.`);
    fails++;
  }
}
for (const e of cand) {
  const r = byName.get(e.name);
  if (r === undefined) { console.log(`RED  ${e.name}\n     UNEXPECTED: ${e.value}`); fails++; }
  else if (r !== e.value) { console.log(`RED  ${e.name}\n     ref:  ${r}\n     cand: ${e.value}`); fails++; }
}
for (const e of ref) if (!cand.some((c) => c.name === e.name)) { console.log(`RED  ${e.name}\n     MISSING from the candidate vector`); fails++; }
if (argv.includes('--falsify')) falsify(M, M2, leanJson);
if (fails) { console.log(`\nwrapmain-region-conformance: ${fails} FAILURE(S) over ${cand.length} entries`); process.exit(1); }
console.log(`wrapmain-region-conformance: ${cand.length} entries conform (2 independently compiled wrap_main blobs cross-checked)`);
