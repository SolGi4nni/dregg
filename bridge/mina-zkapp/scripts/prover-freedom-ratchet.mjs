// prover-freedom-ratchet.mjs — ⚑ THE GATE THAT CAN SEE A FREE CELL.
//
// ⚑ WHY THIS FILE EXISTS. `stepmain-region-conformance.mjs` and `wrapmain-region-conformance.mjs`
// are SHAPE instruments. They diff gate types, run lengths, coefficients, wires and Generic selector
// families against Mina's own compiled blobs, and they are good at that — but a statement word with
// NO in-circuit source has the same ladder shape as one with a source, and a free booleanity row is
// BYTE-IDENTICAL to a derived one. Measured 2026-08-03: not one prover-chosen cell was visible to
// either ledger as such. Words 11 and 39, `vCipBit`, `branch_data`'s two mask bits, `G`/`z₁`/`z₂`,
// the structural pad lane and the wrap transcript's 119 supplied words were all INVISIBLE to the
// gate surface. The census that found them (`KimchiStepProverChoice.lean`,
// `KimchiWrapProverChoice.lean`) had to build three NEW instruments — `AOp.wit` slots,
// `envVarsNoRowReads` and `occCount` — precisely because the conformance diffs cannot see freedom.
//
// ⚑ WHAT THIS GATE IS, EXACTLY, AND WHAT IT IS NOT.
// The census's counts are computed IN LEAN, by `native_decide`, over the ACTUAL emitted program —
// that is where the measurement lives and this file does not reproduce it. What Lean's own build
// CANNOT do is notice that a count went UP and was then written into the theorem. `native_decide`
// reds when `= 19` stops holding; the next commit edits it to `= 20` and the build is green again,
// with nineteen environment cells having quietly become twenty. THAT is the hole this closes.
//
//   Lean says   "the emitted object has N free cells here"   (a proof over the real object)
//   this says   "N must not exceed the CEILING committed below" (a decision, made once, in git)
//
// Two independent sources. Neither is a restatement of the other, which is the difference between a
// gate and a pin against its own definition.
//
// ⚑ IT IS A RATCHET, NOT A SNAPSHOT. Every ceiling has a DIRECTION:
//   `max` — a free-cell count. It may FALL freely (that is the work); a RISE is RED.
//   `eq`  — a structural identity (`WRAP_PRIMARY_LEN = 40`, `nItems = 120`). Any move is RED.
//   `min` — a count of things that are DERIVED rather than supplied. A FALL is RED.
// ⚠ The ceilings below were RE-BASELINED against the restructured census on 2026-08-03 (the
// per-pin moves are named in the block itself) and are a COMMITTED
// DECISION, not "whatever was there". A guard ratchet in this tree was silently re-baselined at
// inflated counts this session and certified them green; re-baselining here is a commit that says
// which number moved, in which direction, and why the new one is the right one.
//
// ⚠ WHAT IT DOES NOT DO. It does not re-derive freedom from the artifact. Freedom is "no constraint
// writes this cell", which is a fact about the CONSTRAINT SYSTEM, not about the placed gate list —
// the emitted JSON carries gate types, coefficients, wires and a witness, and a free cell and a
// derived one are the same bytes there. That is the whole finding this file is downstream of. What
// the artifact IS used for is BINDING: the shape numbers the census's counts are stated at
// (`shapeStep`, `shapeWrap` → rows, PI width, probe rows) are checked against an emission on disk,
// so the pins cannot drift onto a circuit nobody emitted.
//
// USAGE — ⚠ EVERY invocation is green-or-bust. There is no non-gating mode in this file.
//   node scripts/prover-freedom-ratchet.mjs              # the pin ratchet (no Lean build, no artifact)
//   node scripts/prover-freedom-ratchet.mjs --self-test  # ⚑ prove it reds when a count RISES
//   node scripts/prover-freedom-ratchet.mjs --artifact   # + bind the shape pins to a fresh emission
//   node scripts/prover-freedom-ratchet.mjs --list       # print every pin, its value and its ceiling
//                                                        #   (STILL GRADES — `--list` only adds output)
//
// EXIT: 0 every pin within its ceiling · 1 a pin moved the wrong way, or a pin could not be READ
//       · 3 `--artifact` and the emission is stale.
//
// ⚠ A PIN THAT CANNOT BE READ IS RED, NEVER SKIPPED. If the census theorem is renamed, deleted, or
// its statement reshaped so the extractor misses it, this file exits 1 naming the pin. A ratchet
// that silently stops watching is the "documented, not detected" defect wearing a gate's clothes —
// and a DELETED census pin is exactly how an instrument gets retired without anyone deciding to.
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { isStale, leanConeDigest, META_ROOT, requireFreshArtifact } from './emit-provenance.mjs';
import { join } from 'node:path';

const STEP_SRC = 'Dregg2/Circuit/Emit/KimchiStepProverChoice.lean';
const WRAP_SRC = 'Dregg2/Circuit/Emit/KimchiWrapProverChoice.lean';
const WRAP_DRIVER = 'Dregg2/Circuit/Emit/EmitWrapMainJson.lean';
const WRAP_ARTIFACT = '/tmp/pickles-wrapmain/wrapmain_wrap_w5_key.json';
const WRAP_EMIT_CMD = '(cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)';

// ── ⚑ THE COMMITTED CEILINGS ──────────────────────────────────────────────────────────────────────
// Each row: the census THEOREM it is read out of, the sub-expression that carries the number, the
// ceiling, the direction, and — the part that makes re-baselining a decision — WHAT THE NUMBER IS.
//
// `expr` is matched against the theorem's statement text with the number replaced by a capture, so
// a pin whose SHAPE changes (a different variable, a different schedule) fails to extract and reds
// rather than silently matching something else. `A Display Name Is Not A Key`: these are keyed by
// the theorem name AND the expression, never by position.
const PINS = [
  // ── STEP ────────────────────────────────────────────────────────────────────────────────────────
  // ⚑ RE-BASELINED 2026-08-03, and every move is named. The census was RESTRUCTURED (its
  // committed-shape numbers moved into ONE command, `the_step_prover_choice_census`, over a single
  // `occIxs` pass) and this file was still watching the pre-restructure theorem names, so eight of
  // its thirteen step pins had become UNREADABLE — which under this file's own rule is RED, not
  // skipped, and is why they are repointed here rather than left to rot.
  //   · free-witness total 11 → 10   `permClaimed` was an `eEq perm permClaimed` over a variable
  //                                  occupying exactly ONE cell — an assert that could not fail. It
  //                                  is DELETED. Pinned per PROGRAM now (1 + 9), never as a total,
  //                                  because the 9 that has been quoted as the assembly's is R8's.
  //   · unread env cells 19 → 20     −1 (`permClaimed`'s assert output) +2 (the lazy-sponge rung's
  //                                  post-absorb lanes). A RISE, and a re-baseline of a `max` pin,
  //                                  so it is stated here explicitly rather than absorbed.
  //   · assert outputs 18 → 17       the same deletion, from the other side.
  //   · `vDomLog2` 1 → 2             a STRENGTHENING: `Branch_data.typ`'s `~assert_16_bits` chain
  //                                  landed, so the word is no longer solved-for freely.
  //   · pad lane 1 → 2               ⚑ the ONE was the vacuous reading. `vTPad` owns the `w = 0`
  //                                  pin row's cell AND the transcript lane it pads, in ONE σ class
  //                                  — which is what makes the pin BIND the absorb. A count of one
  //                                  would mean the pin and the absorb are in different classes.
  //   · `vCipBit` count pin RETIRED  the bit is DERIVED since this rung (it is ladder 0's `s_odd`),
  //                                  so "how many cells does it own" is no longer the question. Its
  //                                  slot is taken by a `min` pin on `vMaskPack`'s gate rows, whose
  //                                  FALL is the corresponding loss.
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: '(witSlots tStep.ft.fp.prog).length', ceiling: 1, dir: 'max',
    what: "R6's DECLARED FREE-WITNESS SLOTS at the committed step shape — `denomInv`, `ftBuild`'s witnessed-inverse device. `AOp.wit` is a straight-line slot with no defining row. A SECOND is a new cell the prover picks." },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: '(witSlots tStep.fin.fp.prog).length', ceiling: 9, dir: 'max',
    what: "R8's nine — `xiHi` plus four `Field.equal` (inverse, bit) pairs. Pinned separately from R6's because the nine that gets quoted as the ASSEMBLY's is this one alone." },
  { src: 'step', thm: 'the_assembly_compiles_ten_free_witness_slots',
    expr: '(witSlots tS.fin.fp.prog).length', ceiling: 9, dir: 'max',
    what: "the same count at the smoke shape, so a slot that appears only at scale is still one pin away from visible." },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: '(envVarsNoRowReads (circuitEnv tStep) rowsStep).length', ceiling: 20, dir: 'max',
    what: 'ENVIRONMENT CELLS THE GRID NEVER READS at the committed shape — 17 `.aeq` output slots + `vDHi 0` (the dead ξ split) + two post-absorb lanes the lazy sponge no longer reads. Benign today because nothing reads them; a TWENTY-FIRST is a cell whose consumer nobody checked.' },
  { src: 'step', thm: 'the_grid_never_reads_twentytwo_smoke_environment_cells',
    expr: '(envVarsNoRowReads (circuitEnv tS) rowsS).length', ceiling: 22, dir: 'max',
    what: 'the same count at the smoke shape (22 = 20 + words 11/39, which have no ladder there).' },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: '((tStep.ft.fp.prog.toList ++ tStep.fin.fp.prog.toList).countP\n          (fun o => match o with | .aeq _ _ => true | _ => false))',
    ceiling: 17, dir: 'max',
    what: 'the assert-output share of the twenty. Keeps "twenty" a CENSUS: if the total holds while this falls, an unaccounted-for family appeared.' },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (vStmtWrapMsgs shapeStep)', ceiling: 1, dir: 'eq',
    what: 'WORD 11 `messages_for_next_wrap_proof` — no in-circuit source, reaching exactly its own `var_base_mul` counter. Pinned `eq`: MORE cells means a new consumer nobody weighed, FEWER means the ladder stopped reading it and `x_hat` no longer moves with the word.' },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (vStmtLookup shapeStep)', ceiling: 1, dir: 'eq',
    what: "WORD 39, the lookup `Opt`'s inner scalar. Same shape as word 11 and the same `eq` reasoning." },
  { src: 'step', thm: 'the_two_sourceless_statement_words_reach_only_their_own_ladder',
    expr: 'STMT_LOOKUP_VAL', ceiling: 0, dir: 'eq',
    what: "⚑ word 39's VALUE is upstream's own dummy — `~lookup_parameters:{ zero = { var = { challenge = Field.zero } } }` (`step_main.ml:90-95`). It was an invented `Challenge`-width fixture; `eq 0` is a FIDELITY pin, not a freedom one, and a non-zero here means the assembly re-invented a number Mina fixes." },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (bpZ1 shapeStep)', ceiling: 1, dir: 'eq',
    what: '`z₁` of the opening response — one cell, its `Shifted_value.Type2` split row: one equation in three unknowns, all three the prover\'s. This is the forgery surface `substituted_assembly_still_closes_equal_g` exhibits.' },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (bpZ2 shapeStep)', ceiling: 1, dir: 'eq', what: '`z₂`, the twin of `z₁`.' },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (vGx shapeStep)', ceiling: 5, dir: 'eq',
    what: "`G.x` — `assert_on_curve`'s two halves read it twice, plus segment D's absorb and the ladder base. `eq` because a FALL here means a curve check stopped reading the point." },
  { src: 'step', thm: 'the_branch_triple_is_pinned_by_the_suffix_row_and_the_16_bit_chain',
    expr: 'occCount rowsS (vMaskPack shapeSmoke)', ceiling: 3, dir: 'min',
    what: "⚑ DIRECTION INVERTED, and this pin REPLACES the retired `vCipBit` freedom count. `proofs_verified_mask`'s pack variable carries THREE gate rows since the `Prefix_mask` suffix half `m₀·(1−m₁) = 0` landed — the row that refuses the illegal `[1,0]`. A FALL is a refusal that left." },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (vDomLog2 shapeStep)', ceiling: 2, dir: 'eq',
    what: "`domain_log2` occupies TWO cells — `Branch_data.Checked.pack`'s equation AND the `~assert_16_bits` chain's `Field.Assert.equal n scalar` tie. It owned ONE (freely solved-for) until the 16-bit chain landed; `eq 2` is what keeps that chain from being dropped silently." },
  { src: 'step', thm: 'the_step_prover_choice_census',
    expr: 'occAt occStep (vTPad shapeStep)', ceiling: 2, dir: 'eq',
    what: 'THE ONE STRUCTURAL PAD LANE — the single rate-2 lane an odd item count leaves without an arrival. TWO cells: `transcriptRows`\' `w = 0` `Generic` pin AND the transcript lane itself, in one σ class. `eq 2`, because ONE would mean the pin and the lane are in different classes and the pin binds nothing.' },

  // ── WRAP ────────────────────────────────────────────────────────────────────────────────────────
  { src: 'wrap', thm: 'the_wrap_prover_choice_census',
    expr: '((absorbedWordVars tWrap).filter (fun v => occCount rowsWrapKey v == 1)).length',
    ceiling: 119, dir: 'max',
    what: '⚑ THE LARGEST FORGERY SURFACE IN EITHER ASSEMBLY: of the 120 field elements the wrap transcript absorbs, 119 own exactly one permutation cell — the absorb — so no row derives them. Choosing any one steers every challenge squeezed after it, and the first is item 1, so EVERY challenge is reachable. It falls as sub-circuits land (`w6_xhat` derives two more); it must never rise.' },
  { src: 'wrap', thm: 'the_wrap_prover_choice_census', expr: 'nItems shapeWrap', ceiling: 120, dir: 'eq',
    what: 'the transcript\'s item count. `eq`: this is the DENOMINATOR of the 119, and a ratchet whose denominator can drift is not a ratchet.' },
  { src: 'wrap', thm: 'the_wrap_prover_choice_census',
    expr: '(envVarsNoRowReads (circuitEnvAt tWrap .key) rowsWrapKey).length', ceiling: 21, dir: 'max',
    what: "ENVIRONMENT CELLS THE WRAP GRID NEVER READS — one per challenge, each a high chain's dead `hi` from a `split = false` `to_field_checked`. Benign; a rise means a NEW unread family." },
  { src: 'wrap', thm: 'the_wrap_prover_choice_census', expr: 'WRAP_UNCONSUMED.length', ceiling: 8, dir: 'max',
    what: "the named unconsumed classes. A NINTH class is a new region of the wrap statement nothing reads." },
  { src: 'wrap', thm: 'the_wrap_prover_choice_census', expr: 'shapeWrap.pubWords', ceiling: 22, dir: 'min',
    what: '⚑ DIRECTION INVERTED — this counts words the assembly DOES expose (22 of the 40 primary, against the 24 upstream actually pins). Exposing MORE is progress; a FALL is a word that stopped being tied to the public vector, which is a weakening.' },
  { src: 'wrap', thm: 'the_public_vector_gap_against_upstream_is_two_words', expr: 'WRAP_PRIMARY_LEN', ceiling: 40, dir: 'eq',
    what: "`wrap_main`'s primary length. `eq`: it is Mina's, not ours." },
  { src: 'wrap', thm: 'the_xhat_rung_derives_two_of_the_absorbed_words',
    expr: '((absorbedWordVars tSm).filter (fun v => occCount rowsSmXhat v == 1)).length', ceiling: 31, dir: 'max',
    what: "the smoke shape's supplied count at `w6_xhat` — 31 of 34, i.e. the ladder derives two more than `w5_key` does. Falls as rungs land." },
  { src: 'wrap', thm: 'the_xhat_rung_derives_two_of_the_absorbed_words',
    expr: '((absorbedWordVars tSm).filter (fun v => occCount rowsSmXhat v > 1)).length', ceiling: 3, dir: 'min',
    what: '⚑ DIRECTION INVERTED — the words some row CONSUMES. More is better; a fall means a derivation was lost.' },
];

// ── reading the pins out of the Lean the census actually proves ───────────────────────────────────
const SRC_PATH = { step: STEP_SRC, wrap: WRAP_SRC };

/** Slice a named theorem's STATEMENT (`theorem <name> :` … up to the `:= by`). Anything outside a
 *  statement — a docblock, a comment, a neighbouring theorem — cannot contribute a number, so a pin
 *  can never be satisfied by prose that merely mentions the count. */
function statementOf(text, thm) {
  const i = text.indexOf(`theorem ${thm} :`);
  if (i < 0) return null;
  const j = text.indexOf(':= by', i);
  if (j < 0) return null;
  return text.slice(i, j);
}

const escape = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
/** Whitespace-insensitive match of `expr <op> <number>`, capturing the number. Lean wraps lines, so
 *  the expression is matched with `\s+` standing in for any run of whitespace. */
function readPin(text, pin) {
  const st = statementOf(text, pin.thm);
  if (st === null) return { err: `theorem \`${pin.thm}\` is not in ${SRC_PATH[pin.src]} — renamed, deleted, or its statement no longer ends in \`:= by\`` };
  const body = escape(pin.expr).replace(/\s+/g, '\\s+');
  const re = new RegExp(`${body}\\s*(?:=|==)\\s*(\\d+)`);
  const m = st.match(re);
  if (!m) return { err: `\`${pin.expr}\` does not appear against a literal in \`${pin.thm}\` — the census's statement was reshaped and this ratchet stopped watching it` };
  const all = [...st.matchAll(new RegExp(re.source, 'g'))];
  if (all.length > 1) return { err: `\`${pin.expr}\` appears ${all.length} times in \`${pin.thm}\`; the pin is ambiguous and a ratchet must not guess` };
  return { value: Number(m[1]) };
}

const OK = { max: (v, c) => v <= c, min: (v, c) => v >= c, eq: (v, c) => v === c };
const ARROW = { max: '≤', min: '≥', eq: '=' };
const VERDICT = {
  max: 'ROSE — a prover-chosen cell was ADDED',
  min: 'FELL — a derivation was LOST',
  eq: 'MOVED — a structural identity is no longer what it was',
};

function grade(sources) {
  const rows = [];
  for (const pin of PINS) {
    const r = readPin(sources[pin.src], pin);
    rows.push({ pin, ...r, ok: r.err ? false : OK[pin.dir](r.value, pin.ceiling) });
  }
  return rows;
}

function printRows(rows, { verbose }) {
  for (const r of rows) {
    const head = `${r.ok ? 'ok  ' : 'RED '} ${r.pin.src}/${r.pin.thm}`;
    if (r.err) { console.log(`${head}\n       ⚑ UNREADABLE PIN: ${r.err}`); continue; }
    const line = `${r.pin.expr.replace(/\s+/g, ' ')} = ${r.value}  (ceiling ${ARROW[r.pin.dir]} ${r.pin.ceiling})`;
    console.log(`${head}\n       ${line}`);
    if (!r.ok) console.log(`       ⚑ ${VERDICT[r.pin.dir]}: ${r.value} against a committed ${ARROW[r.pin.dir]} ${r.pin.ceiling}\n       ${r.pin.what}`);
    else if (verbose) console.log(`       ${r.pin.what}`);
  }
}

// ── the artifact binding ──────────────────────────────────────────────────────────────────────────
// ⚠ NOT a freedom measurement — see the header. It answers ONE question: are the census's counts
// stated at the shape of a circuit that was actually emitted? A pin over `shapeWrap` is worth
// nothing if `shapeWrap` is not the thing on disk.
const ARTIFACT_PINS = [
  { key: 'name', want: 'wrapmain_wrap_w5_key', why: 'the rung the census states `rowsWrapKey` at. A different rung graded here would bind the pins to a circuit they are not about.' },
  { key: 'public_input_size', want: 22, why: '⚑ `shapeWrap.pubWords = 22` — the census pin, as the emitted circuit\'s OWN primary length. This is the one place a census number is answerable to bytes on disk.' },
  { key: 'num_rows', want: 1999, why: 'the `w5_key` rung\'s emitted row count (MEASURED 2026-08-03)' },
];

function bindArtifact() {
  const cone = leanConeDigest(WRAP_DRIVER);
  if (!existsSync(WRAP_ARTIFACT))
    return { code: 3, lines: [`⚑ --artifact: no emission at ${WRAP_ARTIFACT}. Emit it:  ${WRAP_EMIT_CMD}`] };
  try {
    requireFreshArtifact({ artifact: WRAP_ARTIFACT, cone, emitCmd: WRAP_EMIT_CMD });
  } catch (e) {
    return { code: isStale(e) ? 3 : 1, lines: [e.message] };
  }
  const j = JSON.parse(readFileSync(WRAP_ARTIFACT, 'utf8'));
  const lines = [];
  let bad = 0;
  for (const p of ARTIFACT_PINS) {
    const got = j[p.key];
    const ok = got === p.want;
    if (!ok) bad++;
    lines.push(`   ${ok ? 'ok  ' : 'RED '} artifact/${p.key.padEnd(20)} ${got} (want ${p.want}) — ${p.why}`);
  }
  lines.unshift(`   emission VERIFIED against cone ${cone.digest.slice(0, 16)}… over ${cone.files.length} modules`);
  return { code: bad ? 1 : 0, lines };
}

// ── ⚑ THE RED PATH ────────────────────────────────────────────────────────────────────────────────
// A ratchet nobody proves can go red is the defect it was built to close. Every leg here operates on
// an IN-MEMORY copy of the census sources, so nothing on disk is touched.
function selfTest(sources) {
  console.log('── prover-freedom-ratchet --self-test (a RISE must red; the honest census must not) ──\n');
  const legs = [];
  const leg = (name, ok, detail) => { legs.push(ok); console.log(`   ${ok ? 'ok  ' : 'RED '} ${name.padEnd(62)} ${detail}`); };

  // (1) THE ANCHOR. A ratchet that reds on everything proves nothing.
  const honest = grade(sources);
  const hBad = honest.filter((r) => !r.ok);
  leg('anchor: the census as committed', hBad.length === 0,
    `${honest.length - hBad.length}/${honest.length} pins within their ceilings`);

  // (2) EVERY `max` PIN, RAISED BY ONE. This is the exact motion the gate exists to catch: Lean's
  //     `native_decide` reds, somebody edits the theorem to the new number, and the build is green
  //     again with one more free cell in the circuit.
  let missed = 0, tested = 0;
  for (const pin of PINS.filter((p) => p.dir === 'max' || p.dir === 'eq')) {
    const bent = { ...sources };
    const st = statementOf(sources[pin.src], pin.thm);
    const body = escape(pin.expr).replace(/\s+/g, '\\s+');
    const re = new RegExp(`(${body}\\s*(?:=|==)\\s*)(\\d+)`);
    const raised = st.replace(re, (_, lead, n) => `${lead}${Number(n) + 1}`);
    if (raised === st) { missed++; continue; }
    bent[pin.src] = sources[pin.src].replace(st, raised);
    tested++;
    const rows = grade(bent);
    const hit = rows.find((r) => r.pin === pin);
    if (!hit || hit.ok) { missed++; console.log(`   RED  raising ${pin.thm}/${pin.expr.slice(0, 40)}… by one did NOT red`); }
  }
  leg('every `max`/`eq` pin, raised by one, reds', missed === 0, `${tested} pins bent, ${tested - missed} bit`);

  // (3) EVERY `min` PIN, LOWERED BY ONE — the inverted direction has to bite too, or "more is
  //     better" is an unchecked sentence.
  let mMissed = 0, mTested = 0;
  for (const pin of PINS.filter((p) => p.dir === 'min')) {
    const st = statementOf(sources[pin.src], pin.thm);
    const body = escape(pin.expr).replace(/\s+/g, '\\s+');
    const lowered = st.replace(new RegExp(`(${body}\\s*(?:=|==)\\s*)(\\d+)`), (_, lead, n) => `${lead}${Number(n) - 1}`);
    if (lowered === st) { mMissed++; continue; }
    mTested++;
    const rows = grade({ ...sources, [pin.src]: sources[pin.src].replace(st, lowered) });
    const hit = rows.find((r) => r.pin === pin);
    if (!hit || hit.ok) { mMissed++; console.log(`   RED  lowering ${pin.thm}/${pin.expr.slice(0, 40)}… by one did NOT red`); }
  }
  leg('every `min` pin, lowered by one, reds', mMissed === 0, `${mTested} pins bent, ${mTested - mMissed} bit`);

  // (4) A DELETED CENSUS THEOREM IS RED, NOT SKIPPED. This is how an instrument gets retired without
  //     anyone deciding to, and it is the failure mode a text-scraping ratchet is most exposed to.
  const victim = PINS[0];
  const gone = { ...sources, [victim.src]: sources[victim.src].replace(`theorem ${victim.thm} :`, `theorem ${victim.thm}_RENAMED :`) };
  const gRows = grade(gone);
  const gHit = gRows.find((r) => r.pin === victim);
  leg('a RENAMED census theorem reds (not silently skipped)', !!gHit && !gHit.ok && !!gHit.err,
    gHit?.err ? 'refused, naming the missing theorem' : 'NOT refused');

  // (5) A RESHAPED STATEMENT — the number is still there, the expression is not. A scraper that
  //     matched on the number alone would sail past this.
  const v2 = PINS.find((p) => p.dir === 'max');
  const reshaped = { ...sources, [v2.src]: sources[v2.src].replace(v2.expr, `(${v2.expr}).succ.pred`) };
  const rHit = grade(reshaped).find((r) => r.pin === v2);
  leg('a RESHAPED census statement reds', !!rHit && !rHit.ok && !!rHit.err,
    rHit?.err ? 'refused, naming the expression it stopped watching' : 'NOT refused');

  const bad = legs.filter((x) => !x).length;
  console.log(bad
    ? `\nprover-freedom-ratchet --self-test: ${bad} LEG(S) FAILED`
    : `\nprover-freedom-ratchet --self-test: ${legs.length} legs green (1 honest anchor + 4 red paths)`);
  return bad ? 1 : 0;
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const sources = {};
for (const [k, rel] of Object.entries(SRC_PATH)) {
  const p = join(META_ROOT, rel);
  if (!existsSync(p)) {
    console.error(`⚑ prover-freedom-ratchet: the ${k} census is MISSING at ${p}.\n`
      + '   This gate reads the counts out of the census that proves them. If the module was moved, move this pin table with it;\n'
      + '   if it was deleted, the free-cell instrument was deleted and that is the thing to report, not to skip.');
    process.exit(1);
  }
  sources[k] = readFileSync(p, 'utf8');
}

if (argv.includes('--self-test')) process.exit(selfTest(sources));

console.log('── prover-freedom-ratchet — the census\'s free-cell counts against their COMMITTED ceilings ──\n');
const rows = grade(sources);
printRows(rows, { verbose: argv.includes('--list') });

let code = rows.some((r) => !r.ok) ? 1 : 0;
if (argv.includes('--artifact')) {
  console.log('\n── artifact binding (shape only — freedom is not visible in the emitted bytes) ──');
  const a = bindArtifact();
  for (const l of a.lines) console.log(l);
  if (a.code !== 0) code = code || a.code;
}

const bad = rows.filter((r) => !r.ok).length;
console.log(bad
  ? `\nprover-freedom-ratchet: ${bad} PIN(S) RED over ${rows.length} — a prover-chosen cell moved the wrong way, or a pin stopped being readable.\n`
    + '   ⚠ Raising a ceiling is a COMMIT that says which count moved, in which direction, and why the new number is right.\n'
    + '     Re-baselining to "whatever the census says now" certifies the regression.'
  : `\nprover-freedom-ratchet: ${rows.length} pins within their committed ceilings (${PINS.filter((p) => p.dir === 'max').length} max · ${PINS.filter((p) => p.dir === 'eq').length} eq · ${PINS.filter((p) => p.dir === 'min').length} min)`);
process.exit(code);
