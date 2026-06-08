#!/usr/bin/env node
/**
 * gen-ontology-catalog.js — ANTI-DRIFT ontology generator.
 *
 * Emits `site/src/_includes/studio/ontology-catalog.generated.json`: a
 * machine-readable catalog of every dregg2 effect variant — constructor name,
 * wire mnemonic, typed args, a one-line semantics summary, and the
 * authorization facet it requires — generated DIRECTLY from the verified Lean
 * source of truth (not hand-written, so it cannot silently drift).
 *
 * Sources of truth (parsed, never copied):
 *   1. metatheory/Dregg2/Exec/TurnExecutorFull.lean
 *        - `inductive FullActionA` — the ~56 constructors, their typed args,
 *          and the `/-- … -/` doc-comment immediately preceding each (the
 *          per-effect semantics).
 *        - `def requiredFacetA : FullActionA → Authority.Auth` — the facet
 *          (write / grant / control) each effect demands.
 *   2. metatheory/Dregg2/Exec/FFI.lean
 *        - `def encodeActionW : FullActionA → String` — the wire mnemonic
 *          (`"bal"`, `"del"`, …) each constructor encodes to.
 *
 * The output is DETERMINISTIC (same source ⇒ byte-identical JSON) so a drift
 * check is a plain compare. Run `node site/tools/gen-ontology-catalog.js`;
 * pass `--check` to FAIL if the committed file is stale instead of writing it.
 *
 * This mirrors the app-framework `webgen.rs` ConstantsModule anti-drift pattern
 * (Rust const ⇒ JS), but at the ontology layer: Lean source ⇒ JSON catalog.
 */

'use strict';
const fs = require('fs');
const path = require('path');

// --- Locate the Lean source of truth (repo-root/metatheory/…). -------------
const SITE_DIR = path.resolve(__dirname, '..');
const REPO_ROOT = path.resolve(SITE_DIR, '..');
const META = path.join(REPO_ROOT, 'metatheory');
const F_EXEC = path.join(META, 'Dregg2', 'Exec', 'TurnExecutorFull.lean');
const F_FFI = path.join(META, 'Dregg2', 'Exec', 'FFI.lean');
const OUT = path.join(SITE_DIR, 'src', '_includes', 'studio', 'ontology-catalog.generated.json');

// The cell-program / predicate language source of truth (the doc-commented
// canonical enums), cross-checked against the JSON-projection view that the
// studio's instance inspectors actually consume.
const F_PROGRAM = path.join(REPO_ROOT, 'cell', 'src', 'program.rs');
const F_VIEW = path.join(REPO_ROOT, 'wasm', 'src', 'bindings.rs');
const OUT_PRED = path.join(SITE_DIR, 'src', '_includes', 'studio', 'predicate-catalog.generated.json');

// The node's thin-HTTP turn-submit schema — the ACTUAL JSON shape the live node
// accepts at POST /api/turns/submit. This is the source of truth for the
// Studio's "submit to a node" forms, so the composer cannot send a body the
// node would reject as malformed. Parsed from the `TurnEffectSpec` enum (and the
// `TurnActionSpec` / `SubmitTurnRequest` wrappers) in `node/src/api.rs`.
const F_NODE_API = path.join(REPO_ROOT, 'node', 'src', 'api.rs');
const OUT_SUBMIT = path.join(SITE_DIR, 'src', '_includes', 'studio', 'submit-schema.generated.json');

function read(p) {
  if (!fs.existsSync(p)) {
    console.error(`gen-ontology-catalog: missing source ${p}`);
    process.exit(2);
  }
  return fs.readFileSync(p, 'utf8');
}

// ---------------------------------------------------------------------------
// Parse `inductive FullActionA` — constructors + doc-comments + typed args.
// ---------------------------------------------------------------------------

/** Slice the `inductive FullActionA where … ` block (up to the next top-level def). */
function sliceInductive(src) {
  const start = src.indexOf('inductive FullActionA where');
  if (start < 0) throw new Error('FullActionA inductive not found');
  // Ends at the first top-level `def ` / `/-- **The per-asset…` boundary.
  const tail = src.slice(start);
  const end = tail.search(/\ndef ledgerDeltaAsset/);
  return tail.slice(0, end < 0 ? tail.length : end);
}

/** Collapse a multi-arg Lean binder group `(a b c : T)` into one entry per name. */
function expandBinder(group) {
  // group like "actor cell : CellId" or "id : Nat"
  const m = group.match(/^([^:]+):\s*(.+)$/);
  if (!m) return [];
  const names = m[1].trim().split(/\s+/).filter(Boolean);
  const type = m[2].trim();
  return names.map((name) => ({ name, type: normalizeType(type) }));
}

/** Map Lean types to a compact wire-facing label. */
function normalizeType(t) {
  return t
    .replace(/ℤ/g, 'Int')
    .replace(/\bAssetId\b/, 'AssetId(Nat)')
    .replace(/\bFieldName\b/, 'FieldName(String)')
    .trim();
}

/** Parse the parenthesized binder groups of a constructor signature line(s). */
function parseArgs(sig) {
  const args = [];
  // Match each top-level (...) binder group (no nested parens in FullActionA sigs).
  const re = /\(([^()]+)\)/g;
  let m;
  while ((m = re.exec(sig)) !== null) {
    for (const a of expandBinder(m[1])) args.push(a);
  }
  return args;
}

/** Extract a one-line semantics summary from a doc-comment.
 *
 * Many arms open with a dregg1 reference `\`Foo { … }\` (dregg1 \`apply_foo\`,
 * \`apply.rs:NN\`): <prose>` — we prefer the <prose> AFTER that ref-colon, then
 * cut at the first sentence-ending period, so the summary is the actual
 * semantics, not the dregg1 op name. Falls back to the whole first sentence. */
function firstSentence(doc) {
  if (!doc) return '';
  let s = doc.replace(/\s+/g, ' ').trim();
  // If it opens with a `…` (dregg1 `apply_*`, `apply.rs:NN`): <prose> reference,
  // take the prose AFTER the closing `):` (the ref may itself contain colons
  // inside backticks, so match the parenthesized ref group up to `):`).
  const refEnd = s.match(/^`[^`]+`\s*(?:—\s*[^(]*)?\([^)]*\):\s*/);
  if (refEnd) s = s.slice(refEnd[0].length);
  // Cut at the first sentence-ending period followed by space/end.
  const cut = s.search(/[.](\s|$)/);
  if (cut > 0) s = s.slice(0, cut + 1);
  return s.trim();
}

function parseConstructors(src) {
  const block = sliceInductive(src);
  const lines = block.split('\n');
  const ctors = [];
  let pendingDoc = '';
  let docBuf = null; // accumulating a /-- … -/ comment

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];

    // Doc-comment accumulation.
    if (docBuf !== null) {
      docBuf += ' ' + line.replace(/-\}?\s*$/, '').replace(/-->/, '');
      if (line.includes('-/')) {
        pendingDoc = docBuf
          .replace(/\/--/, '')
          .replace(/-\/.*$/, '')
          .trim();
        docBuf = null;
      }
      continue;
    }
    const docOpen = line.indexOf('/--');
    if (docOpen >= 0) {
      if (line.includes('-/')) {
        pendingDoc = line.slice(docOpen + 3).replace(/-\/.*$/, '').trim();
      } else {
        docBuf = line.slice(docOpen + 3);
      }
      continue;
    }
    // Plain `--` section comments reset nothing but aren't docs.
    if (/^\s*--/.test(line)) continue;

    // Constructor line: `  | name  (args…)…` possibly continued on next lines.
    const cm = line.match(/^\s*\|\s*([a-z][A-Za-z0-9]*)\b(.*)$/);
    if (cm) {
      const name = cm[1];
      let sig = cm[2];
      // Continuation lines (next lines that start with whitespace and `(`)
      let j = i + 1;
      while (
        j < lines.length &&
        /^\s+\(/.test(lines[j]) &&
        !/^\s*\|/.test(lines[j])
      ) {
        sig += ' ' + lines[j].trim();
        j++;
      }
      i = j - 1;
      ctors.push({
        ctor: name,
        args: parseArgs(sig),
        semantics: firstSentence(pendingDoc),
      });
      pendingDoc = '';
    }
  }
  return ctors;
}

// ---------------------------------------------------------------------------
// Parse `requiredFacetA` — ctor ⇒ facet (write|grant|control).
// ---------------------------------------------------------------------------

function parseFacets(src) {
  const start = src.indexOf('def requiredFacetA');
  if (start < 0) throw new Error('requiredFacetA not found');
  const tail = src.slice(start);
  const end = tail.search(/\ndef capFacetMaskA/);
  const block = tail.slice(0, end < 0 ? tail.length : end);
  const facets = {};
  const re = /\|\s*\.([a-zA-Z0-9]+)\b[^=]*=>\s*Authority\.Auth\.(\w+)/g;
  let m;
  while ((m = re.exec(block)) !== null) {
    facets[m[1]] = m[2];
  }
  return facets;
}

// ---------------------------------------------------------------------------
// Parse `encodeActionW` — ctor ⇒ wire mnemonic.
// ---------------------------------------------------------------------------

function parseWireMnemonics(src) {
  const start = src.indexOf('def encodeActionW');
  if (start < 0) throw new Error('encodeActionW not found');
  const tail = src.slice(start);
  const end = tail.search(/\ndef encodeActionsW/);
  const block = tail.slice(0, end < 0 ? tail.length : end);
  const wire = {};
  // Each arm: `  | .ctorName … => "{\"mnemonic\":[…`
  const re = /\|\s*\.([a-zA-Z0-9]+)\b[\s\S]*?=>\s*"\{\\"([a-z]+)\\":/g;
  let m;
  while ((m = re.exec(block)) !== null) {
    if (!(m[1] in wire)) wire[m[1]] = m[2];
  }
  return wire;
}

// ---------------------------------------------------------------------------
// Effect categorization (the §MA-* groupings from the Lean source comments).
// Derived from the wire mnemonic / ctor; kept as a small stable map so the
// browser can group + color.
// ---------------------------------------------------------------------------

function categoryOf(ctor) {
  const C = {
    balanceA: 'value', mintA: 'value', burnA: 'value', bridgeMintA: 'value',
    setFieldA: 'state', emitEventA: 'state', incrementNonceA: 'state',
    setPermissionsA: 'state', setVKA: 'state', makeSovereignA: 'state',
    refusalA: 'state', receiptArchiveA: 'state',
    delegate: 'authority', revoke: 'authority', introduceA: 'authority',
    delegateAttenA: 'authority', attenuateA: 'authority', dropRefA: 'authority',
    revokeDelegationA: 'authority', validateHandoffA: 'authority',
    refreshDelegationA: 'authority', exerciseA: 'authority',
    createCellA: 'lifecycle', createCellFromFactoryA: 'lifecycle', spawnA: 'lifecycle',
    cellSealA: 'lifecycle', cellUnsealA: 'lifecycle', cellDestroyA: 'lifecycle',
    createEscrowA: 'escrow', releaseEscrowA: 'escrow', refundEscrowA: 'escrow',
    createObligationA: 'escrow', fulfillObligationA: 'escrow', slashObligationA: 'escrow',
    createCommittedEscrowA: 'escrow', releaseCommittedEscrowA: 'escrow',
    refundCommittedEscrowA: 'escrow',
    noteSpendA: 'privacy', noteCreateA: 'privacy',
    sealA: 'seal', unsealA: 'seal', createSealPairA: 'seal',
    bridgeLockA: 'bridge', bridgeFinalizeA: 'bridge', bridgeCancelA: 'bridge',
    queueAllocateA: 'queue', queueEnqueueA: 'queue', queueDequeueA: 'queue',
    queueResizeA: 'queue', queueAtomicTxA: 'queue', queuePipelineStepA: 'queue',
    pipelinedSendA: 'queue',
    exportSturdyRefA: 'swiss', enlivenRefA: 'swiss', swissHandoffA: 'swiss',
    swissDropA: 'swiss',
  };
  return C[ctor] || 'other';
}

// ===========================================================================
// PREDICATE / CELL-PROGRAM LANGUAGE catalog.
//
// Source of truth: the doc-commented canonical Rust enums in
// `cell/src/program.rs` — `CellProgram`, `TransitionGuard`, `StateConstraint`.
// Cross-checked against the JSON-projection `StateConstraintView` /
// `CellProgramView` / `TransitionGuardView` in `wasm/src/bindings.rs` that the
// studio's instance inspectors (cell-program.js / predicate.js) actually
// consume — so the explanatory catalog and the live renderer cannot diverge.
// ===========================================================================

/** Slice a `pub enum Name {` … matching-brace block out of a Rust source. */
function sliceEnum(src, name) {
  const m = src.match(new RegExp(`pub enum ${name}\\s*\\{`));
  if (!m) throw new Error(`enum ${name} not found`);
  let i = m.index + m[0].length;
  let depth = 1;
  const start = i;
  for (; i < src.length && depth > 0; i++) {
    if (src[i] === '{') depth++;
    else if (src[i] === '}') depth--;
  }
  return src.slice(start, i - 1);
}

/** Strip `/// …` doc-comment lines into a single prose blob. */
function collectDoc(lines) {
  return lines
    .map((l) => l.replace(/^\s*\/\/\/\s?/, ''))
    .join(' ')
    .replace(/\s+/g, ' ')
    .replace(/\[`[^`]*`\]/g, '') // drop rustdoc intra-links
    .trim();
}

/** First sentence of a doc blob (predicate semantics are terse). */
function firstDocSentence(doc) {
  if (!doc) return '';
  const cut = doc.search(/[.](\s|$)/);
  return (cut > 0 ? doc.slice(0, cut + 1) : doc).trim();
}

/**
 * Parse the top-level variants of an enum block: `Name`, `Name { a: T, … }`,
 * or `Name(T)`. Returns `{ name, fields:[{name,type}], doc }` per variant,
 * skipping `// ───` section separators. Only top-level (depth-0) variants.
 */
function parseEnumVariants(block) {
  const lines = block.split('\n');
  const variants = [];
  let docBuf = [];
  let depth = 0;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trim();

    // Track brace depth from prior lines' net effect (handled below at capture).
    if (depth > 0) {
      // Inside a struct-variant body we already captured; count braces to exit.
      for (const ch of line) {
        if (ch === '{') depth++;
        else if (ch === '}') depth--;
      }
      continue;
    }

    if (trimmed.startsWith('///')) { docBuf.push(line); continue; }
    if (trimmed.startsWith('//')) { docBuf = []; continue; } // section sep / plain
    if (!trimmed) { continue; }
    if (trimmed.startsWith('#')) { continue; } // attribute

    // A variant head: `Ident` optionally followed by `{` or `(`.
    const vm = trimmed.match(/^([A-Z][A-Za-z0-9]*)\s*([{(])?/);
    if (!vm) { docBuf = []; continue; }
    const name = vm[1];
    const doc = firstDocSentence(collectDoc(docBuf));
    docBuf = [];
    const opener = vm[2];

    if (!opener) {
      // Unit variant `Name,`
      variants.push({ name, fields: [], doc });
      continue;
    }

    // Gather the field body across lines until the matching closer.
    const close = opener === '{' ? '}' : ')';
    let body = trimmed.slice(trimmed.indexOf(opener) + 1);
    if (!trimmed.includes(close)) {
      // multi-line — accumulate until depth balances
      let d = 1;
      for (const ch of body) { if (ch === opener) d++; else if (ch === close) d--; }
      let j = i + 1;
      while (j < lines.length && d > 0) {
        const ln = lines[j];
        for (const ch of ln) { if (ch === opener) d++; else if (ch === close) d--; }
        body += '\n' + (d >= 0 ? ln : ln);
        if (d <= 0) break;
        j++;
      }
      i = j;
    } else {
      body = body.slice(0, body.indexOf(close));
    }

    const fields = parseRustFields(body, opener);
    variants.push({ name, fields, doc });
  }
  return variants;
}

/** Parse `{ a: T, b: U }` or `(T, U)` field bodies, dropping rustdoc + attrs. */
function parseRustFields(body, opener) {
  // Strip nested doc-comments and inline comments inside the body.
  const clean = body
    .replace(/\/\/\/[^\n]*/g, '')
    .replace(/\/\/[^\n]*/g, '')
    .replace(/\}[^}]*$/, '') // tail after a closing brace (struct-variant)
    .trim();
  const fields = [];
  if (opener === '{') {
    for (const part of splitTopLevel(clean, ',')) {
      const p = part.trim();
      if (!p) continue;
      const cm = p.match(/^([a-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/s);
      if (cm) fields.push({ name: cm[1], type: normalizeRustType(cm[2]) });
    }
  } else {
    let idx = 0;
    for (const part of splitTopLevel(clean, ',')) {
      const p = part.trim();
      if (!p) continue;
      fields.push({ name: String(idx++), type: normalizeRustType(p) });
    }
  }
  return fields;
}

/** Split on `sep` at top level (not inside <>, (), []). */
function splitTopLevel(s, sep) {
  const out = [];
  let depth = 0, cur = '';
  for (const ch of s) {
    if ('<([{'.includes(ch)) depth++;
    else if ('>)]}'.includes(ch)) depth--;
    if (ch === sep && depth === 0) { out.push(cur); cur = ''; }
    else cur += ch;
  }
  if (cur.trim()) out.push(cur);
  return out;
}

/** Map Rust constraint types to a compact, browser-facing label. */
function normalizeRustType(t) {
  return t
    .replace(/\s+/g, ' ')
    .replace(/\bFieldElement\b/g, 'Field')
    .replace(/\bcrate::id::CellId\b/g, 'CellId')
    .replace(/\[u8;\s*32\]/g, 'Hash32')
    .replace(/\bVec<\(FieldElement,\s*FieldElement\)>/g, 'Vec<(Field,Field)>')
    .trim();
}

function buildPredicate() {
  const prog = read(F_PROGRAM);
  const view = read(F_VIEW);

  const cellProgram = parseEnumVariants(sliceEnum(prog, 'CellProgram'));
  const guards = parseEnumVariants(sliceEnum(prog, 'TransitionGuard'));
  const constraints = parseEnumVariants(sliceEnum(prog, 'StateConstraint'));

  // Cross-check: every canonical StateConstraint variant must have a JSON
  // projection in StateConstraintView (else the instance inspector can't show
  // it), and vice-versa. Report honestly.
  const viewVariants = new Set(
    parseEnumVariants(sliceEnum(view, 'StateConstraintView')).map((v) => v.name)
  );
  const canonNames = constraints.map((c) => c.name);
  const missingFromView = canonNames.filter((n) => !viewVariants.has(n));
  const extraInView = [...viewVariants].filter((n) => !canonNames.includes(n));

  // Which constraints are *locally evaluable* in the browser explainer (pure
  // post-state / (old,new) field comparison, no witness/proof/executor side
  // table)? Honest about model-vs-live: only these are checked for real.
  const LOCALLY_EVALUABLE = new Set([
    'FieldEquals', 'FieldGte', 'FieldLte', 'FieldLteField', 'SumEquals',
    'WriteOnce', 'Immutable', 'Monotonic', 'StrictMonotonic', 'FieldDelta',
    'FieldDeltaInRange', 'SumEqualsAcross', 'MonotonicSequence',
    'AllowedTransitions', 'AnyOf',
  ]);
  const enrichedConstraints = constraints.map((c) => ({
    name: c.name,
    fields: c.fields,
    semantics: c.doc,
    in_view: viewVariants.has(c.name),
    locally_evaluable: LOCALLY_EVALUABLE.has(c.name),
  }));

  return {
    schema: 'dregg-predicate-catalog-v1',
    generated_from: [
      'cell/src/program.rs (CellProgram, TransitionGuard, StateConstraint — canonical doc-commented enums)',
      'wasm/src/bindings.rs (StateConstraintView — the JSON projection the studio consumes; cross-checked)',
    ],
    note:
      'AUTOGENERATED by site/tools/gen-ontology-catalog.js from the verified ' +
      'Rust cell-program source. Do not edit by hand — regenerate.',
    cell_program_kinds: cellProgram.map((k) => ({
      kind: k.name, fields: k.fields, semantics: k.doc,
    })),
    transition_guards: guards.map((g) => ({
      kind: g.name, fields: g.fields, semantics: g.doc,
    })),
    constraint_count: enrichedConstraints.length,
    coverage: {
      constraints_in_view: enrichedConstraints.filter((c) => c.in_view).length,
      locally_evaluable: enrichedConstraints.filter((c) => c.locally_evaluable).length,
      missing_from_view: missingFromView,
      extra_in_view: extraInView,
    },
    constraints: enrichedConstraints,
  };
}

// ===========================================================================
// NODE TURN-SUBMIT SCHEMA.
//
// The Studio's submit step POSTs to the live node's POST /api/turns/submit. The
// node accepts a `SubmitTurnRequest { agent, nonce, fee, memo, actions }` whose
// `actions` are `TurnActionSpec { target?, method?, effects }` and whose effects
// are the `TurnEffectSpec` enum — a deliberately small JSON projection of the
// on-chain `Effect` (only the kinds a thin HTTP client needs: state writes,
// transfers, nonce bumps, events). The richer ~52 effects in the ontology go
// through the typed SDK signed-envelope path, NOT this HTTP form.
//
// We parse `TurnEffectSpec` straight from `node/src/api.rs` so the composer's
// node-submit forms cannot drift from the body the node actually deserializes.
// Each variant carries: its serde `kind` tag (snake_case), the per-field
// {name, type, optional, doc}, and the verified-Lean effect ctor it maps to.
// ===========================================================================

/** snake_case a Rust PascalCase ident, matching `#[serde(rename_all="snake_case")]`. */
function snakeCase(s) {
  return s.replace(/([a-z0-9])([A-Z])/g, '$1_$2').replace(/([A-Z]+)([A-Z][a-z])/g, '$1_$2').toLowerCase();
}

/** Map a Rust field type to a compact, browser-facing JSON-value label. */
function normalizeSubmitType(t) {
  const inner = t.replace(/^Option<(.+)>$/, '$1').trim();
  const base = inner
    .replace(/^Vec<[^>]+>$/, 'string[]')
    .replace(/\bString\b/g, 'hex/scalar string')
    .replace(/\bu64\b/g, 'u64')
    .replace(/\busize\b/g, 'usize');
  return base.trim();
}

/**
 * Parse a `#[serde(tag="kind", rename_all="snake_case")] enum TurnEffectSpec`.
 * Returns one record per variant: { kind, variant, doc, fields:[{name,type,optional,doc}] }.
 * Field-level `#[serde(default)]` ⇒ optional. `Option<…>` is also optional.
 */
function parseSubmitEffects(src) {
  const block = sliceEnum(src, 'TurnEffectSpec');
  const lines = block.split('\n');
  const variants = [];
  let docBuf = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    const trimmed = line.trim();
    if (trimmed.startsWith('///')) { docBuf.push(line); i++; continue; }
    if (trimmed.startsWith('#')) { docBuf = []; i++; continue; } // variant-level attr
    if (!trimmed) { i++; continue; }

    // Variant head `Name {`
    const vm = trimmed.match(/^([A-Z][A-Za-z0-9]*)\s*\{/);
    if (!vm) { docBuf = []; i++; continue; }
    const variant = vm[1];
    const vdoc = firstDocSentence(collectDoc(docBuf));
    docBuf = [];

    // Walk the struct body until the matching closing brace at depth 0.
    const fields = [];
    let pendingDefault = false;
    let fdoc = [];
    i++;
    let depth = 1;
    for (; i < lines.length; i++) {
      const fl = lines[i].trim();
      if (fl === '}' || fl === '},') { depth--; if (depth === 0) { i++; break; } continue; }
      if (fl.startsWith('///')) { fdoc.push(lines[i]); continue; }
      if (/#\[serde\([^)]*\bdefault\b/.test(fl)) { pendingDefault = true; continue; }
      if (fl.startsWith('#')) { continue; } // other attrs
      const fm = fl.match(/^([a-z_][A-Za-z0-9_]*)\s*:\s*([^,]+),?$/);
      if (fm) {
        const type = fm[2].trim();
        fields.push({
          name: fm[1],
          type: normalizeSubmitType(type),
          optional: pendingDefault || /^Option</.test(type),
          doc: firstDocSentence(collectDoc(fdoc)),
        });
        pendingDefault = false;
        fdoc = [];
      }
    }
    variants.push({ kind: snakeCase(variant), variant, doc: vdoc, fields });
  }
  return variants;
}

// Map each submit `kind` to the verified-Lean effect ctor it materializes into
// (api.rs `build_effect`: SetField→SetField, Transfer→Transfer, …; the on-chain
// Effect ctors correspond to FullActionA `setFieldA` / `balanceA` / `emitEventA`
// / `incrementNonceA`). Kept as a tiny stable map and CROSS-CHECKED below so a
// new submit variant without a known ctor is reported, not silently dropped.
const SUBMIT_KIND_TO_CTOR = {
  set_field: 'setFieldA',
  transfer: 'balanceA',
  emit_event: 'emitEventA',
  increment_nonce: 'incrementNonceA',
};

function buildSubmit(effects) {
  const api = read(F_NODE_API);
  const variants = parseSubmitEffects(api);
  const ctorByName = new Map(effects.map((e) => [e.ctor, e]));
  const submittable = variants.map((v) => {
    const ctor = SUBMIT_KIND_TO_CTOR[v.kind] || null;
    const cat = ctor ? ctorByName.get(ctor) : null;
    return {
      kind: v.kind,
      variant: v.variant,
      semantics: v.doc,
      fields: v.fields,
      ctor,
      category: cat ? cat.category : null,
      facet: cat ? cat.facet : null,
    };
  });
  const missingCtor = submittable.filter((s) => !s.ctor).map((s) => s.kind);
  return {
    schema: 'dregg-submit-schema-v1',
    generated_from: [
      'node/src/api.rs (TurnEffectSpec enum — the JSON projection POST /api/turns/submit deserializes)',
    ],
    note:
      'AUTOGENERATED by site/tools/gen-ontology-catalog.js from the node HTTP ' +
      'API source. This is the EXACT effect-JSON the live node accepts on the ' +
      'thin-HTTP submit path; the richer ontology effects go through the typed ' +
      'SDK signed-envelope path. Do not edit by hand — regenerate.',
    endpoint: '/api/turns/submit',
    request_shape: {
      agent: 'hex CellId (advisory; node derives + signs as itself)',
      nonce: 'u64',
      fee: 'u64',
      memo: 'string?',
      actions: '[{ target?: hex CellId, method?: string, effects: TurnEffect[] }]',
    },
    auth: 'Bearer token from POST /cipherclerk/unlock (loopback may be allowed before a passphrase is set)',
    effect_count: submittable.length,
    coverage: {
      submittable_of_ontology: submittable.filter((s) => s.ctor).length,
      missing_ctor: missingCtor,
    },
    effects: submittable,
  };
}

// ---------------------------------------------------------------------------
// Build the catalog.
// ---------------------------------------------------------------------------

function build() {
  const exec = read(F_EXEC);
  const ffi = read(F_FFI);

  const ctors = parseConstructors(exec);
  const facets = parseFacets(exec);
  const wire = parseWireMnemonics(ffi);

  const effects = ctors.map((c) => ({
    ctor: c.ctor,
    wire: wire[c.ctor] || null,
    category: categoryOf(c.ctor),
    facet: facets[c.ctor] || null,
    args: c.args,
    semantics: c.semantics,
  }));

  // Coverage cross-check: every constructor must have a facet; report wire gaps.
  const missingFacet = effects.filter((e) => !e.facet).map((e) => e.ctor);
  const missingWire = effects.filter((e) => !e.wire).map((e) => e.ctor);

  const catalog = {
    schema: 'dregg-ontology-catalog-v1',
    generated_from: [
      'metatheory/Dregg2/Exec/TurnExecutorFull.lean (FullActionA, requiredFacetA)',
      'metatheory/Dregg2/Exec/FFI.lean (encodeActionW wire codec)',
    ],
    note:
      'AUTOGENERATED by site/tools/gen-ontology-catalog.js from the verified ' +
      'Lean source. Do not edit by hand — regenerate; a drift check (--check) ' +
      'fails if this file is stale.',
    effect_count: effects.length,
    facet_legend: {
      write: 'mutates a cell record / the ledger (Authority.Auth.write)',
      grant: 'moves or mints CAPABILITY, not cell state (Authority.Auth.grant)',
      control: 'a nested exercise re-enters the privileged path (Authority.Auth.control)',
    },
    categories: [
      'value', 'state', 'authority', 'lifecycle', 'escrow',
      'privacy', 'seal', 'bridge', 'queue', 'swiss', 'other',
    ],
    coverage: {
      effects_with_facet: effects.length - missingFacet.length,
      effects_with_wire: effects.length - missingWire.length,
      missing_facet: missingFacet,
      missing_wire: missingWire,
    },
    effects,
  };
  return catalog;
}

// Stable, pretty, trailing-newline JSON for clean diffs.
function render(catalog) {
  return JSON.stringify(catalog, null, 2) + '\n';
}

function main() {
  const check = process.argv.includes('--check');

  // --- Effect ontology (Lean FullActionA) --------------------------------
  const catalog = build();
  const text = render(catalog);
  const cov = catalog.coverage;
  process.stderr.write(
    `gen-ontology-catalog: ${catalog.effect_count} effects · ` +
      `facet ${cov.effects_with_facet}/${catalog.effect_count} · ` +
      `wire ${cov.effects_with_wire}/${catalog.effect_count}\n`
  );
  if (cov.missing_facet.length)
    process.stderr.write(`  missing facet: ${cov.missing_facet.join(', ')}\n`);
  if (cov.missing_wire.length)
    process.stderr.write(`  missing wire:  ${cov.missing_wire.join(', ')}\n`);

  // --- Predicate / cell-program language (Rust cell/src/program.rs) -------
  const pred = buildPredicate();
  const predText = render(pred);
  const pcov = pred.coverage;
  process.stderr.write(
    `  predicate language: ${pred.constraint_count} constraints · ` +
      `${pred.cell_program_kinds.length} program kinds · ` +
      `${pred.transition_guards.length} guards · ` +
      `view ${pcov.constraints_in_view}/${pred.constraint_count} · ` +
      `locally-evaluable ${pcov.locally_evaluable}/${pred.constraint_count}\n`
  );
  if (pcov.missing_from_view.length)
    process.stderr.write(`  ⚠ constraints with NO JSON view: ${pcov.missing_from_view.join(', ')}\n`);
  if (pcov.extra_in_view.length)
    process.stderr.write(`  ⚠ view variants with NO canonical enum: ${pcov.extra_in_view.join(', ')}\n`);

  // --- Node turn-submit schema (node/src/api.rs TurnEffectSpec) -----------
  const submit = buildSubmit(catalog.effects);
  const submitText = render(submit);
  const scov = submit.coverage;
  process.stderr.write(
    `  submit schema: ${submit.effect_count} effect kinds on ${submit.endpoint} · ` +
      `mapped-to-ontology ${scov.submittable_of_ontology}/${submit.effect_count}\n`
  );
  if (scov.missing_ctor.length)
    process.stderr.write(`  ⚠ submit kinds with NO ontology ctor: ${scov.missing_ctor.join(', ')}\n`);

  if (check) {
    let stale = false;
    for (const [file, want] of [[OUT, text], [OUT_PRED, predText], [OUT_SUBMIT, submitText]]) {
      const actual = fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '';
      if (actual !== want) {
        console.error(
          `\nontology drift: ${path.relative(REPO_ROOT, file)} is stale ` +
            `vs source.\nRegenerate: node site/tools/gen-ontology-catalog.js`
        );
        stale = true;
      }
    }
    if (stale) process.exit(1);
    process.stderr.write('  drift check: OK (all catalogs match source)\n');
    return;
  }

  fs.writeFileSync(OUT, text);
  process.stderr.write(`  wrote ${path.relative(REPO_ROOT, OUT)}\n`);
  fs.writeFileSync(OUT_PRED, predText);
  process.stderr.write(`  wrote ${path.relative(REPO_ROOT, OUT_PRED)}\n`);
  fs.writeFileSync(OUT_SUBMIT, submitText);
  process.stderr.write(`  wrote ${path.relative(REPO_ROOT, OUT_SUBMIT)}\n`);
}

main();
