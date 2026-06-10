/**
 * <dregg-factory-composer> — FACTORY AUTHORING v0 (the Studio's cell-program
 * factory workbench).
 *
 * Author a `FactoryDescriptor`: pick perpetual `StateConstraint`s from the
 * generated predicate catalog (with the explainer inline), see the LIVE PROOF
 * BADGES for what the result actually guarantees, and export the descriptor as
 * the exact serde JSON shape `dregg_cell::factory::FactoryDescriptor`
 * deserializes (the same shape the wasm `deploy_factory_descriptor` binding
 * accepts).
 *
 * THE BADGES COME FROM DATA, NEVER HAND-SET:
 *
 *   * Substrate guarantees — `assurance-catalog.generated.json`, parsed from
 *     `metatheory/Dregg2/AssuranceCase.lean`. Every keystone pin listed there
 *     is `#assert_axioms`-certified: Lean's own `collectAxioms` audit proves
 *     it rests ONLY on the kernel triple. The badge text/statement/floor are
 *     quoted from that file.
 *   * Per-constraint enforcement — `predicate-catalog.generated.json`, parsed
 *     from `cell/src/program.rs` (semantics doc-comments, SimpleStateConstraint
 *     membership) and `wasm/src/bindings.rs` (in_view cross-check).
 *   * Operator-discipline limits — the `expressibility_limits` field, quoted
 *     verbatim from `cell/src/blueprint.rs` module docs ("What the program
 *     CANNOT see").
 *   * Worked examples — `factory-samples.generated.json`, produced by RUNNING
 *     the real Rust constructors (blueprint.rs + starbridge-apps/polis); see
 *     `site/tools/gen-factory-samples.sh`.
 *
 * HONESTY RULES (substrate rule: no JS reimplementation of kernel semantics):
 *   * No VK hashing in JS — the exported `factory_vk` is a placeholder the
 *     deploy step replaces/derives (the in-browser runtime's
 *     `deploy_factory_descriptor` keys the registry by it; real toolchains
 *     content-address it). The export says so in `_provenance`.
 *   * Constraints whose serde shape this composer cannot edit are carried
 *     OPAQUE: kept byte-identical in the export, shown as raw JSON.
 *
 * Usage: <dregg-factory-composer></dregg-factory-composer>
 */

const PRED_CATALOG_URL = '/_includes/studio/predicate-catalog.generated.json';
const ASSURANCE_URL = '/_includes/studio/assurance-catalog.generated.json';
const SAMPLES_URL = '/_includes/studio/factory-samples.generated.json';

// Compose-then-inspect round trip: when the composed constraint set IS a
// recognizable polis machine (council / amendment / constitution / worker
// mandate), mount the matching platform inspector on it in factory view.
import { classifyConstraints, constraintsOf } from '../polis-decode.js';

const POLIS_INSPECTOR_TAG = {
  council: 'dregg-council',
  amendment: 'dregg-council',
  constitution: 'dregg-constitution',
  mandate: 'dregg-mandate',
};

function esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

// ---------------------------------------------------------------------------
// Field-element codec (display/entry only — no hashing, no kernel semantics).
// A `Field` is a 32-byte array in the serde shape. Users enter a decimal
// scalar, 0x-hex, or full 64-hex; we encode big-endian into the last bytes,
// mirroring `field_from_u64` (big-endian u64 in the trailing 8 bytes).
// ---------------------------------------------------------------------------

function fieldTo32(raw) {
  const t = String(raw ?? '').trim();
  const out = new Array(32).fill(0);
  if (!t) return out;
  if (/^[0-9a-fA-F]{64}$/.test(t)) {
    for (let i = 0; i < 32; i++) out[i] = parseInt(t.slice(i * 2, i * 2 + 2), 16);
    return out;
  }
  let v;
  try { v = BigInt(t); } catch { return null; }
  if (v < 0n) return null;
  for (let i = 31; i >= 0 && v > 0n; i--) { out[i] = Number(v & 0xffn); v >>= 8n; }
  return v > 0n ? null : out;
}

function field32ToDisplay(arr) {
  if (!Array.isArray(arr) || arr.length !== 32) return JSON.stringify(arr);
  // small scalar (leading 24 bytes zero) → decimal; else 64-hex
  if (arr.slice(0, 24).every((b) => b === 0)) {
    let v = 0n;
    for (const b of arr) v = (v << 8n) | BigInt(b & 0xff);
    return v.toString();
  }
  return arr.map((b) => (b & 0xff).toString(16).padStart(2, '0')).join('');
}

function validField(raw) { return fieldTo32(raw) !== null; }

// ---------------------------------------------------------------------------
// Per-type field renderers / encoders. A catalog constraint kind is COMPOSABLE
// here iff every one of its fields has an entry in TYPE_UI; everything else is
// importable-but-opaque (kept losslessly, shown raw). Driven by the generated
// catalog so new constraints with these shapes appear automatically.
// ---------------------------------------------------------------------------

const TYPE_UI = {
  'u8': {
    placeholder: '0..7 (slot)',
    validate: (v) => /^\d+$/.test(String(v).trim()) && Number(v) < 256 ? null : 'integer 0..255',
    encode: (v) => Number(String(v).trim() || 0),
    decode: (x) => String(x),
  },
  'u32': {
    placeholder: '0',
    validate: (v) => /^\d+$/.test(String(v).trim()) ? null : 'non-negative integer',
    encode: (v) => Number(String(v).trim() || 0),
    decode: (x) => String(x),
  },
  'u64': {
    placeholder: '0',
    validate: (v) => /^\d+$/.test(String(v).trim()) ? null : 'non-negative integer',
    encode: (v) => Number(String(v).trim() || 0),
    decode: (x) => String(x),
  },
  'usize': {
    placeholder: '0',
    validate: (v) => /^\d+$/.test(String(v).trim()) ? null : 'non-negative integer',
    encode: (v) => Number(String(v).trim() || 0),
    decode: (x) => String(x),
  },
  'i64': {
    placeholder: '0 (may be negative)',
    validate: (v) => /^-?\d+$/.test(String(v).trim()) ? null : 'integer',
    encode: (v) => Number(String(v).trim() || 0),
    decode: (x) => String(x),
  },
  'Field': {
    placeholder: 'decimal, 0x…, or 64-hex',
    validate: (v) => validField(v) ? null : 'decimal scalar, 0x… hex, or 64-hex field',
    encode: (v) => fieldTo32(v),
    decode: (x) => field32ToDisplay(x),
  },
  'Hash32': {
    placeholder: '64-hex',
    validate: (v) => /^[0-9a-fA-F]{64}$/.test(String(v).trim()) ? null : '64 hex chars',
    encode: (v) => { const t = String(v).trim(); const o = []; for (let i = 0; i < 32; i++) o.push(parseInt(t.slice(i * 2, i * 2 + 2), 16)); return o; },
    decode: (x) => Array.isArray(x) ? x.map((b) => (b & 0xff).toString(16).padStart(2, '0')).join('') : String(x),
  },
  'Vec<u8>': {
    placeholder: 'comma-separated slots, e.g. 1,2',
    validate: (v) => String(v).split(',').map((s) => s.trim()).filter(Boolean).every((s) => /^\d+$/.test(s) && Number(s) < 256) ? null : 'comma-separated integers 0..255',
    encode: (v) => String(v).split(',').map((s) => s.trim()).filter(Boolean).map(Number),
    decode: (x) => (x || []).join(','),
  },
  'Vec<u64>': {
    placeholder: 'comma-separated integers',
    validate: (v) => String(v).split(',').map((s) => s.trim()).filter(Boolean).every((s) => /^\d+$/.test(s)) ? null : 'comma-separated non-negative integers',
    encode: (v) => String(v).split(',').map((s) => s.trim()).filter(Boolean).map(Number),
    decode: (x) => (x || []).join(','),
  },
  'Option<u64>': {
    placeholder: 'blank = none',
    validate: (v) => String(v).trim() === '' || /^\d+$/.test(String(v).trim()) ? null : 'non-negative integer or blank',
    encode: (v) => String(v).trim() === '' ? null : Number(String(v).trim()),
    decode: (x) => x == null ? '' : String(x),
  },
  // state-machine transition pairs: one `old > new` per line (scalars/hex)
  'Vec<(Field, Field)>': {
    placeholder: 'one "old > new" per line, e.g.\n0 > 1\n1 > 2',
    multiline: true,
    validate: (v) => {
      const lines = String(v).split('\n').map((s) => s.trim()).filter(Boolean);
      if (!lines.length) return 'at least one "old > new" pair';
      for (const ln of lines) {
        const m = ln.split('>');
        if (m.length !== 2 || !validField(m[0]) || !validField(m[1])) return `bad pair: "${ln}" (want "old > new")`;
      }
      return null;
    },
    encode: (v) => String(v).split('\n').map((s) => s.trim()).filter(Boolean)
      .map((ln) => ln.split('>').map((p) => fieldTo32(p.trim()))),
    decode: (x) => (x || []).map(([a, b]) => `${field32ToDisplay(a)} > ${field32ToDisplay(b)}`).join('\n'),
  },
  'Vec<(i64, u8)>': {
    placeholder: 'one "coeff * slot" per line, e.g.\n1 * 0\n-2 * 3',
    multiline: true,
    validate: (v) => {
      const lines = String(v).split('\n').map((s) => s.trim()).filter(Boolean);
      if (!lines.length) return 'at least one "coeff * slot" term';
      for (const ln of lines) {
        const m = ln.split('*');
        if (m.length !== 2 || !/^-?\d+$/.test(m[0].trim()) || !/^\d+$/.test(m[1].trim())) return `bad term: "${ln}" (want "coeff * slot")`;
      }
      return null;
    },
    encode: (v) => String(v).split('\n').map((s) => s.trim()).filter(Boolean)
      .map((ln) => { const [c, i] = ln.split('*'); return [Number(c.trim()), Number(i.trim())]; }),
    decode: (x) => (x || []).map(([c, i]) => `${c} * ${i}`).join('\n'),
  },
};

// ---------------------------------------------------------------------------
// Element
// ---------------------------------------------------------------------------

class DreggFactoryComposer extends HTMLElement {
  connectedCallback() {
    // Composed entries: { kind, fields:{name:rawString}, guard:{slot,value}|null }
    // or { opaque: <raw serde object> } for imported-but-uneditable shapes.
    this._entries = [];
    this._draftKind = null;
    this._draft = {};
    this._draftGuard = null;       // {slot, value} | null while composing
    this._mode = 'Hosted';
    this._budget = '1';
    this._capSelfSig = true;       // the settlement blueprints' one template
    this._loadedExample = null;    // key of the loaded worked example
    this._load();
  }

  async _load() {
    if (!this._pred) {
      this.innerHTML = `<div class="dregg-fc__loading">Loading catalogs…</div>`;
      try {
        const fetchJson = async (url) => {
          const res = await fetch(url, { headers: { Accept: 'application/json' } });
          if (!res.ok) throw new Error(`${url}: status ${res.status}`);
          return res.json();
        };
        [this._pred, this._assurance, this._samples] = await Promise.all([
          fetchJson(PRED_CATALOG_URL), fetchJson(ASSURANCE_URL), fetchJson(SAMPLES_URL),
        ]);
      } catch (err) {
        this.innerHTML =
          `<div class="dregg-inspector dregg-inspector--err">Could not load the generated catalogs ` +
          `(${esc(err && err.message || err)}). Run <code>node site/tools/gen-ontology-catalog.js</code> ` +
          `and <code>site/tools/gen-factory-samples.sh</code>, then rebuild.</div>`;
        return;
      }
      this._byKind = new Map(this._pred.constraints.map((c) => [c.name, c]));
      this._composable = this._pred.constraints.filter(
        (c) => c.fields.length === 0 || c.fields.every((f) => TYPE_UI[f.type])
      );
      // AnyOf is composed via the guard helper, not picked directly.
      this._composable = this._composable.filter((c) => c.name !== 'AnyOf' && c.name !== 'AllOf' && c.name !== 'Not');
      this._draftKind = this._composable[0]?.name || null;
    }
    // dregg://factory/<vk-or-key> deep link (resolver.js → ?factory=…): load
    // the worked example whose key / descriptor hash / factory vk matches.
    if (!this._deepLinked) {
      this._deepLinked = true;
      try {
        const want = (new URLSearchParams(window.location.search).get('factory') || '').trim().toLowerCase();
        if (want) {
          const hex = (bytes) => (bytes || []).map((b) => Number(b).toString(16).padStart(2, '0')).join('');
          const key = Object.keys(this._samples).find((k) => {
            const s = this._samples[k];
            if (!s || !s.descriptor) return false;
            return k.toLowerCase() === want
              || String(s.descriptor_hash || '').toLowerCase().startsWith(want)
              || hex(s.descriptor.factory_vk).startsWith(want);
          });
          if (key) { this._loadExample(key); return; }
        }
      } catch { /* embedded without URL context */ }
    }
    this._render();
  }

  // --- validation ------------------------------------------------------------
  _entryErrors(entry) {
    if (entry.opaque) return {};
    const cat = this._byKind.get(entry.kind);
    const errs = {};
    for (const f of cat.fields) {
      const ui = TYPE_UI[f.type];
      const e = ui && ui.validate(entry.fields[f.name] ?? '');
      if (e) errs[f.name] = e;
    }
    if (entry.guard) {
      if (!/^\d+$/.test(String(entry.guard.slot).trim()) || Number(entry.guard.slot) > 255) errs._guardSlot = 'guard slot: integer 0..255';
      if (!validField(entry.guard.value)) errs._guardValue = 'guard value: scalar/hex';
    }
    return errs;
  }
  _allValid() { return this._entries.every((e) => Object.keys(this._entryErrors(e)).length === 0); }

  // --- serde encoding ----------------------------------------------------------
  /** One entry → the exact `StateConstraint` serde shape. */
  _entryToSerde(entry) {
    if (entry.opaque) return entry.opaque;
    const cat = this._byKind.get(entry.kind);
    // Every composable StateConstraint variant is a struct variant, so the
    // serde shape is externally tagged with a {} field body.
    const body = {};
    for (const f of cat.fields) body[f.name] = TYPE_UI[f.type].encode(entry.fields[f.name] ?? '');
    const bare = { [entry.kind]: body };
    if (!entry.guard) return bare;
    // The blueprint state-guard pattern: AnyOf[ FieldEquals(guardSlot, guardVal), THIS ]
    return {
      AnyOf: {
        variants: [
          { FieldEquals: { index: Number(entry.guard.slot), value: fieldTo32(entry.guard.value) } },
          bare,
        ],
      },
    };
  }

  _descriptor() {
    return {
      _provenance:
        'Authored in the dregg Studio factory composer. factory_vk is a PLACEHOLDER ' +
        '(all-zero): the deploy step keys/derives the real content-addressed VK — this ' +
        'composer does not reimplement kernel hashing in JS. state_constraints are the ' +
        'perpetual cell-program invariants the executor checks on EVERY state-modifying turn.',
      factory_vk: new Array(32).fill(0),
      child_program_vk: null,
      child_vk_strategy: null,
      allowed_cap_templates: this._capSelfSig
        ? [{ target: 'SelfCell', max_permissions: 'Signature', attenuatable: true }]
        : [],
      field_constraints: [],
      state_constraints: this._entries.map((e) => this._entryToSerde(e)),
      default_mode: this._mode,
      creation_budget: String(this._budget).trim() === '' ? null : Number(this._budget),
    };
  }

  // --- import (worked examples / pasted descriptors) ---------------------------
  /** Try to decode one serde StateConstraint into an editable entry; else opaque. */
  _serdeToEntry(sc) {
    const kind = Object.keys(sc)[0];
    const body = sc[kind];
    // The guard pattern: AnyOf with exactly [FieldEquals, X] where X is decodable.
    if (kind === 'AnyOf' && Array.isArray(body?.variants) && body.variants.length === 2) {
      const [g, x] = body.variants;
      if (g.FieldEquals && Object.keys(x).length === 1) {
        const inner = this._serdeToEntry(x);
        if (inner && !inner.opaque && !inner.guard) {
          return { ...inner, guard: { slot: String(g.FieldEquals.index), value: field32ToDisplay(g.FieldEquals.value) } };
        }
      }
    }
    const cat = this._byKind.get(kind);
    if (cat && cat.fields.every((f) => TYPE_UI[f.type])) {
      const fields = {};
      let ok = true;
      for (const f of cat.fields) {
        if (body && f.name in body) fields[f.name] = TYPE_UI[f.type].decode(body[f.name]);
        else if (body == null && cat.fields.length === 0) { /* unit */ }
        else ok = false;
      }
      if (ok) return { kind, fields, guard: null };
    }
    return { opaque: sc };
  }

  _loadExample(key) {
    const ex = this._samples[key];
    if (!ex) return;
    const d = ex.descriptor;
    this._entries = (d.state_constraints || []).map((sc) => this._serdeToEntry(sc));
    this._mode = typeof d.default_mode === 'string' ? d.default_mode : 'Hosted';
    this._budget = d.creation_budget == null ? '' : String(d.creation_budget);
    this._capSelfSig = (d.allowed_cap_templates || []).length > 0;
    this._loadedExample = key;
    this._render();
  }

  // ============================================================================
  // RENDER
  // ============================================================================
  _render() {
    const editable = this._entries.filter((e) => !e.opaque).length;
    const opaque = this._entries.length - editable;
    const head =
      `<div class="dregg-fc__head">` +
        `<div class="dregg-fc__title">Author a factory` +
          `<span class="dregg-fc__count">${this._entries.length} constraint${this._entries.length === 1 ? '' : 's'}` +
          `${opaque ? ` (${opaque} opaque)` : ''}</span></div>` +
        `<div class="dregg-fc__prov">A factory descriptor mints cells whose <strong>perpetual state ` +
          `constraints</strong> the executor checks on <strong>every</strong> state-modifying turn ` +
          `(<code>cell/src/factory.rs</code> · slot caveats). Pick constraints from the generated ` +
          `catalog, watch the proof badges, export the exact serde JSON ` +
          `<code>deploy_factory_descriptor</code> accepts.</div>` +
      `</div>`;

    const examples = this._renderExamples();
    const list = this._renderEntries();
    const add = this._renderAddForm();
    const meta = this._renderMeta();
    const badges = this._renderBadges();
    const exportB = this._renderExport();
    const inspect = this._renderInspect();

    this.innerHTML =
      `<div class="dregg-fc">${head}${examples}` +
      `<div class="dregg-fc__cols">` +
        `<div class="dregg-fc__col">${list}${add}${meta}${exportB}</div>` +
        `<div class="dregg-fc__col dregg-fc__col--badges">${badges}</div>` +
      `</div>${inspect}</div>`;
    this._wire();
  }

  /**
   * Compose-then-inspect: when the composed constraint set IS a recognizable
   * polis machine, mount the matching platform inspector (factory view) on
   * the EXACT descriptor this composer would export — the same machine
   * recognizer the explorer's Polis page uses (polis-decode.js). Edits to the
   * constraint list re-render the inspector live.
   */
  _renderInspect() {
    let cls = null;
    let desc = null;
    try {
      desc = this._descriptor();
      cls = classifyConstraints(constraintsOf(desc));
    } catch { /* not classifiable */ }
    if (!cls || !desc) return '';
    const tag = POLIS_INSPECTOR_TAG[cls.family];
    if (!tag) return '';
    return (
      `<details class="dregg-fc__inspect" open>` +
        `<summary>Inspect what this builds — your constraint set is a recognizable ` +
        `<code>${esc(cls.family)}</code> machine</summary>` +
        `<div class="dregg-fc__inspect-body">` +
          `<${tag} mode="descriptor" data-descriptor="${esc(JSON.stringify(desc))}"></${tag}>` +
        `</div>` +
      `</details>`
    );
  }

  _renderExamples() {
    const keys = ['escrow', 'obligation', 'council', 'constitution'].filter((k) => this._samples[k]);
    const chips = keys.map((k) => {
      const on = this._loadedExample === k;
      return `<button class="dregg-fc__ex${on ? ' is-on' : ''}" data-example="${k}" ` +
        `title="${esc(this._samples[k].source)}">${esc(this._samples[k].title)}</button>`;
    }).join('');
    return (
      `<div class="dregg-fc__examples">` +
        `<span class="dregg-fc__exlabel">worked examples (generated by running the real Rust constructors):</span>${chips}` +
        (this._loadedExample
          ? `<div class="dregg-fc__exnote">Loaded <code>${esc(this._loadedExample)}</code> — ` +
            `${esc(this._samples[this._loadedExample].source)} · descriptor hash ` +
            `<code>${esc(String(this._samples[this._loadedExample].descriptor_hash).slice(0, 16))}…</code>. ` +
            `Decodable constraints became editable rows; the rest are carried opaque (export-lossless).</div>`
          : '') +
      `</div>`
    );
  }

  _badgesFor(entry) {
    if (entry.opaque) {
      return `<span class="dregg-fc__badge is-opaque" title="imported as-is; this composer cannot edit its shape, but the export keeps it byte-identical">opaque (lossless)</span>`;
    }
    const cat = this._byKind.get(entry.kind);
    const b = [];
    b.push(`<span class="dregg-fc__badge is-enforced" title="state_constraints are slot caveats: the executor evaluates them on every state-modifying turn of every cell minted by this factory (cell/src/factory.rs)">executor-enforced · every turn</span>`);
    if (cat.locally_evaluable) {
      b.push(`<span class="dregg-fc__badge is-local" title="this constraint is a pure (old,new)-field comparison; the Studio's predicate explorer mirrors it faithfully in-browser">browser-mirrored</span>`);
    } else {
      b.push(`<span class="dregg-fc__badge is-witness" title="needs the executor (witness / proof / side-table / chain height); not decidable from the slots alone">witness/executor-gated</span>`);
    }
    if (!cat.in_view) {
      b.push(`<span class="dregg-fc__badge is-noview" title="no JSON projection in wasm/src/bindings.rs StateConstraintView yet: live cell inspectors cannot display this constraint">no inspector view yet</span>`);
    }
    if (entry.guard) {
      b.push(`<span class="dregg-fc__badge is-guard" title="wrapped as AnyOf[state-guard, constraint] — the blueprint term-pinning pattern: the constraint binds except in the guard state">state-guarded</span>`);
    }
    return b.join('');
  }

  _renderEntries() {
    if (!this._entries.length) {
      return `<ul class="dregg-fc__entries"><li class="dregg-fc__empty">no constraints yet — every authorized state change would be valid (program <code>None</code>). Add invariants below or load a worked example.</li></ul>`;
    }
    const rows = this._entries.map((entry, i) => {
      const errs = this._entryErrors(entry);
      const bad = Object.keys(errs).length > 0;
      let body;
      if (entry.opaque) {
        body = `<code class="dregg-fc__opaque">${esc(JSON.stringify(entry.opaque).slice(0, 220))}${JSON.stringify(entry.opaque).length > 220 ? '…' : ''}</code>`;
      } else {
        const cat = this._byKind.get(entry.kind);
        const chips = cat.fields.map((f) =>
          `<span class="dregg-fc__chip${errs[f.name] ? ' is-bad' : ''}" title="${esc(errs[f.name] || f.type)}">${esc(f.name)}=<code>${esc(String(entry.fields[f.name] ?? '').split('\n').join(' · '))}</code></span>`).join('');
        const guard = entry.guard
          ? `<span class="dregg-fc__chip is-guardchip${errs._guardSlot || errs._guardValue ? ' is-bad' : ''}">unless slot[${esc(entry.guard.slot)}] = <code>${esc(entry.guard.value)}</code></span>`
          : '';
        body = `<div class="dregg-fc__sem">${esc(cat.semantics)}</div><div class="dregg-fc__chips">${chips}${guard}</div>`;
      }
      return `<li class="dregg-fc__entry${bad ? ' is-bad' : ''}">` +
        `<div class="dregg-fc__entry-head"><code class="dregg-fc__kind">${esc(entry.opaque ? Object.keys(entry.opaque)[0] : entry.kind)}</code>` +
        `<span class="dregg-fc__badges">${this._badgesFor(entry)}</span>` +
        `<button class="dregg-fc__del" data-del="${i}" title="remove">✕</button></div>` +
        body +
        (bad ? `<div class="dregg-fc__err">${esc(Object.values(errs).join(' · '))}</div>` : '') +
      `</li>`;
    }).join('');
    return `<ul class="dregg-fc__entries">${rows}</ul>`;
  }

  _renderAddForm() {
    const kind = this._draftKind;
    const cat = this._byKind.get(kind);
    const groups = { 'browser-mirrored (pure field comparison)': [], 'witness / executor-gated': [] };
    for (const c of this._composable) {
      (c.locally_evaluable ? groups['browser-mirrored (pure field comparison)'] : groups['witness / executor-gated']).push(c);
    }
    const opts = Object.entries(groups).map(([label, cs]) =>
      `<optgroup label="${esc(label)}">` +
        cs.map((c) => `<option value="${esc(c.name)}"${c.name === kind ? ' selected' : ''}>${esc(c.name)}</option>`).join('') +
      `</optgroup>`).join('');

    const inputs = (cat ? cat.fields : []).map((f) => {
      const ui = TYPE_UI[f.type];
      const val = this._draft[f.name] ?? '';
      const err = ui.validate(val);
      const touched = f.name in this._draft;
      const input = ui.multiline
        ? `<textarea data-field="${esc(f.name)}" rows="3" placeholder="${esc(ui.placeholder)}"${touched && err ? ' class="is-bad"' : ''}>${esc(val)}</textarea>`
        : `<input data-field="${esc(f.name)}" value="${esc(val)}" placeholder="${esc(ui.placeholder)}"${touched && err ? ' class="is-bad"' : ''}>`;
      return `<div class="dregg-fc__finp"><label>${esc(f.name)} <span class="dregg-fc__dim">${esc(f.type)}</span></label>${input}` +
        (touched && err ? `<span class="dregg-fc__finp-err">${esc(err)}</span>` : '') + `</div>`;
    }).join('');

    const guardable = cat && cat.simple;
    const guardRow = guardable
      ? `<label class="dregg-fc__guard"><input type="checkbox" data-guard-toggle${this._draftGuard ? ' checked' : ''}> ` +
        `state-guard it <span class="dregg-fc__dim">(AnyOf[slot = value, …] — binds except in the guard state; the blueprint term-pinning pattern)</span></label>` +
        (this._draftGuard
          ? `<div class="dregg-fc__guard-fields">` +
            `<div class="dregg-fc__finp"><label>guard slot</label><input data-guard="slot" value="${esc(this._draftGuard.slot)}" placeholder="0"></div>` +
            `<div class="dregg-fc__finp"><label>guard value</label><input data-guard="value" value="${esc(this._draftGuard.value)}" placeholder="0 (e.g. UNINIT)"></div>` +
            `</div>`
          : '')
      : (cat ? `<div class="dregg-fc__dim" style="font-size:0.72rem">not state-guardable (only SimpleStateConstraint kinds nest inside AnyOf — from the canonical enum)</div>` : '');

    return (
      `<div class="dregg-fc__add">` +
        `<div class="dregg-fc__add-pick">` +
          `<select class="dregg-fc__add-kind">${opts}</select>` +
          (cat ? `<span class="dregg-fc__add-sem">${esc(cat.semantics)}</span>` : '') +
        `</div>` +
        `<div class="dregg-fc__add-fields">${inputs}</div>` +
        guardRow +
        `<button class="dregg-fc__add-btn">+ add constraint</button>` +
      `</div>`
    );
  }

  _renderMeta() {
    return (
      `<div class="dregg-fc__meta">` +
        `<div class="dregg-fc__finp"><label>default mode <span class="dregg-fc__dim">(Hosted = federation stores state; Sovereign = commitment only)</span></label>` +
          `<select data-meta="mode"><option${this._mode === 'Hosted' ? ' selected' : ''}>Hosted</option><option${this._mode === 'Sovereign' ? ' selected' : ''}>Sovereign</option></select></div>` +
        `<div class="dregg-fc__finp"><label>creation budget <span class="dregg-fc__dim">(cells/epoch; blank = unlimited)</span></label>` +
          `<input data-meta="budget" value="${esc(this._budget)}" placeholder="1"></div>` +
        `<label class="dregg-fc__guard"><input type="checkbox" data-meta-capsig${this._capSelfSig ? ' checked' : ''}> ` +
          `self-cell signature cap template <span class="dregg-fc__dim">(the settlement blueprints' one template: the minted cell can be acted on with Signature permission, attenuatable)</span></label>` +
      `</div>`
    );
  }

  _renderBadges() {
    const a = this._assurance;
    const triple = (a.kernel_axiom_triple || []).join(', ');
    const editable = this._entries.filter((e) => !e.opaque);
    const localN = editable.filter((e) => this._byKind.get(e.kind)?.locally_evaluable).length;
    const witnessN = editable.length - localN;
    const opaqueN = this._entries.length - editable.length;

    const subRows = a.guarantees.map((g) => {
      const pins = g.pins.length;
      const tip = `${g.statement || ''}\n\nFloor: ${g.floor || '(none stated)'}\n\nApex: ${g.apex_theorem || '—'} · ${pins} #assert_axioms pins (each certified by Lean collectAxioms = {${triple}})`;
      return `<div class="dregg-fc__g" title="${esc(tip)}">` +
        `<span class="dregg-fc__g-letter">${esc(g.letter)}</span>` +
        `<span class="dregg-fc__g-name">${esc(g.title)}</span>` +
        `<span class="dregg-fc__g-pins">${pins} pins</span>` +
        `<div class="dregg-fc__g-stmt">${esc(g.statement)}</div>` +
        (g.floor ? `<div class="dregg-fc__g-floor">floor: ${esc(g.floor)}</div>` : '') +
      `</div>`;
    }).join('');

    const floorRows = (a.assumption_floor || []).map((f) =>
      `<li title="${esc(f.detail)}">${esc(f.name)}</li>`).join('');

    const limits = (this._pred.expressibility_limits || []).map((l) =>
      `<li>${esc(l)}</li>`).join('');

    return (
      `<div class="dregg-fc__badgepanel">` +
        `<h4 class="dregg-fc__h">Proof badges <span class="dregg-fc__dim">(live, from generated data)</span></h4>` +

        `<div class="dregg-fc__sect">` +
          `<div class="dregg-fc__sect-title">Substrate guarantees <span class="dregg-fc__dim">— carried by the kernel for every cell this factory mints</span></div>` +
          subRows +
          `<div class="dregg-fc__note">Source: <code>Dregg2/AssuranceCase.lean</code> via ` +
          `<code>assurance-catalog.generated.json</code>. Every pin is <code>#assert_axioms</code>-certified: ` +
          `Lean's <code>collectAxioms</code> audit proves it rests only on <code>{${esc(triple)}}</code> ` +
          `(no <code>sorry</code>). Hover a guarantee for its statement, floor, and apex theorem.</div>` +
        `</div>` +

        `<div class="dregg-fc__sect">` +
          `<div class="dregg-fc__sect-title">Assumption floor <span class="dregg-fc__dim">— the only out-of-kernel carriers (hover for detail)</span></div>` +
          `<ul class="dregg-fc__floor">${floorRows}</ul>` +
        `</div>` +

        `<div class="dregg-fc__sect">` +
          `<div class="dregg-fc__sect-title">What your constraints add</div>` +
          `<div class="dregg-fc__addsum">` +
            `<div><strong>${this._entries.length}</strong> perpetual invariant${this._entries.length === 1 ? '' : 's'} — evaluated by the executor on <strong>every</strong> state-modifying turn of every minted cell</div>` +
            `<div><strong>${localN}</strong> browser-mirrored (pure field comparisons — the Studio can replay them) · ` +
            `<strong>${witnessN}</strong> witness/executor-gated` +
            (opaqueN ? ` · <strong>${opaqueN}</strong> opaque (imported, export-lossless)` : '') + `</div>` +
          `</div>` +
        `</div>` +

        `<div class="dregg-fc__sect">` +
          `<div class="dregg-fc__sect-title">Operator / SDK discipline <span class="dregg-fc__dim">— NOT program-enforced (source-stated limits)</span></div>` +
          `<ul class="dregg-fc__limits">${limits}</ul>` +
          `<div class="dregg-fc__note">Quoted from <code>cell/src/blueprint.rs</code> ("What the program CANNOT see") ` +
          `via the generated predicate catalog — honesty about where enforcement ends.</div>` +
        `</div>` +
      `</div>`
    );
  }

  _renderExport() {
    const valid = this._allValid();
    const json = JSON.stringify(this._descriptor(), null, 2);
    return (
      `<div class="dregg-fc__export">` +
        `<div class="dregg-fc__advance">` +
          `<span class="dregg-fc__valid ${valid ? 'is-ok' : 'is-fail'}">${valid ? '✓ descriptor valid' : '✗ fix the highlighted constraints'}</span>` +
          `<button class="dregg-fc__copy"${valid ? '' : ' disabled'}>Copy JSON</button>` +
          `<button class="dregg-fc__download"${valid ? '' : ' disabled'}>Download .json</button>` +
        `</div>` +
        `<details class="dregg-fc__preview"><summary>FactoryDescriptor JSON (the exact serde shape <code>deploy_factory_descriptor</code> accepts)</summary>` +
          `<pre class="dregg-fc__json">${esc(json)}</pre></details>` +
      `</div>`
    );
  }

  // ============================================================================
  // WIRING
  // ============================================================================
  _wire() {
    this.querySelectorAll('[data-example]').forEach((b) =>
      b.addEventListener('click', () => this._loadExample(b.getAttribute('data-example'))));

    const kindSel = this.querySelector('.dregg-fc__add-kind');
    if (kindSel) kindSel.addEventListener('change', () => {
      this._draftKind = kindSel.value; this._draft = {}; this._draftGuard = null; this._render();
    });

    this.querySelectorAll('.dregg-fc__add-fields [data-field]').forEach((inp) =>
      inp.addEventListener('input', () => {
        this._draft[inp.getAttribute('data-field')] = inp.value;
        const cat = this._byKind.get(this._draftKind);
        const f = cat.fields.find((x) => x.name === inp.getAttribute('data-field'));
        const err = f ? TYPE_UI[f.type].validate(inp.value) : null;
        inp.classList.toggle('is-bad', !!err);
        const errEl = inp.parentElement.querySelector('.dregg-fc__finp-err');
        if (err && !errEl) { const s = document.createElement('span'); s.className = 'dregg-fc__finp-err'; s.textContent = err; inp.after(s); }
        else if (err && errEl) errEl.textContent = err;
        else if (!err && errEl) errEl.remove();
      }));

    const guardToggle = this.querySelector('[data-guard-toggle]');
    if (guardToggle) guardToggle.addEventListener('change', () => {
      this._draftGuard = guardToggle.checked ? { slot: '0', value: '0' } : null;
      this._render();
    });
    this.querySelectorAll('[data-guard]').forEach((inp) =>
      inp.addEventListener('input', () => {
        if (this._draftGuard) this._draftGuard[inp.getAttribute('data-guard')] = inp.value;
      }));

    const addBtn = this.querySelector('.dregg-fc__add-btn');
    if (addBtn) addBtn.addEventListener('click', () => {
      const cat = this._byKind.get(this._draftKind);
      if (!cat) return;
      const fields = {};
      for (const f of cat.fields) fields[f.name] = this._draft[f.name] ?? '';
      this._entries.push({ kind: this._draftKind, fields, guard: this._draftGuard ? { ...this._draftGuard } : null });
      this._draft = {}; this._draftGuard = null; this._loadedExample = null;
      this._render();
    });

    this.querySelectorAll('.dregg-fc__del').forEach((b) =>
      b.addEventListener('click', () => { this._entries.splice(+b.getAttribute('data-del'), 1); this._render(); }));

    this.querySelectorAll('[data-meta]').forEach((inp) =>
      inp.addEventListener('change', () => {
        const k = inp.getAttribute('data-meta');
        if (k === 'mode') this._mode = inp.value;
        else if (k === 'budget') this._budget = inp.value;
        this._render();
      }));
    const capSig = this.querySelector('[data-meta-capsig]');
    if (capSig) capSig.addEventListener('change', () => { this._capSelfSig = capSig.checked; this._render(); });

    const copy = this.querySelector('.dregg-fc__copy');
    if (copy) copy.addEventListener('click', async () => {
      try {
        await navigator.clipboard.writeText(JSON.stringify(this._descriptor(), null, 2));
        copy.textContent = 'Copied ✓'; setTimeout(() => { copy.textContent = 'Copy JSON'; }, 1500);
      } catch { copy.textContent = 'copy failed'; }
    });
    const dl = this.querySelector('.dregg-fc__download');
    if (dl) dl.addEventListener('click', () => {
      const blob = new Blob([JSON.stringify(this._descriptor(), null, 2)], { type: 'application/json' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'factory-descriptor.json';
      a.click();
      URL.revokeObjectURL(a.href);
    });
  }
}

if (!customElements.get('dregg-factory-composer')) {
  customElements.define('dregg-factory-composer', DreggFactoryComposer);
}

// --- styles (site palette only) ----------------------------------------------
(function injectStyles() {
  if (document.getElementById('dregg-factory-composer-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-factory-composer-styles';
  s.textContent = `
.dregg-fc { font-family: var(--font-mono, ui-monospace, monospace); }
.dregg-fc__loading { color: var(--fg-dim); padding: 10px; }
.dregg-fc__title { display:flex; align-items:baseline; gap:10px; font-size:1.1rem; color:var(--fg); font-weight:600; }
.dregg-fc__count { font-size:0.8rem; color:var(--fg-dim); font-weight:normal; }
.dregg-fc__prov { font-size:0.78rem; color:var(--fg-dim); margin-top:4px; line-height:1.5; }
.dregg-fc__prov code, .dregg-fc__note code { color:var(--fg); }
.dregg-fc__dim { color:var(--fg-dim); font-size:0.92em; }
.dregg-fc__examples { display:flex; align-items:center; flex-wrap:wrap; gap:8px; margin:12px 0; padding:8px 10px; border:1px dashed var(--line); border-radius:6px; }
.dregg-fc__inspect { border:1px solid var(--line); border-radius:6px; margin-top:12px; }
.dregg-fc__inspect > summary { cursor:pointer; padding:8px 10px; color:var(--fg-dim); font-size:0.84rem; user-select:none; }
.dregg-fc__inspect-body { border-top:1px solid var(--line); padding:10px; background:var(--bg, #0d1117); }
.dregg-fc__exlabel { font-size:0.72rem; color:var(--fg-dim); }
.dregg-fc__ex { cursor:pointer; font:inherit; font-size:0.76rem; padding:4px 10px; border:1px solid var(--line); border-radius:12px; background:var(--bg-raised); color:var(--fg); }
.dregg-fc__ex:hover { border-color:var(--accent,#5b8a5a); }
.dregg-fc__ex.is-on { border-color:var(--accent,#5b8a5a); outline:1px solid var(--accent,#5b8a5a); }
.dregg-fc__exnote { flex-basis:100%; font-size:0.72rem; color:var(--fg-dim); line-height:1.5; }
.dregg-fc__exnote code { color:var(--fg); }
.dregg-fc__cols { display:grid; grid-template-columns: minmax(0,3fr) minmax(0,2fr); gap:14px; align-items:start; }
@media (max-width: 900px) { .dregg-fc__cols { grid-template-columns: 1fr; } }
.dregg-fc__entries { list-style:none; padding:0; margin:0 0 10px; display:flex; flex-direction:column; gap:6px; }
.dregg-fc__entry { border:1px solid var(--line); border-left:3px solid var(--accent,#5b8a5a); border-radius:5px; background:var(--bg-raised); padding:8px 10px; }
.dregg-fc__entry.is-bad { border-left-color:#d4685c; }
.dregg-fc__entry-head { display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
.dregg-fc__kind { font-size:0.86rem; color:var(--fg); font-weight:600; }
.dregg-fc__badges { display:flex; gap:5px; flex-wrap:wrap; }
.dregg-fc__badge { font-size:0.64rem; text-transform:uppercase; letter-spacing:0.03em; padding:1px 7px; border-radius:9px; border:1px solid var(--line); color:var(--fg-dim); cursor:help; }
.dregg-fc__badge.is-enforced { border-color:#62c47a; color:#8ee6a2; }
.dregg-fc__badge.is-local { border-color:#64a8c8; color:#8fcde6; }
.dregg-fc__badge.is-witness { border-color:#c9a84c; color:#f2d06b; }
.dregg-fc__badge.is-noview { border-color:#d4685c; color:#f18b7d; }
.dregg-fc__badge.is-guard { border-color:#9060c0; color:#bf9aea; }
.dregg-fc__badge.is-opaque { border-color:var(--fg-dim); color:var(--fg-dim); }
.dregg-fc__del { margin-left:auto; background:none; border:0; color:var(--fg-dim); cursor:pointer; }
.dregg-fc__del:hover { color:#e08878; }
.dregg-fc__sem { font-size:0.74rem; color:var(--fg-dim); margin-top:4px; line-height:1.45; }
.dregg-fc__chips { display:flex; flex-wrap:wrap; gap:6px; margin-top:5px; }
.dregg-fc__chip { font-size:0.76rem; padding:1px 7px; background:var(--bg); border:1px solid var(--line); border-radius:3px; color:var(--fg-dim); }
.dregg-fc__chip code { color:var(--fg); }
.dregg-fc__chip.is-bad { border-color:#d4685c; }
.dregg-fc__chip.is-guardchip { border-style:dashed; }
.dregg-fc__opaque { display:block; font-size:0.7rem; color:var(--fg-dim); margin-top:5px; word-break:break-all; }
.dregg-fc__err { font-size:0.72rem; color:#e08878; margin-top:5px; }
.dregg-fc__empty { color:var(--fg-dim); font-style:italic; padding:8px 10px; border:1px dashed var(--line); border-radius:5px; }
.dregg-fc__empty code { color:var(--fg); }
.dregg-fc__add { border:1px solid var(--line); border-radius:6px; background:var(--bg); padding:10px; margin-bottom:10px; }
.dregg-fc__add-pick { display:flex; align-items:center; gap:10px; flex-wrap:wrap; margin-bottom:8px; }
.dregg-fc__add-kind { padding:6px 8px; font:inherit; font-size:0.8rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-fc__add-sem { font-size:0.76rem; color:var(--fg-dim); flex:1; min-width:160px; line-height:1.4; }
.dregg-fc__add-fields { display:flex; flex-wrap:wrap; gap:10px; margin-bottom:8px; }
.dregg-fc__finp { display:flex; flex-direction:column; gap:3px; }
.dregg-fc__finp label { font-size:0.72rem; color:var(--fg-dim); }
.dregg-fc__finp input, .dregg-fc__finp textarea, .dregg-fc__finp select { padding:6px 8px; font:inherit; font-size:0.78rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; min-width:150px; }
.dregg-fc__finp input:focus, .dregg-fc__finp textarea:focus { outline:none; border-color:var(--accent,#5b8a5a); }
.dregg-fc__finp input.is-bad, .dregg-fc__finp textarea.is-bad { border-color:#d4685c; }
.dregg-fc__finp-err { font-size:0.7rem; color:#e08878; }
.dregg-fc__guard { display:flex; align-items:center; gap:7px; font-size:0.76rem; color:var(--fg); margin:6px 0; flex-wrap:wrap; }
.dregg-fc__guard-fields { display:flex; gap:10px; margin:4px 0 8px 22px; }
.dregg-fc__add-btn { cursor:pointer; padding:6px 14px; font:inherit; font-size:0.8rem; background:color-mix(in srgb,var(--accent,#5b8a5a) 18%,var(--bg-raised)); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-fc__add-btn:hover { border-color:var(--accent,#5b8a5a); }
.dregg-fc__meta { display:flex; flex-wrap:wrap; gap:12px; align-items:flex-end; border:1px solid var(--line); border-radius:6px; background:var(--bg-raised); padding:10px; margin-bottom:10px; }
.dregg-fc__export { margin-top:4px; }
.dregg-fc__advance { display:flex; align-items:center; gap:12px; flex-wrap:wrap; }
.dregg-fc__valid { font-size:0.8rem; font-weight:600; }
.dregg-fc__valid.is-ok { color:var(--accent-bright,#7db87b); }
.dregg-fc__valid.is-fail { color:#e08878; }
.dregg-fc__copy, .dregg-fc__download { cursor:pointer; padding:6px 14px; font:inherit; font-size:0.8rem; border:1px solid var(--line); border-radius:5px; background:color-mix(in srgb,var(--accent,#5b8a5a) 22%,var(--bg-raised)); color:var(--fg); }
.dregg-fc__copy:hover:not(:disabled), .dregg-fc__download:hover:not(:disabled) { border-color:var(--accent,#5b8a5a); }
.dregg-fc__copy:disabled, .dregg-fc__download:disabled { opacity:0.45; cursor:not-allowed; }
.dregg-fc__preview { margin:10px 0; font-size:0.78rem; }
.dregg-fc__preview summary { cursor:pointer; color:var(--fg-dim); }
.dregg-fc__preview summary code { color:var(--fg); }
.dregg-fc__json { background:var(--bg-raised); border:1px solid var(--line); border-radius:5px; padding:10px; font-size:0.72rem; color:var(--fg); overflow:auto; max-height:380px; white-space:pre; margin:6px 0 0; }
.dregg-fc__badgepanel { border:1px solid var(--line); border-radius:8px; background:var(--bg); padding:12px; position:sticky; top:12px; }
.dregg-fc__h { margin:0 0 8px; font-size:0.9rem; color:var(--fg); }
.dregg-fc__sect { margin-top:12px; }
.dregg-fc__sect-title { font-size:0.74rem; text-transform:uppercase; letter-spacing:0.05em; color:var(--fg); margin-bottom:6px; }
.dregg-fc__g { display:grid; grid-template-columns:24px 1fr auto; gap:2px 8px; border:1px solid var(--line); border-radius:5px; background:var(--bg-raised); padding:6px 8px; margin-bottom:5px; cursor:help; }
.dregg-fc__g-letter { display:flex; align-items:center; justify-content:center; width:22px; height:22px; border-radius:50%; background:color-mix(in srgb,var(--accent,#5b8a5a) 30%,var(--bg)); color:var(--fg); font-size:0.74rem; font-weight:700; }
.dregg-fc__g-name { font-size:0.78rem; color:var(--fg); font-weight:600; align-self:center; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.dregg-fc__g-pins { font-size:0.66rem; color:#8ee6a2; border:1px solid #62c47a; border-radius:9px; padding:1px 7px; align-self:center; white-space:nowrap; }
.dregg-fc__g-stmt { grid-column:2 / -1; font-size:0.72rem; color:var(--fg-dim); line-height:1.4; }
.dregg-fc__g-floor { grid-column:2 / -1; font-size:0.66rem; color:#d4b060; line-height:1.4; }
.dregg-fc__floor { list-style:none; padding:0; margin:0; display:flex; flex-wrap:wrap; gap:5px; }
.dregg-fc__floor li { font-size:0.7rem; border:1px solid var(--line); border-radius:9px; padding:2px 8px; color:var(--fg-dim); cursor:help; }
.dregg-fc__addsum { font-size:0.76rem; color:var(--fg-dim); line-height:1.6; }
.dregg-fc__addsum strong { color:var(--fg); }
.dregg-fc__limits { padding-left:16px; margin:0; display:grid; gap:5px; font-size:0.72rem; color:var(--fg-dim); line-height:1.45; }
.dregg-fc__note { font-size:0.68rem; color:var(--fg-dim); margin-top:7px; line-height:1.45; }
`;
  document.head.appendChild(s);
})();
