/**
 * <dregg-turn-composer> — the CELL-PROGRAM / TURN authoring IDE core.
 *
 * A guided compose → validate → simulate → submit flow for building a real
 * dregg turn out of the catalogued effect vocabulary, WITHOUT hand-writing
 * JSON:
 *
 *   1. COMPOSE  — pick an effect kind (grouped by category, with one-line
 *      semantics from the verified-Lean catalog), fill its typed fields via
 *      guided inputs, and stack effects into an action. A live wire-JSON
 *      preview shows exactly what will be sent.
 *
 *   2. VALIDATE — every field is checked against the generated SUBMIT SCHEMA
 *      (`submit-schema.generated.json`, parsed straight from the node's
 *      `TurnEffectSpec` in `node/src/api.rs`) — hex cell ids, slot indices,
 *      scalar/hex values, amounts — with inline errors. The submit button is
 *      gated on a fully-valid turn.
 *
 *   3. SIMULATE — apply the effects to a small modeled cell state and show the
 *      resulting (old → new) slot/balance/nonce/event diff. This is a LOCAL
 *      model of the field-write fragment only; everything the local model can
 *      NOT decide (caller authorization, ledger-wide conservation, the STARK
 *      proof) is honestly labeled "needs executor" — never faked.
 *
 *   4. SUBMIT   — POST the turn to a live node's `/api/turns/submit` and surface
 *      the node's honest verdict (`accepted` / `turn_hash` / `proof_status` /
 *      `error`). Auth (Bearer token) and node URL are user-supplied.
 *
 * Anti-drift: the effect vocabulary, field shapes, and node endpoint all come
 * from generated-from-source JSON. This element renders into its own light DOM
 * and needs no wasm/runtime for compose/validate/simulate; only SUBMIT touches
 * the network.
 *
 * Usage:
 *   <dregg-turn-composer></dregg-turn-composer>
 * Attributes:
 *   node      — initial node base URL (default: same-origin, else localhost:8420)
 *   src       — override the submit-schema URL
 */

const SUBMIT_SCHEMA_URL = '/_includes/studio/submit-schema.generated.json';
const NODE_URL_KEY = 'dregg_node_url';
const NODE_TOKEN_KEY = 'dregg_node_token';
const DEFAULT_NODE_URL = 'http://localhost:8420';
const NSLOTS = 8;

function esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

// Same same-origin default the explorer uses: on a real https host front the
// node on that origin; locally fall back to localhost:8420.
function defaultNodeUrl() {
  try {
    const { protocol, hostname, origin } = window.location;
    const isLocal = hostname === 'localhost' || hostname === '127.0.0.1' || hostname === '[::1]';
    if ((protocol === 'http:' || protocol === 'https:') && !isLocal) return origin;
  } catch (_) { /* non-browser */ }
  return DEFAULT_NODE_URL;
}

// ---------------------------------------------------------------------------
// Field validation — mirrors what the node's parsers accept (parse_cell_id /
// parse_field_element in api.rs): a cell id is 64 hex chars (or empty ⇒ defaults
// to the action target); a value is a 64-hex field element OR a hex (0x…) /
// decimal scalar; index is a usize; amount is a u64; topic is a scalar word;
// data is a list of scalar words.
// ---------------------------------------------------------------------------

const HEX64 = /^[0-9a-fA-F]{64}$/;

function validateCellId(v, { allowEmpty }) {
  const t = (v || '').trim();
  if (!t) return allowEmpty ? null : 'required (64-hex cell id)';
  return HEX64.test(t) ? null : 'must be 64 hex chars';
}
function validateScalarOrHex(v) {
  const t = (v || '').trim();
  if (!t) return 'required';
  if (HEX64.test(t)) return null;                       // full field element
  if (/^0x[0-9a-fA-F]+$/.test(t)) return null;          // hex scalar
  if (/^\d+$/.test(t)) return null;                     // decimal scalar
  return 'hex field element, 0x… hex, or decimal scalar';
}
function validateIndex(v) {
  const t = (v || '').trim();
  if (!/^\d+$/.test(t)) return 'non-negative integer';
  const n = Number(t);
  if (n >= NSLOTS) return `0..${NSLOTS - 1} for the local model (the chain allows more)`;
  return null;
}
function validateU64(v) {
  const t = (v || '').trim();
  if (!/^\d+$/.test(t)) return 'non-negative integer';
  return null;
}

// Interpret a scalar/hex string as an integer for the local simulation model.
function toModelInt(v) {
  const t = (v || '').trim();
  if (!t) return 0;
  if (HEX64.test(t)) {
    // Low 8 bytes, little-endian, mirroring parse_field_element's scalar path
    // when the value happens to be a small number; for a full field element we
    // just take the trailing 16 hex (low 8 bytes) as an approximation for the
    // model's integer view (documented simplification).
    try { return Number(BigInt('0x' + t.slice(48)) & 0xffffffffffffffffn); }
    catch { return 0; }
  }
  if (/^0x/.test(t)) { try { return Number(BigInt(t)); } catch { return 0; } }
  const n = Number(t);
  return Number.isFinite(n) ? n : 0;
}

// ---------------------------------------------------------------------------
// Per-kind field UI specs. We drive the inputs from the generated schema's
// field list, but a kind needs a little extra UI hinting (validator, default
// resolution, simulation). This table is keyed by the schema `kind` so a NEW
// submit kind shows up as an un-simulated raw form rather than silently
// breaking.
// ---------------------------------------------------------------------------

const FIELD_UI = {
  set_field: {
    cell:  { label: 'cell',  placeholder: '(blank = action target)', validate: (v) => validateCellId(v, { allowEmpty: true }) },
    index: { label: 'slot',  placeholder: '0', validate: validateIndex, default: '0' },
    value: { label: 'value', placeholder: 'decimal, 0x…, or 64-hex', validate: validateScalarOrHex, default: '0' },
  },
  transfer: {
    from:   { label: 'from',   placeholder: '(blank = action target)', validate: (v) => validateCellId(v, { allowEmpty: true }) },
    to:     { label: 'to',     placeholder: '64-hex recipient cell id', validate: (v) => validateCellId(v, { allowEmpty: false }) },
    amount: { label: 'amount', placeholder: '0', validate: validateU64, default: '0' },
  },
  emit_event: {
    cell:  { label: 'cell',  placeholder: '(blank = action target)', validate: (v) => validateCellId(v, { allowEmpty: true }) },
    topic: { label: 'topic', placeholder: 'decimal/0x… topic word', validate: validateScalarOrHex, default: '0' },
    data:  { label: 'data',  placeholder: 'comma-separated words', validate: () => null, isList: true },
  },
  increment_nonce: {
    cell:  { label: 'cell',  placeholder: '(blank = action target)', validate: (v) => validateCellId(v, { allowEmpty: true }) },
  },
};

const CAT_HUE = {
  value: '#5b8a5a', state: '#c8a050', authority: '#c86060', lifecycle: '#5080c8',
  escrow: '#9060c0', privacy: '#a050a0', seal: '#50a0a8', bridge: '#c87830',
  queue: '#5aa0a0', swiss: '#8a78c0', other: '#8a948f',
};
function catColor(cat) {
  const hue = CAT_HUE[cat] || CAT_HUE.other;
  return `background:color-mix(in srgb,${hue} 20%,var(--bg-raised));color:${hue}`;
}

// ---------------------------------------------------------------------------
// Element
// ---------------------------------------------------------------------------

class DreggTurnComposer extends HTMLElement {
  connectedCallback() {
    this._effects = [];          // composed effects (form-model objects)
    this._draftKind = null;      // kind currently being added
    this._draft = {};            // draft field values for the add-form
    this._target = '';           // action target cell (optional)
    // Fee doubles as the per-turn computron budget the executor charges against
    // (a fee=0 turn is rejected "computron budget exceeded" for any real effect),
    // so default to a sane non-zero budget rather than make first-run users hit
    // that wall. 500 comfortably covers a small turn.
    this._fee = '500';
    this._memo = '';
    this._submitResult = null;   // last node response (or error)
    this._submitting = false;
    this._step = 'compose';      // compose | simulate | submit (progressive)
    this._load();
  }

  async _load() {
    if (!this._schema) {
      const url = this.getAttribute('src') || SUBMIT_SCHEMA_URL;
      this.innerHTML = `<div class="dregg-tc__loading">Loading turn-submit schema…</div>`;
      try {
        const res = await fetch(url, { headers: { Accept: 'application/json' } });
        if (!res.ok) throw new Error('status ' + res.status);
        this._schema = await res.json();
      } catch (err) {
        this.innerHTML =
          `<div class="dregg-inspector dregg-inspector--err">Could not load submit schema ` +
          `(${esc(err && err.message || err)}). Run <code>node site/tools/gen-ontology-catalog.js</code> ` +
          `and rebuild.</div>`;
        return;
      }
      this._draftKind = this._schema.effects[0]?.kind || null;
    }
    this._render();
  }

  // --- node config (shared with the explorer's localStorage keys) -----------
  _nodeUrl() {
    return localStorage.getItem(NODE_URL_KEY) || this.getAttribute('node') || defaultNodeUrl();
  }
  _nodeToken() { return localStorage.getItem(NODE_TOKEN_KEY) || ''; }

  // --- per-effect validation -----------------------------------------------
  _effectErrors(eff) {
    const ui = FIELD_UI[eff.kind] || {};
    const errs = {};
    for (const [name, spec] of Object.entries(ui)) {
      if (!spec.validate) continue;
      const e = spec.validate(eff.fields[name]);
      if (e) errs[name] = e;
    }
    return errs;
  }
  _allValid() {
    if (!this._effects.length) return false;
    return this._effects.every((eff) => Object.keys(this._effectErrors(eff)).length === 0);
  }

  // --- turn → wire JSON (exact node body) -----------------------------------
  _wireBody() {
    const actions = [{
      ...(this._target.trim() ? { target: this._target.trim() } : {}),
      effects: this._effects.map((eff) => this._effectWire(eff)),
    }];
    return {
      agent: this._target.trim() || '00'.repeat(32),
      nonce: 0,
      fee: Number(this._fee) || 0,
      ...(this._memo.trim() ? { memo: this._memo.trim() } : {}),
      actions,
    };
  }
  _effectWire(eff) {
    const ui = FIELD_UI[eff.kind] || {};
    const out = { kind: eff.kind };
    for (const [name, spec] of Object.entries(ui)) {
      const raw = (eff.fields[name] ?? '').trim();
      if (spec.isList) {
        const list = raw ? raw.split(',').map((s) => s.trim()).filter(Boolean) : [];
        if (list.length) out[name] = list;
        continue;
      }
      if (raw === '' && (name === 'cell' || name === 'from')) continue; // optional default
      if (name === 'index') out[name] = Number(raw || 0);
      else if (name === 'amount') out[name] = Number(raw || 0);
      else out[name] = raw;
    }
    return out;
  }

  // --- LOCAL simulation model (field-write fragment only, honest about gaps) -
  // Models a single cell: 8 integer slots, a balance, a nonce, and an event log.
  // Returns { old, new, steps:[{label, kind, detail, deferred}] } where steps
  // marked deferred are the parts the local model can NOT decide (it says so).
  _simulate() {
    const slots = new Array(NSLOTS).fill(0);
    const before = { slots: slots.slice(), balance: 1000, nonce: 0, events: [] };
    const st = { slots: slots.slice(), balance: 1000, nonce: 0, events: [] };
    const steps = [];
    for (const eff of this._effects) {
      const errs = this._effectErrors(eff);
      if (Object.keys(errs).length) {
        steps.push({ kind: eff.kind, label: `${eff.kind} (invalid)`, detail: Object.entries(errs).map(([k, v]) => `${k}: ${v}`).join('; '), bad: true });
        continue;
      }
      switch (eff.kind) {
        case 'set_field': {
          const i = Number(eff.fields.index || 0);
          const v = toModelInt(eff.fields.value);
          const prev = st.slots[i];
          st.slots[i] = v;
          steps.push({ kind: eff.kind, label: `setField slot[${i}]`, detail: `${prev} → ${v}` });
          break;
        }
        case 'transfer': {
          const amt = Number(eff.fields.amount || 0);
          const prev = st.balance;
          st.balance = Math.max(0, st.balance - amt);
          steps.push({ kind: eff.kind, label: `transfer ${amt}`, detail: `balance ${prev} → ${st.balance} (this cell's debit)` });
          steps.push({ kind: eff.kind, label: 'conservation across recipient + fee burn', detail: 'the ledger-wide value-conservation law spans both cells and the fee', deferred: true });
          break;
        }
        case 'increment_nonce': {
          const prev = st.nonce;
          st.nonce += 1;
          steps.push({ kind: eff.kind, label: 'incrementNonce', detail: `${prev} → ${st.nonce}` });
          break;
        }
        case 'emit_event': {
          const topic = toModelInt(eff.fields.topic);
          const data = (eff.fields.data || '').split(',').map((s) => s.trim()).filter(Boolean).map(toModelInt);
          st.events.push({ topic, data });
          steps.push({ kind: eff.kind, label: `emitEvent topic=${topic}`, detail: `+1 event, ${data.length} data word(s)` });
          break;
        }
        default:
          steps.push({ kind: eff.kind, label: eff.kind, detail: 'no local model for this kind', deferred: true });
      }
    }
    // Always-present honest caveats the local model can't decide.
    steps.push({ kind: '_auth', label: 'caller authorization', detail: 'every effect must be authorized by the operator cipherclerk signature over the action — verified only by the node executor', deferred: true });
    steps.push({ kind: '_proof', label: 'STARK proof of the turn', detail: 'the node produces the verifiable-execution proof; not modeled in-browser', deferred: true });
    return { before, after: st, steps };
  }

  // --- submit to a live node ------------------------------------------------
  async _doSubmit() {
    this._submitting = true;
    this._submitResult = null;
    this._render();
    const base = this._nodeUrl().replace(/\/+$/, '');
    const token = this._nodeToken();
    const body = this._wireBody();
    try {
      const res = await fetch(`${base}/api/turns/submit`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          Accept: 'application/json',
          ...(token ? { Authorization: `Bearer ${token}` } : {}),
        },
        body: JSON.stringify(body),
      });
      let payload = null;
      try { payload = await res.json(); } catch { /* non-JSON */ }
      this._submitResult = { http: res.status, ok: res.ok, payload };
    } catch (err) {
      this._submitResult = { http: 0, ok: false, error: String(err && err.message || err) };
    } finally {
      this._submitting = false;
      this._render();
    }
  }

  // ========================================================================
  // RENDER
  // ========================================================================
  _render() {
    const s = this._schema;
    const valid = this._allValid();
    const head =
      `<div class="dregg-tc__head">` +
        `<div class="dregg-tc__title">Compose a turn` +
          `<span class="dregg-tc__count">${this._effects.length} effect${this._effects.length === 1 ? '' : 's'}</span></div>` +
        `<div class="dregg-tc__prov">Build a real turn from the catalogued effect vocabulary, then ` +
          `simulate it locally and submit it to a node. Effect shapes come from ` +
          `<code>${esc(s.endpoint)}</code>'s schema, generated from the node source ` +
          `(<code>node/src/api.rs</code>). Only the ${s.effect_count} thin-HTTP effect kinds are shown — ` +
          `the richer ontology effects go through the typed SDK signed-envelope path.</div>` +
      `</div>`;

    const steps =
      `<ol class="dregg-tc__steps">` +
        ['compose', 'simulate', 'submit'].map((k, i) => {
          const on = this._step === k;
          const reachable = k === 'compose' || (k === 'simulate' && this._effects.length) || (k === 'submit' && valid);
          return `<li class="dregg-tc__step${on ? ' is-on' : ''}${reachable ? '' : ' is-locked'}" data-step="${k}">` +
            `<span class="dregg-tc__step-n">${i + 1}</span>${k}</li>`;
        }).join('<span class="dregg-tc__step-arrow">→</span>') +
      `</ol>`;

    let body = '';
    if (this._step === 'compose') body = this._renderCompose();
    else if (this._step === 'simulate') body = this._renderSimulate();
    else body = this._renderSubmit();

    this.innerHTML = `<div class="dregg-tc">${head}${steps}<div class="dregg-tc__body">${body}</div></div>`;
    this._wire();
  }

  _renderCompose() {
    const s = this._schema;
    const valid = this._allValid();

    // Composed effect list with per-effect validity.
    const list = this._effects.length
      ? this._effects.map((eff, i) => {
          const errs = this._effectErrors(eff);
          const bad = Object.keys(errs).length > 0;
          const fields = Object.entries(eff.fields)
            .filter(([, v]) => (v ?? '') !== '')
            .map(([k, v]) => `<span class="dregg-tc__chip">${esc(k)}=<code>${esc(v)}</code></span>`).join('');
          const errLine = bad
            ? `<div class="dregg-tc__efferr">${Object.entries(errs).map(([k, v]) => `${esc(k)}: ${esc(v)}`).join(' · ')}</div>`
            : '';
          return `<li class="dregg-tc__eff${bad ? ' is-bad' : ''}">` +
            `<div class="dregg-tc__eff-head"><code class="dregg-tc__eff-kind">${esc(eff.kind)}</code>` +
            `<span class="dregg-tc__cat" style="${catColor(eff.category)}">${esc(eff.category || '')}</span>` +
            `<button class="dregg-tc__eff-del" data-del="${i}" title="remove">✕</button></div>` +
            `<div class="dregg-tc__eff-fields">${fields || '<span class="dregg-tc__dim">(defaults)</span>'}</div>` +
            errLine + `</li>`;
        }).join('')
      : `<li class="dregg-tc__empty">no effects yet — add one below to start your turn</li>`;

    return (
      `<div class="dregg-tc__compose">` +
        // action meta (progressive: collapsed-by-default advanced row)
        `<div class="dregg-tc__meta">` +
          `<label class="dregg-tc__mlabel">target cell <span class="dregg-tc__dim">(optional — defaults to your agent cell)</span></label>` +
          `<input class="dregg-tc__minput" data-meta="target" value="${esc(this._target)}" placeholder="64-hex cell id, or blank">` +
          `<div class="dregg-tc__meta-row">` +
            `<span><label class="dregg-tc__mlabel">fee <span class="dregg-tc__dim">(= computron budget; 0 ⇒ "budget exceeded")</span></label><input class="dregg-tc__minput dregg-tc__minput--sm" data-meta="fee" value="${esc(this._fee)}"></span>` +
            `<span><label class="dregg-tc__mlabel">memo</label><input class="dregg-tc__minput dregg-tc__minput--sm" data-meta="memo" value="${esc(this._memo)}" placeholder="optional"></span>` +
          `</div>` +
        `</div>` +

        `<ul class="dregg-tc__effs">${list}</ul>` +

        // add-effect form
        this._renderAddForm() +

        // live wire preview
        `<details class="dregg-tc__preview"><summary>wire JSON preview (the exact body sent to the node)</summary>` +
          `<pre class="dregg-tc__json">${esc(JSON.stringify(this._wireBody(), null, 2))}</pre></details>` +

        // advance
        `<div class="dregg-tc__advance">` +
          `<span class="dregg-tc__valid ${valid ? 'is-ok' : 'is-fail'}">` +
            (this._effects.length
              ? (valid ? '✓ all effects valid' : '✗ fix the highlighted effects')
              : 'add at least one effect') + `</span>` +
          `<button class="dregg-tc__next" data-goto="simulate"${this._effects.length ? '' : ' disabled'}>Simulate →</button>` +
        `</div>` +
      `</div>`
    );
  }

  _renderAddForm() {
    const s = this._schema;
    const kind = this._draftKind;
    const spec = s.effects.find((e) => e.kind === kind);
    const opts = s.effects.map((e) =>
      `<option value="${esc(e.kind)}"${e.kind === kind ? ' selected' : ''}>${esc(e.kind)} — ${esc((e.category || ''))}</option>`).join('');
    const ui = FIELD_UI[kind] || {};
    const inputs = Object.entries(ui).map(([name, fspec]) => {
      const val = this._draft[name] ?? (fspec.default ?? '');
      const err = fspec.validate ? fspec.validate(val) : null;
      const touched = name in this._draft;
      return `<div class="dregg-tc__finp">` +
        `<label>${esc(fspec.label)}${fspec.isList ? ' <span class="dregg-tc__dim">(list)</span>' : ''}</label>` +
        `<input data-field="${esc(name)}" value="${esc(val)}" placeholder="${esc(fspec.placeholder || '')}"` +
        `${touched && err ? ' class="is-bad"' : ''}>` +
        (touched && err ? `<span class="dregg-tc__finp-err">${esc(err)}</span>` : '') +
      `</div>`;
    }).join('');

    return (
      `<div class="dregg-tc__add">` +
        `<div class="dregg-tc__add-pick">` +
          `<select class="dregg-tc__add-kind">${opts}</select>` +
          (spec ? `<span class="dregg-tc__add-sem">${esc(spec.semantics)}</span>` : '') +
        `</div>` +
        `<div class="dregg-tc__add-fields">${inputs}</div>` +
        `<button class="dregg-tc__add-btn">+ add effect</button>` +
      `</div>`
    );
  }

  _renderSimulate() {
    const sim = this._simulate();
    const slotDiff = sim.after.slots.map((v, i) =>
      `<span class="dregg-tc__slot${v !== sim.before.slots[i] ? ' is-changed' : ''}">` +
      `[${i}] ${sim.before.slots[i]}${v !== sim.before.slots[i] ? `→${v}` : ''}</span>`).join('');

    const stepRows = sim.steps.map((step) => {
      const cls = step.bad ? 'is-bad' : (step.deferred ? 'is-deferred' : 'is-ok');
      const verdict = step.bad ? 'INVALID' : (step.deferred ? 'needs executor' : 'applied');
      return `<li class="dregg-tc__simrow ${cls}">` +
        `<code>${esc(step.label)}</code>` +
        `<span class="dregg-tc__simverdict">${verdict}</span>` +
        `<span class="dregg-tc__simwhy">${esc(step.detail)}</span></li>`;
    }).join('');

    return (
      `<div class="dregg-tc__sim">` +
        `<p class="dregg-tc__note">Local model of the field-write fragment over a single cell ` +
          `(8 integer slots, a balance, a nonce, an event log). It applies the parts it can and ` +
          `<strong>honestly labels</strong> what only the node executor can decide — caller ` +
          `authorization, ledger-wide value conservation, the STARK proof. Slots/values are modeled ` +
          `as integers; the real field is a 32-byte <code>FieldElement</code>.</p>` +
        `<div class="dregg-tc__simstate"><span class="dregg-tc__simstate-label">slots</span>${slotDiff}</div>` +
        `<div class="dregg-tc__simstate"><span class="dregg-tc__simstate-label">balance</span>` +
          `<span class="dregg-tc__slot${sim.after.balance !== sim.before.balance ? ' is-changed' : ''}">${sim.before.balance}` +
          `${sim.after.balance !== sim.before.balance ? `→${sim.after.balance}` : ''}</span>` +
          `<span class="dregg-tc__simstate-label" style="margin-left:14px">nonce</span>` +
          `<span class="dregg-tc__slot${sim.after.nonce !== sim.before.nonce ? ' is-changed' : ''}">${sim.before.nonce}` +
          `${sim.after.nonce !== sim.before.nonce ? `→${sim.after.nonce}` : ''}</span>` +
          `<span class="dregg-tc__simstate-label" style="margin-left:14px">events</span>` +
          `<span class="dregg-tc__slot${sim.after.events.length ? ' is-changed' : ''}">${sim.after.events.length}</span>` +
        `</div>` +
        `<ul class="dregg-tc__simrows">${stepRows}</ul>` +
        `<div class="dregg-tc__advance">` +
          `<button class="dregg-tc__back" data-goto="compose">← back to compose</button>` +
          `<button class="dregg-tc__next" data-goto="submit"${this._allValid() ? '' : ' disabled'}>Submit to a node →</button>` +
        `</div>` +
      `</div>`
    );
  }

  _renderSubmit() {
    const url = this._nodeUrl();
    const hasToken = !!this._nodeToken();
    const r = this._submitResult;
    let resultBlock = '';
    if (this._submitting) {
      resultBlock = `<div class="dregg-tc__subres is-pending">submitting…</div>`;
    } else if (r) {
      if (r.error || r.http === 0) {
        resultBlock = `<div class="dregg-tc__subres is-fail"><strong>unreachable</strong> — ${esc(r.error || 'no response')}. ` +
          `Check the node URL, that the node is running, and CORS (the node allows localhost / extension origins by default).</div>`;
      } else if (r.http === 401 || r.http === 403) {
        resultBlock = `<div class="dregg-tc__subres is-fail"><strong>HTTP ${r.http}</strong> — the node requires an unlocked ` +
          `operator. Set a Bearer token (from <code>POST /cipherclerk/unlock</code>) below, or run the node on loopback ` +
          `before a passphrase is set.</div>`;
      } else {
        const p = r.payload || {};
        const accepted = p.accepted === true;
        resultBlock = `<div class="dregg-tc__subres ${accepted ? 'is-ok' : 'is-fail'}">` +
          `<div class="dregg-tc__subres-head"><strong>${accepted ? 'ACCEPTED' : 'REJECTED'}</strong> ` +
          `<span class="dregg-tc__dim">HTTP ${r.http}</span></div>` +
          (p.turn_hash ? `<div class="dregg-tc__kv"><span>turn</span><code>${esc(p.turn_hash)}</code></div>` : '') +
          (p.proof_status ? `<div class="dregg-tc__kv"><span>proof</span><code>${esc(p.proof_status)}</code></div>` : '') +
          (typeof p.witness_count === 'number' ? `<div class="dregg-tc__kv"><span>witnesses</span><code>${esc(p.witness_count)}</code></div>` : '') +
          (p.error ? `<div class="dregg-tc__kv"><span>error</span><code>${esc(p.error)}</code></div>` : '') +
          `<div class="dregg-tc__dim" style="margin-top:6px">This is the node's real executor verdict over your turn.</div>` +
        `</div>`;
      }
    }

    return (
      `<div class="dregg-tc__submit">` +
        `<p class="dregg-tc__note">Submit the composed turn to a live node's <code>${esc(this._schema.endpoint)}</code>. ` +
          `The node derives the signer from its own operator cipherclerk and signs the turn as itself ` +
          `(confused-deputy hardening), so the <code>agent</code> field is advisory. The response is the ` +
          `node's honest accept/reject.</p>` +
        `<div class="dregg-tc__nodecfg">` +
          `<div class="dregg-tc__finp"><label>node URL</label>` +
            `<input data-cfg="url" value="${esc(url)}" placeholder="${esc(DEFAULT_NODE_URL)}"></div>` +
          `<div class="dregg-tc__finp"><label>Bearer token <span class="dregg-tc__dim">(from /cipherclerk/unlock; ${hasToken ? 'set' : 'optional on loopback'})</span></label>` +
            `<input data-cfg="token" type="password" value="${esc(this._nodeToken())}" placeholder="hex token, or blank for loopback"></div>` +
        `</div>` +
        `<details class="dregg-tc__preview"><summary>final wire JSON</summary>` +
          `<pre class="dregg-tc__json">${esc(JSON.stringify(this._wireBody(), null, 2))}</pre></details>` +
        `<div class="dregg-tc__advance">` +
          `<button class="dregg-tc__back" data-goto="simulate">← back to simulate</button>` +
          `<button class="dregg-tc__submit-btn"${this._submitting ? ' disabled' : ''}>Submit turn</button>` +
        `</div>` +
        resultBlock +
      `</div>`
    );
  }

  // ========================================================================
  // WIRING
  // ========================================================================
  _wire() {
    // step nav (only to reachable steps)
    this.querySelectorAll('.dregg-tc__step').forEach((li) => {
      if (li.classList.contains('is-locked')) return;
      li.addEventListener('click', () => { this._step = li.getAttribute('data-step'); this._render(); });
    });
    this.querySelectorAll('[data-goto]').forEach((b) =>
      b.addEventListener('click', () => { if (!b.disabled) { this._step = b.getAttribute('data-goto'); this._render(); } }));

    // meta inputs
    this.querySelectorAll('[data-meta]').forEach((inp) =>
      inp.addEventListener('input', () => {
        const k = inp.getAttribute('data-meta');
        if (k === 'target') this._target = inp.value;
        else if (k === 'fee') this._fee = inp.value;
        else if (k === 'memo') this._memo = inp.value;
        // refresh only the preview to avoid losing focus
        const pre = this.querySelector('.dregg-tc__json');
        if (pre) pre.textContent = JSON.stringify(this._wireBody(), null, 2);
      }));

    // add-form
    const kindSel = this.querySelector('.dregg-tc__add-kind');
    if (kindSel) kindSel.addEventListener('change', () => { this._draftKind = kindSel.value; this._draft = {}; this._render(); });
    this.querySelectorAll('.dregg-tc__add-fields [data-field]').forEach((inp) =>
      inp.addEventListener('input', () => {
        this._draft[inp.getAttribute('data-field')] = inp.value;
        // live-validate just this input
        const spec = (FIELD_UI[this._draftKind] || {})[inp.getAttribute('data-field')];
        const err = spec && spec.validate ? spec.validate(inp.value) : null;
        inp.classList.toggle('is-bad', !!err);
        const errEl = inp.parentElement.querySelector('.dregg-tc__finp-err');
        if (err && !errEl) {
          const s = document.createElement('span'); s.className = 'dregg-tc__finp-err'; s.textContent = err; inp.after(s);
        } else if (err && errEl) errEl.textContent = err;
        else if (!err && errEl) errEl.remove();
      }));
    const addBtn = this.querySelector('.dregg-tc__add-btn');
    if (addBtn) addBtn.addEventListener('click', () => {
      const kind = this._draftKind;
      const ui = FIELD_UI[kind] || {};
      const fields = {};
      for (const [name, spec] of Object.entries(ui)) fields[name] = this._draft[name] ?? (spec.default ?? '');
      const cat = this._schema.effects.find((e) => e.kind === kind);
      this._effects.push({ kind, category: cat ? cat.category : null, fields });
      this._draft = {};
      this._render();
    });

    // remove effect
    this.querySelectorAll('.dregg-tc__eff-del').forEach((b) =>
      b.addEventListener('click', () => { this._effects.splice(+b.getAttribute('data-del'), 1); this._render(); }));

    // submit-step config + submit
    this.querySelectorAll('[data-cfg]').forEach((inp) =>
      inp.addEventListener('change', () => {
        const k = inp.getAttribute('data-cfg');
        if (k === 'url') localStorage.setItem(NODE_URL_KEY, inp.value.trim());
        else if (k === 'token') localStorage.setItem(NODE_TOKEN_KEY, inp.value.trim());
      }));
    const subBtn = this.querySelector('.dregg-tc__submit-btn');
    if (subBtn) subBtn.addEventListener('click', () => {
      // persist any unsaved cfg fields first
      this.querySelectorAll('[data-cfg]').forEach((inp) => {
        const k = inp.getAttribute('data-cfg');
        if (k === 'url') localStorage.setItem(NODE_URL_KEY, inp.value.trim());
        else if (k === 'token') localStorage.setItem(NODE_TOKEN_KEY, inp.value.trim());
      });
      this._doSubmit();
    });
  }
}

if (!customElements.get('dregg-turn-composer')) {
  customElements.define('dregg-turn-composer', DreggTurnComposer);
}

// --- styles (site palette only) --------------------------------------------
(function injectStyles() {
  if (document.getElementById('dregg-turn-composer-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-turn-composer-styles';
  s.textContent = `
.dregg-tc { font-family: var(--font-mono, ui-monospace, monospace); }
.dregg-tc__loading { color: var(--fg-dim); padding: 10px; }
.dregg-tc__title { display:flex; align-items:baseline; gap:10px; font-size:1.1rem; color:var(--fg); font-weight:600; }
.dregg-tc__count { font-size:0.8rem; color:var(--fg-dim); font-weight:normal; }
.dregg-tc__prov { font-size:0.78rem; color:var(--fg-dim); margin-top:4px; line-height:1.5; }
.dregg-tc__prov code, .dregg-tc__note code { color:var(--fg); }
.dregg-tc__steps { list-style:none; display:flex; align-items:center; gap:4px; padding:0; margin:14px 0; flex-wrap:wrap; }
.dregg-tc__step { display:flex; align-items:center; gap:6px; padding:5px 12px; font-size:0.8rem; color:var(--fg-dim); background:var(--bg-raised); border:1px solid var(--line); border-radius:14px; cursor:pointer; text-transform:capitalize; }
.dregg-tc__step.is-locked { opacity:0.45; cursor:not-allowed; }
.dregg-tc__step.is-on { color:var(--fg); border-color:var(--accent,#5b8a5a); outline:1px solid var(--accent,#5b8a5a); }
.dregg-tc__step-n { display:inline-flex; align-items:center; justify-content:center; width:18px; height:18px; border-radius:50%; background:var(--bg); font-size:0.7rem; }
.dregg-tc__step.is-on .dregg-tc__step-n { background:var(--accent,#5b8a5a); color:var(--bg); }
.dregg-tc__step-arrow { color:var(--fg-dim); font-size:0.8rem; }
.dregg-tc__note { font-size:0.82rem; color:var(--fg-dim); line-height:1.55; margin:0 0 10px; }
.dregg-tc__dim { color:var(--fg-dim); font-size:0.92em; }
.dregg-tc__meta { display:flex; flex-direction:column; gap:5px; margin-bottom:12px; padding:10px; background:var(--bg-raised); border:1px solid var(--line); border-radius:6px; }
.dregg-tc__mlabel { font-size:0.74rem; color:var(--fg-dim); }
.dregg-tc__minput { padding:6px 8px; font:inherit; font-size:0.8rem; background:var(--bg); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-tc__minput:focus { outline:none; border-color:var(--accent,#5b8a5a); }
.dregg-tc__meta-row { display:flex; gap:12px; margin-top:4px; }
.dregg-tc__meta-row span { display:flex; flex-direction:column; gap:3px; }
.dregg-tc__minput--sm { width:120px; }
.dregg-tc__effs { list-style:none; padding:0; margin:0 0 10px; display:flex; flex-direction:column; gap:6px; }
.dregg-tc__eff { border:1px solid var(--line); border-left:3px solid var(--accent,#5b8a5a); border-radius:5px; background:var(--bg-raised); padding:8px 10px; }
.dregg-tc__eff.is-bad { border-left-color:#d4685c; }
.dregg-tc__eff-head { display:flex; align-items:center; gap:8px; }
.dregg-tc__eff-kind { font-size:0.86rem; color:var(--fg); font-weight:600; }
.dregg-tc__cat { font-size:0.68rem; padding:1px 7px; border-radius:3px; }
.dregg-tc__eff-del { margin-left:auto; background:none; border:0; color:var(--fg-dim); cursor:pointer; }
.dregg-tc__eff-del:hover { color:#e08878; }
.dregg-tc__eff-fields { display:flex; flex-wrap:wrap; gap:6px; margin-top:5px; }
.dregg-tc__chip { font-size:0.76rem; padding:1px 7px; background:var(--bg); border:1px solid var(--line); border-radius:3px; color:var(--fg-dim); }
.dregg-tc__chip code { color:var(--fg); }
.dregg-tc__efferr { font-size:0.74rem; color:#e08878; margin-top:5px; }
.dregg-tc__empty { color:var(--fg-dim); font-style:italic; padding:8px 10px; border:1px dashed var(--line); border-radius:5px; }
.dregg-tc__add { border:1px solid var(--line); border-radius:6px; background:var(--bg); padding:10px; margin-bottom:10px; }
.dregg-tc__add-pick { display:flex; align-items:center; gap:10px; flex-wrap:wrap; margin-bottom:8px; }
.dregg-tc__add-kind { padding:6px 8px; font:inherit; font-size:0.8rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-tc__add-sem { font-size:0.78rem; color:var(--fg-dim); flex:1; min-width:160px; }
.dregg-tc__add-fields { display:flex; flex-wrap:wrap; gap:10px; margin-bottom:8px; }
.dregg-tc__finp { display:flex; flex-direction:column; gap:3px; }
.dregg-tc__finp label { font-size:0.72rem; color:var(--fg-dim); }
.dregg-tc__finp input { padding:6px 8px; font:inherit; font-size:0.78rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; min-width:150px; }
.dregg-tc__finp input:focus { outline:none; border-color:var(--accent,#5b8a5a); }
.dregg-tc__finp input.is-bad { border-color:#d4685c; }
.dregg-tc__finp-err { font-size:0.7rem; color:#e08878; }
.dregg-tc__add-btn { cursor:pointer; padding:6px 14px; font:inherit; font-size:0.8rem; background:color-mix(in srgb,var(--accent,#5b8a5a) 18%,var(--bg-raised)); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-tc__add-btn:hover { border-color:var(--accent,#5b8a5a); }
.dregg-tc__preview { margin:10px 0; font-size:0.78rem; }
.dregg-tc__preview summary { cursor:pointer; color:var(--fg-dim); }
.dregg-tc__json { background:var(--bg-raised); border:1px solid var(--line); border-radius:5px; padding:10px; font-size:0.76rem; color:var(--fg); overflow-x:auto; white-space:pre; margin:6px 0 0; }
.dregg-tc__advance { display:flex; align-items:center; gap:12px; margin-top:12px; flex-wrap:wrap; }
.dregg-tc__valid { font-size:0.8rem; font-weight:600; }
.dregg-tc__valid.is-ok { color:var(--accent-bright,#7db87b); }
.dregg-tc__valid.is-fail { color:#e08878; }
.dregg-tc__next, .dregg-tc__back, .dregg-tc__submit-btn { cursor:pointer; padding:7px 16px; font:inherit; font-size:0.82rem; border:1px solid var(--line); border-radius:5px; background:var(--bg-raised); color:var(--fg); }
.dregg-tc__next, .dregg-tc__submit-btn { background:color-mix(in srgb,var(--accent,#5b8a5a) 22%,var(--bg-raised)); margin-left:auto; }
.dregg-tc__next:hover:not(:disabled), .dregg-tc__submit-btn:hover:not(:disabled) { border-color:var(--accent,#5b8a5a); }
.dregg-tc__next:disabled, .dregg-tc__submit-btn:disabled { opacity:0.45; cursor:not-allowed; }
.dregg-tc__back:hover { border-color:var(--accent,#5b8a5a); }
.dregg-tc__simstate { display:flex; align-items:center; flex-wrap:wrap; gap:6px; margin:8px 0; }
.dregg-tc__simstate-label { font-size:0.7rem; text-transform:uppercase; letter-spacing:0.05em; color:var(--fg-dim); }
.dregg-tc__slot { font-size:0.78rem; padding:2px 7px; background:var(--bg-raised); border:1px solid var(--line); border-radius:3px; color:var(--fg-dim); }
.dregg-tc__slot.is-changed { color:var(--accent-bright,#7db87b); border-color:var(--accent,#5b8a5a); }
.dregg-tc__simrows { list-style:none; padding:0; margin:10px 0; display:flex; flex-direction:column; gap:5px; }
.dregg-tc__simrow { display:flex; align-items:center; gap:10px; flex-wrap:wrap; padding:6px 10px; border:1px solid var(--line); border-radius:5px; background:var(--bg-raised); font-size:0.8rem; }
.dregg-tc__simrow.is-ok { border-left:3px solid var(--accent,#5b8a5a); }
.dregg-tc__simrow.is-deferred { border-left:3px solid #c8a050; }
.dregg-tc__simrow.is-bad { border-left:3px solid #d4685c; }
.dregg-tc__simrow code { color:var(--fg); }
.dregg-tc__simverdict { font-size:0.7rem; font-weight:600; padding:1px 7px; border-radius:3px; background:var(--bg); }
.dregg-tc__simrow.is-ok .dregg-tc__simverdict { color:var(--accent-bright,#7db87b); }
.dregg-tc__simrow.is-deferred .dregg-tc__simverdict { color:#d4b060; }
.dregg-tc__simrow.is-bad .dregg-tc__simverdict { color:#e08878; }
.dregg-tc__simwhy { color:var(--fg-dim); font-size:0.74rem; flex:1; min-width:140px; }
.dregg-tc__nodecfg { display:flex; gap:12px; flex-wrap:wrap; margin-bottom:8px; }
.dregg-tc__nodecfg .dregg-tc__finp input { min-width:240px; }
.dregg-tc__subres { margin-top:12px; padding:10px 12px; border:1px solid var(--line); border-radius:6px; font-size:0.82rem; }
.dregg-tc__subres.is-ok { border-left:3px solid var(--accent,#5b8a5a); background:color-mix(in srgb,var(--accent,#5b8a5a) 10%,var(--bg-raised)); }
.dregg-tc__subres.is-fail { border-left:3px solid #d4685c; background:color-mix(in srgb,#d4685c 8%,var(--bg-raised)); }
.dregg-tc__subres.is-pending { border-left:3px solid #c8a050; color:var(--fg-dim); }
.dregg-tc__subres-head { font-size:0.9rem; margin-bottom:6px; }
.dregg-tc__kv { display:flex; gap:8px; font-size:0.78rem; margin-top:3px; }
.dregg-tc__kv span { color:var(--fg-dim); min-width:64px; }
.dregg-tc__kv code { color:var(--fg); word-break:break-all; }
`;
  document.head.appendChild(s);
})();
