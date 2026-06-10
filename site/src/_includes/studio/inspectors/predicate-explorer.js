/**
 * <dregg-predicate-explorer> — the CELL-PROGRAM / PREDICATE LANGUAGE explainer.
 *
 * Upgrades the instance-only `<dregg-cell-program>` / `<dregg-state-constraint>`
 * inspectors into a TEACHING + COMPOSING surface:
 *
 *   1. Browses the whole predicate language — every `StateConstraint` variant,
 *      the four `CellProgram` kinds, and the six `TransitionGuard` kinds — with
 *      typed fields and one-line semantics, all generated from the verified Rust
 *      source (`cell/src/program.rs`, cross-checked against the JSON view in
 *      `wasm/src/bindings.rs`) by `site/tools/gen-ontology-catalog.js`. Cannot
 *      drift from the evaluator it documents.
 *
 *   2. Lets the user compose a small `Predicate` over an (old → new) 8-slot
 *      cell state and SEE WHAT IT ACCEPTS OR REJECTS. The locally-evaluable
 *      constraints (pure post-state / (old,new) field comparisons) are checked
 *      against a faithful JS MIRROR of the Rust `StateConstraint::evaluate`
 *      semantics — honest about which constraints need the executor (witness /
 *      proof / side-table) and are therefore modeled-as-deferred, not faked.
 *
 * No node / wasm required: this is documentation + a pure-function evaluator
 * over the field-comparison fragment of the language.
 *
 * Usage:  <dregg-predicate-explorer></dregg-predicate-explorer>
 */

const PRED_CATALOG_URL = '/_includes/studio/predicate-catalog.generated.json';
const NSLOTS = 8;

function esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

// ---------------------------------------------------------------------------
// Faithful JS MIRROR of the locally-evaluable fragment of
// `StateConstraint::evaluate` (cell/src/program.rs). Slots are plain integers
// here (the real field is a 32-byte FieldElement; for the explainer we model
// slots as JS numbers / BigInt-safe integers and document the simplification).
//
// Each entry returns { ok: bool, why: string }. Constraints that need a
// witness / proof / executor side-table are NOT mirrored — they return
// { deferred: true } so the UI labels them honestly as "needs executor".
// ---------------------------------------------------------------------------

function asInt(v) { const n = Number(v); return Number.isFinite(n) ? n : 0; }

const EVAL = {
  FieldEquals: (c, o, n) =>
    ({ ok: n[c.index] === asInt(c.value), why: `new[${c.index}]=${n[c.index]} ${n[c.index] === asInt(c.value) ? '=' : '≠'} ${asInt(c.value)}` }),
  FieldGte: (c, o, n) =>
    ({ ok: n[c.index] >= asInt(c.value), why: `new[${c.index}]=${n[c.index]} ${n[c.index] >= asInt(c.value) ? '≥' : '<'} ${asInt(c.value)}` }),
  FieldLte: (c, o, n) =>
    ({ ok: n[c.index] <= asInt(c.value), why: `new[${c.index}]=${n[c.index]} ${n[c.index] <= asInt(c.value) ? '≤' : '>'} ${asInt(c.value)}` }),
  FieldLteField: (c, o, n) =>
    ({ ok: n[c.left_index] <= n[c.right_index], why: `new[${c.left_index}]=${n[c.left_index]} ${n[c.left_index] <= n[c.right_index] ? '≤' : '>'} new[${c.right_index}]=${n[c.right_index]}` }),
  SumEquals: (c, o, n) => {
    const s = (c.indices || []).reduce((a, i) => a + n[i], 0);
    return { ok: s === asInt(c.value), why: `Σnew[${(c.indices||[]).join(',')}]=${s} ${s === asInt(c.value) ? '=' : '≠'} ${asInt(c.value)}` };
  },
  WriteOnce: (c, o, n) =>
    ({ ok: o[c.index] === 0 || n[c.index] === o[c.index], why: o[c.index] === 0 ? `slot[${c.index}] first write ${o[c.index]}→${n[c.index]} OK` : `slot[${c.index}] frozen at ${o[c.index]}, new=${n[c.index]}` }),
  Immutable: (c, o, n) =>
    ({ ok: n[c.index] === o[c.index], why: `slot[${c.index}] ${o[c.index]}→${n[c.index]} ${n[c.index] === o[c.index] ? '(unchanged)' : '(MUTATED)'}` }),
  Monotonic: (c, o, n) =>
    ({ ok: n[c.index] >= o[c.index], why: `slot[${c.index}] ${o[c.index]}→${n[c.index]} ${n[c.index] >= o[c.index] ? 'non-decreasing' : 'DECREASED'}` }),
  StrictMonotonic: (c, o, n) =>
    ({ ok: n[c.index] > o[c.index], why: `slot[${c.index}] ${o[c.index]}→${n[c.index]} ${n[c.index] > o[c.index] ? 'strictly up' : 'NOT strictly up'}` }),
  FieldDelta: (c, o, n) =>
    ({ ok: n[c.index] === o[c.index] + asInt(c.delta), why: `slot[${c.index}] ${o[c.index]}+${asInt(c.delta)} ${n[c.index] === o[c.index] + asInt(c.delta) ? '=' : '≠'} ${n[c.index]}` }),
  FieldDeltaInRange: (c, o, n) => {
    const d = n[c.index] - o[c.index];
    const ok = d >= asInt(c.min_delta) && d <= asInt(c.max_delta);
    return { ok, why: `Δslot[${c.index}]=${d} ${ok ? '∈' : '∉'} [${asInt(c.min_delta)},${asInt(c.max_delta)}]` };
  },
  SumEqualsAcross: (c, o, n) => {
    const sIn = (c.input_fields || []).reduce((a, i) => a + n[i], 0);
    const sInOld = (c.input_fields || []).reduce((a, i) => a + o[i], 0);
    const sOut = (c.output_fields || []).reduce((a, i) => a + n[i], 0);
    const ok = sIn === sInOld + sOut;
    return { ok, why: `Σnew_in=${sIn} ${ok ? '=' : '≠'} Σold_in+Σnew_out=${sInOld}+${sOut}` };
  },
  MonotonicSequence: (c, o, n) =>
    ({ ok: n[c.seq_index] === o[c.seq_index] + 1, why: `seq[${c.seq_index}] ${o[c.seq_index]}→${n[c.seq_index]} ${n[c.seq_index] === o[c.seq_index] + 1 ? '(+1)' : '(not +1)'}` }),
  AllowedTransitions: (c, o, n) => {
    const pairs = (c.allowed || []).map((p) => `${asInt(p[0])}→${asInt(p[1])}`);
    const cur = `${o[c.slot_index]}→${n[c.slot_index]}`;
    return { ok: pairs.includes(cur), why: `slot[${c.slot_index}] ${cur} ${pairs.includes(cur) ? '∈' : '∉'} {${pairs.join(',')}}` };
  },
  AnyOf: (c, o, n) => {
    const rs = (c.variants || []).map((v) => evalConstraint(v, o, n));
    const ok = rs.some((r) => r.ok);
    return { ok, why: `${rs.filter((r) => r.ok).length}/${rs.length} alternatives hold` };
  },
};

function evalConstraint(c, oldS, newS) {
  const fn = EVAL[c.kind];
  if (!fn) return { deferred: true, why: 'needs the executor (witness / proof / side-table)' };
  try { return fn(c, oldS, newS); }
  catch (e) { return { ok: false, why: 'eval error: ' + (e && e.message || e) }; }
}

/** Compact `field=value` summary of a composed constraint's scalar fields. */
function constraintArgsSummary(c) {
  return Object.keys(c)
    .filter((k) => k !== 'kind')
    .map((k) => `${k}=${Array.isArray(c[k]) ? `[${c[k].map((x) => (x && x.kind) || x).join(',')}]` : c[k]}`)
    .join(', ');
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class DreggPredicateExplorer extends HTMLElement {
  connectedCallback() {
    // Composer model: an old/new 8-slot state + a list of composed constraints.
    this._old = new Array(NSLOTS).fill(0);
    this._new = new Array(NSLOTS).fill(0);
    this._composed = [];
    this._tab = 'language'; // 'language' | 'compose'
    this._load();
  }

  async _load() {
    if (!this._cat) {
      const url = this.getAttribute('src') || PRED_CATALOG_URL;
      this.innerHTML = `<div class="dregg-pred__loading">Loading predicate language…</div>`;
      try {
        const res = await fetch(url, { headers: { Accept: 'application/json' } });
        if (!res.ok) throw new Error('status ' + res.status);
        this._cat = await res.json();
      } catch (err) {
        this.innerHTML =
          `<div class="dregg-inspector dregg-inspector--err">Could not load predicate catalog ` +
          `(${esc(err && err.message || err)}). Run <code>node site/tools/gen-ontology-catalog.js</code> ` +
          `and rebuild.</div>`;
        return;
      }
    }
    this._render();
    // dregg://constraint/<kind> deep link (resolver.js → ?constraint=<kind>):
    // open the language reference at that entry, once.
    if (!this._deepLinked) {
      this._deepLinked = true;
      try {
        const want = new URLSearchParams(window.location.search).get('constraint');
        if (want) {
          this._tab = 'language';
          this._render();
          const el = this.querySelector(`#pred-${CSS.escape(want)}`);
          if (el) {
            el.classList.add('is-deeplinked');
            el.scrollIntoView({ behavior: 'smooth', block: 'center' });
          }
        }
      } catch { /* no URL context (embedded) */ }
    }
  }

  _render() {
    const c = this._cat;
    const cov = c.coverage || {};
    const tabs =
      `<div class="dregg-pred__tabs">` +
        `<button class="dregg-pred__tab${this._tab === 'language' ? ' is-on' : ''}" data-tab="language">Language reference</button>` +
        `<button class="dregg-pred__tab${this._tab === 'compose' ? ' is-on' : ''}" data-tab="compose">Compose &amp; test</button>` +
      `</div>`;

    const head =
      `<div class="dregg-pred__head">` +
        `<div class="dregg-pred__title">Cell-program / predicate language` +
          `<span class="dregg-pred__count">${c.constraint_count} constraints</span></div>` +
        `<div class="dregg-pred__prov">Generated from the verified Rust source ` +
          `(<code>cell/src/program.rs</code> — <code>CellProgram</code>, <code>StateConstraint</code>, ` +
          `<code>TransitionGuard</code>), cross-checked against the studio's JSON view. ` +
          `${cov.constraints_in_view}/${c.constraint_count} render as instances; ` +
          `${cov.locally_evaluable}/${c.constraint_count} are evaluable in this in-browser explainer ` +
          `(the rest need the executor — witness / proof / side-table).</div>` +
      `</div>`;

    const body = this._tab === 'language' ? this._renderLanguage() : this._renderCompose();
    this.innerHTML = `<div class="dregg-pred">${head}${tabs}<div class="dregg-pred__body">${body}</div></div>`;
    this._wire();
  }

  _renderLanguage() {
    const c = this._cat;
    const kindBlock = (title, items, kindKey) =>
      `<section class="dregg-pred__sec"><h3>${esc(title)}</h3>` +
      items.map((it) => {
        const fields = (it.fields || []).map((f) =>
          `<span class="dregg-pred__field"><span class="dregg-pred__fname">${esc(f.name)}</span>` +
          `<span class="dregg-pred__ftype">${esc(f.type)}</span></span>`).join('');
        const evalable = kindKey === 'constraint'
          ? (it.locally_evaluable
              ? `<span class="dregg-pred__tag dregg-pred__tag--live" title="checked against a faithful JS mirror of the Rust evaluator">evaluable here</span>`
              : `<span class="dregg-pred__tag dregg-pred__tag--exec" title="needs the executor: witness / proof / side-table">needs executor</span>`)
          : '';
        return `<div class="dregg-pred__item" id="pred-${esc(it.kind || it.name)}">` +
          `<div class="dregg-pred__item-head"><code class="dregg-pred__kind">${esc(it.kind || it.name)}</code>${evalable}</div>` +
          `<div class="dregg-pred__sem">${esc(it.semantics)}</div>` +
          (fields ? `<div class="dregg-pred__fields">${fields}</div>` : '') +
        `</div>`;
      }).join('') + `</section>`;

    return (
      kindBlock('Cell-program kinds', c.cell_program_kinds, 'program') +
      kindBlock('Transition guards (case selection)', c.transition_guards, 'guard') +
      kindBlock('State constraints (the predicate vocabulary)',
        c.constraints.map((x) => ({ ...x, kind: x.name })), 'constraint')
    );
  }

  _renderCompose() {
    const c = this._cat;
    const evalable = c.constraints.filter((x) => x.locally_evaluable);
    const slotRow = (label, arr, which) =>
      `<div class="dregg-pred__slots"><span class="dregg-pred__slots-label">${label}</span>` +
      arr.map((v, i) =>
        `<input class="dregg-pred__slot" type="number" data-which="${which}" data-idx="${i}" ` +
        `value="${v}" aria-label="${label} slot ${i}">`).join('') + `</div>`;

    const composedList = this._composed.length
      ? this._composed.map((c2, i) => {
          const r = evalConstraint(c2, this._old, this._new);
          const cls = r.deferred ? 'is-deferred' : (r.ok ? 'is-ok' : 'is-fail');
          const verdict = r.deferred ? 'deferred' : (r.ok ? 'ACCEPT' : 'REJECT');
          return `<li class="dregg-pred__row ${cls}">` +
            `<code>${esc(c2.kind)}(${esc(constraintArgsSummary(c2))})</code>` +
            `<span class="dregg-pred__verdict">${verdict}</span>` +
            `<span class="dregg-pred__why">${esc(r.why || '')}</span>` +
            `<button class="dregg-pred__del" data-del="${i}" title="remove">✕</button></li>`;
        }).join('')
      : `<li class="dregg-pred__empty">no constraints yet — add one below</li>`;

    // Overall verdict (implicit AND over all composed; deferred are skipped honestly)
    const results = this._composed.map((c2) => evalConstraint(c2, this._old, this._new));
    const decidable = results.filter((r) => !r.deferred);
    const allOk = decidable.length && decidable.every((r) => r.ok);
    const anyDeferred = results.some((r) => r.deferred);
    const overall = !this._composed.length
      ? `<span class="dregg-pred__overall is-neutral">add constraints to test</span>`
      : `<span class="dregg-pred__overall ${allOk ? 'is-ok' : 'is-fail'}">` +
        `transition ${allOk ? 'ACCEPTED' : 'REJECTED'} by the decidable constraints` +
        (anyDeferred ? ` (some need the executor — not decided here)` : '') + `</span>`;

    // The add-constraint form: pick a locally-evaluable variant + a couple ints.
    const opts = evalable.map((x) =>
      `<option value="${esc(x.name)}">${esc(x.name)}</option>`).join('');

    return (
      `<div class="dregg-pred__compose">` +
        `<p class="dregg-pred__note">Model an (old → new) 8-slot cell state, compose ` +
          `<code>Predicate</code> constraints, and see the real accept/reject. Slots are ` +
          `modeled as integers (the real field is a 32-byte <code>FieldElement</code>); ` +
          `the field-comparison fragment is mirrored faithfully from ` +
          `<code>StateConstraint::evaluate</code>.</p>` +
        slotRow('old', this._old, 'old') +
        slotRow('new', this._new, 'new') +
        `<div class="dregg-pred__overall-wrap">${overall}</div>` +
        `<ul class="dregg-pred__rows">${composedList}</ul>` +
        `<div class="dregg-pred__addform">` +
          `<select class="dregg-pred__add-kind">${opts}</select>` +
          `<input class="dregg-pred__add-a" type="number" placeholder="index/slot" value="0">` +
          `<input class="dregg-pred__add-b" type="number" placeholder="value/2nd" value="0">` +
          `<button class="dregg-pred__add">add constraint</button>` +
        `</div>` +
        `<p class="dregg-pred__note dregg-pred__note--dim">The two inputs map to the variant's ` +
          `first one or two scalar fields (index, then value/2nd-index). Set/vec-valued ` +
          `variants (AnyOf, AllowedTransitions, SumEqualsAcross) are best explored in the ` +
          `language reference; the simple field comparisons are fully interactive here.</p>` +
      `</div>`
    );
  }

  // Build a constraint object from the add-form's two scalar inputs, mapping
  // them onto the chosen variant's first one/two scalar fields.
  _mkConstraint(kind, a, b) {
    switch (kind) {
      case 'FieldEquals': return { kind, index: a, value: b };
      case 'FieldGte': return { kind, index: a, value: b };
      case 'FieldLte': return { kind, index: a, value: b };
      case 'FieldLteField': return { kind, left_index: a, right_index: b };
      case 'WriteOnce': return { kind, index: a };
      case 'Immutable': return { kind, index: a };
      case 'Monotonic': return { kind, index: a };
      case 'StrictMonotonic': return { kind, index: a };
      case 'MonotonicSequence': return { kind, seq_index: a };
      case 'FieldDelta': return { kind, index: a, delta: b };
      case 'FieldDeltaInRange': return { kind, index: a, min_delta: 0, max_delta: b };
      case 'SumEquals': return { kind, indices: [a], value: b };
      case 'SumEqualsAcross': return { kind, input_fields: [a], output_fields: [b] };
      case 'AllowedTransitions': return { kind, slot_index: a, allowed: [[0, b]] };
      case 'AnyOf': return { kind, variants: [{ kind: 'FieldEquals', index: a, value: b }] };
      default: return { kind, index: a, value: b };
    }
  }

  _wire() {
    this.querySelectorAll('.dregg-pred__tab').forEach((b) =>
      b.addEventListener('click', () => { this._tab = b.getAttribute('data-tab'); this._render(); }));

    this.querySelectorAll('.dregg-pred__slot').forEach((inp) =>
      inp.addEventListener('input', () => {
        const w = inp.getAttribute('data-which'); const i = +inp.getAttribute('data-idx');
        (w === 'old' ? this._old : this._new)[i] = asInt(inp.value);
        this._renderComposeOnly();
      }));

    const addBtn = this.querySelector('.dregg-pred__add');
    if (addBtn) addBtn.addEventListener('click', () => {
      const kind = this.querySelector('.dregg-pred__add-kind').value;
      const a = asInt(this.querySelector('.dregg-pred__add-a').value);
      const b = asInt(this.querySelector('.dregg-pred__add-b').value);
      this._composed.push(this._mkConstraint(kind, a, b));
      this._renderComposeOnly();
    });

    this.querySelectorAll('.dregg-pred__del').forEach((b) =>
      b.addEventListener('click', () => {
        this._composed.splice(+b.getAttribute('data-del'), 1);
        this._renderComposeOnly();
      }));
  }

  // Re-render only the compose body (keeps tab state; avoids losing input focus
  // on slot edits by replacing just the rows + verdict).
  _renderComposeOnly() {
    if (this._tab !== 'compose') return this._render();
    const body = this.querySelector('.dregg-pred__body');
    if (!body) return this._render();
    // Cheap: re-render the whole compose body. Focus is on the add-form, which
    // we leave intact by only swapping the rows + verdict regions.
    const rowsWrap = body.querySelector('.dregg-pred__rows');
    const overallWrap = body.querySelector('.dregg-pred__overall-wrap');
    if (!rowsWrap || !overallWrap) return this._render();
    const tmp = document.createElement('div');
    tmp.innerHTML = this._renderCompose();
    rowsWrap.replaceWith(tmp.querySelector('.dregg-pred__rows'));
    overallWrap.replaceWith(tmp.querySelector('.dregg-pred__overall-wrap'));
    // Re-wire the new delete buttons.
    this.querySelectorAll('.dregg-pred__del').forEach((b) =>
      b.addEventListener('click', () => {
        this._composed.splice(+b.getAttribute('data-del'), 1);
        this._renderComposeOnly();
      }));
  }
}

if (!customElements.get('dregg-predicate-explorer')) {
  customElements.define('dregg-predicate-explorer', DreggPredicateExplorer);
}

// --- styles (site palette only) --------------------------------------------
(function injectStyles() {
  if (document.getElementById('dregg-predicate-explorer-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-predicate-explorer-styles';
  s.textContent = `
.dregg-pred { font-family: var(--font-mono, ui-monospace, monospace); }
.dregg-pred__loading { color: var(--fg-dim); padding: 10px; }
.dregg-pred__title { display:flex; align-items:baseline; gap:10px; font-size:1.1rem; color:var(--fg); font-weight:600; }
.dregg-pred__count { font-size:0.8rem; color:var(--fg-dim); font-weight:normal; }
.dregg-pred__prov { font-size:0.78rem; color:var(--fg-dim); margin-top:4px; line-height:1.5; }
.dregg-pred__prov code { color:var(--fg); }
.dregg-pred__tabs { display:flex; gap:6px; margin:12px 0; border-bottom:1px solid var(--line); }
.dregg-pred__tab { padding:7px 14px; font:inherit; font-size:0.82rem; cursor:pointer; background:none; color:var(--fg-dim); border:0; border-bottom:2px solid transparent; }
.dregg-pred__tab:hover { color:var(--fg); }
.dregg-pred__tab.is-on { color:var(--fg); border-bottom-color:var(--accent,#5b8a5a); }
.dregg-pred__sec { margin-bottom:18px; }
.dregg-pred__sec h3 { font-size:0.86rem; color:var(--fg); margin:0 0 8px; text-transform:uppercase; letter-spacing:0.04em; }
.dregg-pred__item { border:1px solid var(--line); border-radius:6px; background:var(--bg-raised); padding:8px 10px; margin-bottom:6px; }
.dregg-pred__item.is-deeplinked { border-color:var(--accent,#5b8a5a); box-shadow:0 0 0 1px var(--accent,#5b8a5a); }
.dregg-pred__item-head { display:flex; align-items:center; gap:8px; }
.dregg-pred__kind { font-size:0.88rem; color:var(--fg); font-weight:600; }
.dregg-pred__tag { font-size:0.68rem; padding:1px 7px; border-radius:3px; }
.dregg-pred__tag--live { background:color-mix(in srgb,var(--accent,#5b8a5a) 22%,var(--bg-raised)); color:var(--accent-bright,#7db87b); }
.dregg-pred__tag--exec { background:color-mix(in srgb,#c8a050 18%,var(--bg-raised)); color:#d4b060; }
.dregg-pred__sem { font-size:0.82rem; color:var(--fg); line-height:1.5; margin:5px 0 6px; }
.dregg-pred__fields { display:flex; flex-wrap:wrap; gap:6px; }
.dregg-pred__field { display:inline-flex; gap:4px; align-items:baseline; padding:1px 7px; background:var(--bg); border:1px solid var(--line); border-radius:3px; font-size:0.76rem; }
.dregg-pred__fname { color:var(--fg); }
.dregg-pred__ftype { color:var(--fg-dim); font-size:0.72rem; }
.dregg-pred__note { font-size:0.8rem; color:var(--fg-dim); line-height:1.5; }
.dregg-pred__note code { color:var(--fg); }
.dregg-pred__note--dim { font-size:0.74rem; opacity:0.85; }
.dregg-pred__slots { display:flex; align-items:center; gap:5px; margin:8px 0; flex-wrap:wrap; }
.dregg-pred__slots-label { font-size:0.74rem; color:var(--fg-dim); min-width:30px; text-transform:uppercase; }
.dregg-pred__slot { width:52px; padding:5px; font:inherit; font-size:0.78rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; text-align:center; }
.dregg-pred__slot:focus { outline:none; border-color:var(--accent,#5b8a5a); }
.dregg-pred__overall-wrap { margin:10px 0; }
.dregg-pred__overall { display:inline-block; padding:5px 12px; border-radius:5px; font-size:0.82rem; font-weight:600; }
.dregg-pred__overall.is-ok { background:color-mix(in srgb,var(--accent,#5b8a5a) 25%,var(--bg-raised)); color:var(--accent-bright,#7db87b); }
.dregg-pred__overall.is-fail { background:color-mix(in srgb,#d4685c 22%,var(--bg-raised)); color:#e08878; }
.dregg-pred__overall.is-neutral { background:var(--bg-raised); color:var(--fg-dim); border:1px dashed var(--line); }
.dregg-pred__rows { list-style:none; padding:0; margin:8px 0; display:flex; flex-direction:column; gap:5px; }
.dregg-pred__row { display:flex; align-items:center; gap:10px; flex-wrap:wrap; padding:6px 10px; border:1px solid var(--line); border-radius:5px; background:var(--bg-raised); font-size:0.8rem; }
.dregg-pred__row.is-ok { border-left:3px solid var(--accent,#5b8a5a); }
.dregg-pred__row.is-fail { border-left:3px solid #d4685c; }
.dregg-pred__row.is-deferred { border-left:3px solid #c8a050; }
.dregg-pred__row code { color:var(--fg); }
.dregg-pred__verdict { font-size:0.72rem; font-weight:600; padding:1px 7px; border-radius:3px; background:var(--bg); }
.dregg-pred__row.is-ok .dregg-pred__verdict { color:var(--accent-bright,#7db87b); }
.dregg-pred__row.is-fail .dregg-pred__verdict { color:#e08878; }
.dregg-pred__row.is-deferred .dregg-pred__verdict { color:#d4b060; }
.dregg-pred__why { color:var(--fg-dim); font-size:0.74rem; flex:1; min-width:120px; }
.dregg-pred__del { margin-left:auto; background:none; border:0; color:var(--fg-dim); cursor:pointer; font-size:0.8rem; }
.dregg-pred__del:hover { color:#e08878; }
.dregg-pred__empty { color:var(--fg-dim); font-style:italic; padding:6px 10px; border:1px dashed var(--line); border-radius:5px; }
.dregg-pred__addform { display:flex; gap:6px; flex-wrap:wrap; margin-top:8px; }
.dregg-pred__addform select, .dregg-pred__addform input { padding:6px 8px; font:inherit; font-size:0.78rem; background:var(--bg-raised); color:var(--fg); border:1px solid var(--line); border-radius:4px; }
.dregg-pred__add-a, .dregg-pred__add-b { width:96px; }
.dregg-pred__add { cursor:pointer; background:color-mix(in srgb,var(--accent,#5b8a5a) 18%,var(--bg-raised)); color:var(--fg); }
.dregg-pred__add:hover { border-color:var(--accent,#5b8a5a); }
`;
  document.head.appendChild(s);
})();
