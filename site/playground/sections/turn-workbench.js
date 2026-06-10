/**
 * Turn Workbench — the verb-first turn surface (dregg3 framing).
 *
 * The kernel is being reduced to EIGHT verbs (docs/DREGG3.md §2.3:
 * create · write · move · grant · revoke · shield/unshield · lifecycle);
 * everything else among the legacy effects is a cell-program pattern
 * (factory + Pred + these verbs). This section drives the verbs against the
 * REAL in-browser wasm runtime (the same `dregg-turn` TurnExecutor crate the
 * node runs) and, for the thin-HTTP-submittable fragment, against a live
 * devnet node:
 *
 *   1. VERB PALETTE — the eight verbs, each with its subsumption note and an
 *      honest status: turn-composable here, drivable by a dedicated runtime
 *      call, or out of this workbench's scope.
 *   2. EXPLAIN BEFORE YOU RUN — every staged effect is explained from the
 *      GENERATED catalogs (ontology-catalog.generated.json: the verified-Lean
 *      semantics, required authority facet, wire mnemonic) before anything is
 *      signed or executed. Anti-blind-signing from data, not hardcoded copy.
 *   3. RUN LOCALLY — execute the staged turn via wasm `execute_turn` (real
 *      executor, real receipt: turn_hash + pre/post state commitments +
 *      computrons), then optionally `prove_turn` (a real EffectVM STARK).
 *   4. SUBMIT TO DEVNET — POST the thin-HTTP equivalent to a node's
 *      /api/turns/submit and show the node's honest verdict. Effects with no
 *      thin-HTTP projection are labeled, never silently dropped.
 *
 * WASM API GAPS (documented in the panel below, not stubbed):
 *   - `sdk/src/explain.rs` (explain_turn / explain_action / explain_effect)
 *     has no wasm-bindgen export; the explain panel uses the generated
 *     catalogs instead and says so.
 *   - No browser blocklace-sync binding (wasm/src/bindings.rs:1545 note) —
 *     live consensus state comes via the node HTTP API only.
 *   - No `get_factory_descriptor(vk)` lookup binding (factory-descriptor.js
 *     renders deploy results / supplied data only).
 */

import { getWasm } from '../playground.js';

const ONTOLOGY_URL = '/_includes/studio/ontology-catalog.generated.json';
const SUBMIT_SCHEMA_URL = '/_includes/studio/submit-schema.generated.json';
const NODE_URL_KEY = 'dregg_node_url';
const NODE_TOKEN_KEY = 'dregg_node_token';

function esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function defaultNodeUrl() {
  try {
    const { protocol, hostname, origin } = window.location;
    const isLocal = hostname === 'localhost' || hostname === '127.0.0.1' || hostname === '[::1]';
    if ((protocol === 'http:' || protocol === 'https:') && !isLocal) return origin;
  } catch {}
  return 'http://localhost:8420';
}

// The eight dregg3 verbs (docs/DREGG3.md §2.3) with their subsumption notes
// and what THIS workbench can drive tonight. `effects` are turn-composable
// staged effects (wasm execute_turn RawAction kinds); `action` is a dedicated
// runtime-call mini-action.
const VERBS = [
  {
    verb: 'create', subsumes: 'CreateCell · CreateCellFromFactory · spawn',
    effects: [], action: 'create_agent',
    note: 'drivable here: mint a new agent cell into the local runtime (create_agent). Factory-born creation lives in the Studio factory tab + Factories section.',
  },
  {
    verb: 'write', subsumes: 'SetField · EmitEvent · nonce-prologue',
    effects: ['set_field', 'emit_event', 'increment_nonce'], action: null,
    note: 'turn-composable here. Events are observability writes; the nonce bump is turn prologue.',
  },
  {
    verb: 'move', subsumes: 'Transfer · mint/burn = the issuer moving from/to its own well',
    effects: ['transfer'], action: null,
    note: 'turn-composable here. Conservation (Σ per asset = 0) is a kernel theorem, not a convention.',
  },
  {
    verb: 'grant', subsumes: 'GrantCapability · introduce · delegate-attenuate',
    effects: ['grant'], action: null,
    note: 'turn-composable here (local runtime only — no thin-HTTP projection; the node path is the typed SDK signed envelope).',
  },
  {
    verb: 'revoke', subsumes: 'RevokeCapability · revocation channels · epoch bumps',
    effects: [], action: 'revoke_slot',
    note: 'drivable here: revoke a held capability slot via the dedicated runtime call.',
  },
  {
    verb: 'shield', subsumes: 'NoteCreate (value → private commitment)',
    effects: [], action: 'shield_note',
    note: 'drivable here: create a private note (real Pedersen commitment + nullifier machinery in wasm).',
  },
  {
    verb: 'unshield', subsumes: 'NoteSpend (commitment → value, nullifier inserted)',
    effects: [], action: 'unshield_note',
    note: 'drivable here: spend a note via the dedicated runtime call (no-double-spend = freshness guarantee D).',
  },
  {
    verb: 'lifecycle', subsumes: 'seal/unseal · destroy · sovereign exit · epoch advance',
    effects: [], action: 'advance_height',
    note: 'partially drivable here: advance the local chain height (+1). Seal/destroy/sovereign-exit are exercised in the Sovereign section.',
  },
];

// Staged-effect field forms (the wasm execute_turn RawAction shapes —
// bindings.rs parse_effects; value_hex is a 64-hex field element).
const EFFECT_FORMS = {
  set_field: {
    fields: { index: { ph: 'slot 0..7', def: '0' }, value_hex: { ph: '64-hex or decimal', def: '1' } },
    toRaw: (f) => ({ type: 'set_field', index: Number(f.index || 0), value_hex: toHex64(f.value_hex) }),
    submitKind: 'set_field',
    toSubmit: (f) => ({ kind: 'set_field', index: Number(f.index || 0), value: String(f.value_hex || '0') }),
  },
  emit_event: {
    fields: { topic: { ph: 'topic name (hashed via symbol())', def: 'demo' } },
    toRaw: (f) => ({ type: 'emit_event', topic: String(f.topic || 'demo'), data_hex: [] }),
    submitKind: 'emit_event',
    toSubmit: (f) => ({ kind: 'emit_event', topic: String(f.topic || 'demo') }),
  },
  increment_nonce: {
    fields: {},
    toRaw: () => ({ type: 'increment_nonce' }),
    submitKind: 'increment_nonce',
    toSubmit: () => ({ kind: 'increment_nonce' }),
  },
  transfer: {
    fields: { to: { ph: 'recipient (pick agent below or 64-hex)', def: '' }, amount: { ph: 'amount', def: '10' } },
    toRaw: (f) => ({ type: 'transfer', to: f.to, amount: Number(f.amount || 0) }),
    submitKind: 'transfer',
    toSubmit: (f) => ({ kind: 'transfer', to: f.to, amount: Number(f.amount || 0) }),
  },
  grant: {
    fields: { to: { ph: 'grantee cell (64-hex)', def: '' }, permissions: { ph: 'none|signature|proof|either', def: 'signature' } },
    toRaw: (f) => ({ type: 'grant', to: f.to, permissions: f.permissions || 'signature' }),
    submitKind: null, // no thin-HTTP projection — labeled, not dropped
    toSubmit: null,
  },
};

// kind → verified-Lean ontology ctor (for the explain panel).
const KIND_TO_CTOR = {
  set_field: 'setFieldA',
  transfer: 'balanceA',
  emit_event: 'emitEventA',
  increment_nonce: 'incrementNonceA',
  grant: 'introduceA',
};

function toHex64(v) {
  const t = String(v ?? '').trim();
  if (/^[0-9a-fA-F]{64}$/.test(t)) return t.toLowerCase();
  let n;
  try { n = BigInt(t || '0'); } catch { n = 0n; }
  return n.toString(16).padStart(64, '0');
}

// ---------------------------------------------------------------------------
// Section state
// ---------------------------------------------------------------------------
let wasm = null;
let handle = null;
let agents = [];           // { name, cell_id }
let staged = [];           // { kind, fields }
let log = [];              // activity log entries (real call results)
let lastRun = null;        // last execute_turn result
let lastProof = null;      // last prove_turn result
let lastSubmit = null;     // last node submit result
let ontology = null;       // generated catalogs
let activeVerb = 'write';

function logLine(kind, text) {
  log.unshift({ kind, text, at: new Date().toLocaleTimeString() });
  log = log.slice(0, 30);
}

export function initTurnWorkbench(wasmExports) {
  const section = document.getElementById('section-turn-workbench');
  if (!section) return;
  wasm = wasmExports;

  Promise.all([
    fetch(ONTOLOGY_URL).then((r) => (r.ok ? r.json() : null)),
    fetch(SUBMIT_SCHEMA_URL).then((r) => (r.ok ? r.json() : null)),
  ]).then(([ont]) => { ontology = ont; render(section); }).catch(() => render(section));

  render(section);
}

function ensureRuntime() {
  if (!wasm) return false;
  if (handle === null) {
    handle = wasm.create_runtime();
    // Genesis (alice) funds subsequent agents' minting turns, so it needs
    // headroom: minting bob with 1000 costs ~2000 from genesis.
    for (const [name, balance] of [['alice', 10000n], ['bob', 1000n]]) {
      try {
        const r = wasm.create_agent(handle, name, balance);
        agents.push({ name, cell_id: extractCellId(r) });
      } catch (e) {
        logLine('err', `create_agent(${name}) failed: ${e.message || e}`);
      }
    }
    logLine('ok', `local runtime ready — agents: ${agents.map((a) => `${a.name}=${String(a.cell_id).slice(0, 8)}…`).join(', ')}`);
  }
  return true;
}

function extractCellId(r) {
  if (!r || typeof r !== 'object') return '';
  for (const k of ['cell_id', 'cellId', 'agent_cell_id', 'id']) if (r[k]) return r[k];
  return '';
}

function explainFor(kind) {
  const ctor = KIND_TO_CTOR[kind];
  const eff = ontology?.effects?.find((e) => e.ctor === ctor);
  if (!eff) {
    return { semantics: `no ontology mapping for "${kind}" — explained only by its kernel Effect name`, facet: null, wire: null, ctor };
  }
  return { semantics: eff.semantics, facet: eff.facet, wire: eff.wire, ctor: eff.ctor };
}

// ---------------------------------------------------------------------------
// Actions (all REAL wasm / network calls)
// ---------------------------------------------------------------------------

function runLocal(section) {
  if (!ensureRuntime()) return;
  const actions = [];
  for (const s of staged) {
    const form = EFFECT_FORMS[s.kind];
    try { actions.push(form.toRaw(s.fields)); }
    catch (e) { logLine('err', `${s.kind}: ${e.message || e}`); return; }
  }
  try {
    // Fee doubles as the computron budget (a small turn uses ~300/effect).
    lastRun = wasm.execute_turn(handle, 0, JSON.stringify(actions), 2000n);
    lastProof = null;
    const status = lastRun.status || 'unknown';
    logLine(status === 'committed' ? 'ok' : 'err',
      `execute_turn → ${status}${lastRun.turn_hash ? ` · ${String(lastRun.turn_hash).slice(0, 12)}…` : ''}${lastRun.error ? ` · ${lastRun.error}` : ''}`);
  } catch (e) {
    lastRun = { status: 'error', error: String(e.message || e) };
    logLine('err', `execute_turn threw: ${e.message || e}`);
  }
  render(section);
}

function proveLast(section) {
  if (!lastRun?.turn_hash) return;
  const btn = section.querySelector('#twb-prove');
  if (btn) { btn.disabled = true; btn.textContent = 'proving (real STARK — may take a moment)…'; }
  setTimeout(() => {
    try {
      lastProof = wasm.prove_turn(handle, lastRun.turn_hash);
      logLine('ok', `prove_turn → ${lastProof.kind} · ${lastProof.proof_size_bytes} bytes · ${lastProof.trace_rows} rows`);
    } catch (e) {
      lastProof = { error: String(e.message || e) };
      logLine('err', `prove_turn failed: ${e.message || e}`);
    }
    render(section);
  }, 30);
}

async function submitToNode(section) {
  const url = (localStorage.getItem(NODE_URL_KEY) || defaultNodeUrl()).replace(/\/+$/, '');
  const token = localStorage.getItem(NODE_TOKEN_KEY) || '';
  const submittable = staged.filter((s) => EFFECT_FORMS[s.kind].toSubmit);
  const skipped = staged.filter((s) => !EFFECT_FORMS[s.kind].toSubmit).map((s) => s.kind);
  const body = {
    agent: '00'.repeat(32),
    nonce: 0,
    fee: 500,
    actions: [{ effects: submittable.map((s) => EFFECT_FORMS[s.kind].toSubmit(s.fields)) }],
  };
  lastSubmit = { pending: true };
  render(section);
  try {
    const res = await fetch(`${url}/api/turns/submit`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json', Accept: 'application/json',
        ...(token ? { Authorization: `Bearer ${token}` } : {}),
      },
      body: JSON.stringify(body),
    });
    let payload = null;
    try { payload = await res.json(); } catch {}
    lastSubmit = { http: res.status, ok: res.ok, payload, skipped, url };
    logLine(res.ok ? 'ok' : 'err', `node submit → HTTP ${res.status}${payload?.turn_hash ? ` · ${String(payload.turn_hash).slice(0, 12)}…` : ''}`);
  } catch (e) {
    lastSubmit = { http: 0, error: String(e.message || e), skipped, url };
    logLine('err', `node unreachable: ${e.message || e}`);
  }
  render(section);
}

function runVerbAction(section, action) {
  if (!ensureRuntime()) return;
  try {
    if (action === 'create_agent') {
      const name = `agent-${agents.length}`;
      const r = wasm.create_agent(handle, name, 500n);
      agents.push({ name, cell_id: extractCellId(r) });
      logLine('ok', `create (verb): minted ${name} = ${String(extractCellId(r)).slice(0, 12)}…`);
    } else if (action === 'revoke_slot') {
      const r = wasm.revoke_capability(handle, 0, 0);
      logLine('ok', `revoke (verb): revoke_capability(agent 0, slot 0) → ${JSON.stringify(r).slice(0, 80)}`);
    } else if (action === 'shield_note') {
      const r = wasm.create_note(handle, 0, 42n, 0n);
      logLine('ok', `shield (verb): create_note(42) → commitment ${String(r.commitment || '').slice(0, 14)}…`);
    } else if (action === 'unshield_note') {
      const r = wasm.spend_note(handle, 0, 42n, 0n);
      logLine('ok', `unshield (verb): spend_note(42) → nullifier ${String(r.nullifier || '').slice(0, 14)}…`);
    } else if (action === 'advance_height') {
      const r = wasm.advance_height(handle, 1n);
      logLine('ok', `lifecycle (verb): advance_height(+1) → height ${r.new_height ?? r.height ?? '?'}`);
    }
  } catch (e) {
    logLine('err', `${action} failed: ${e.message || e}`);
  }
  render(section);
}

// ---------------------------------------------------------------------------
// Render
// ---------------------------------------------------------------------------

function render(section) {
  const wasmOk = !!wasm;

  const verbCards = VERBS.map((v) => {
    const on = activeVerb === v.verb;
    const drivable = v.effects.length || v.action;
    return `<button class="twb-verb${on ? ' is-on' : ''}${drivable ? '' : ' is-passive'}" data-verb="${v.verb}" title="${esc(v.note)}">
      <span class="twb-verb__name">${esc(v.verb)}</span>
      <span class="twb-verb__sub">${esc(v.subsumes)}</span>
      <span class="twb-verb__status">${v.effects.length ? 'turn-composable' : (v.action ? 'runtime call' : 'see other sections')}</span>
    </button>`;
  }).join('');

  const active = VERBS.find((v) => v.verb === activeVerb) || VERBS[1];
  const effButtons = active.effects.map((k) =>
    `<button class="pg-btn pg-btn--primary pg-btn--sm" data-stage="${k}">+ stage ${k}</button>`).join(' ');
  const actBtn = active.action
    ? `<button class="pg-btn pg-btn--accent pg-btn--sm" data-verbact="${active.action}"${wasmOk ? '' : ' disabled'}>run ${esc(active.verb)} now (dedicated call)</button>`
    : '';

  const stagedRows = staged.length ? staged.map((s, i) => {
    const ex = explainFor(s.kind);
    const form = EFFECT_FORMS[s.kind];
    const inputs = Object.entries(form.fields).map(([name, spec]) =>
      `<label class="twb-f"><span>${esc(name)}</span><input data-si="${i}" data-sf="${esc(name)}" value="${esc(s.fields[name] ?? spec.def)}" placeholder="${esc(spec.ph)}"></label>`).join('');
    return `<li class="twb-staged">
      <div class="twb-staged__head">
        <code>${esc(s.kind)}</code>
        ${ex.wire ? `<span class="twb-pill" title="wire mnemonic (Dregg2/Exec/FFI.lean)">${esc(ex.wire)}</span>` : ''}
        ${ex.facet ? `<span class="twb-pill twb-pill--facet" title="required authority facet (requiredFacetA)">${esc(ex.facet)}</span>` : ''}
        ${form.toSubmit ? '' : `<span class="twb-pill twb-pill--warn" title="no TurnEffectSpec projection in node/src/api.rs — node path is the typed SDK signed envelope">local-only</span>`}
        <button class="twb-del" data-unstage="${i}">✕</button>
      </div>
      <div class="twb-staged__explain" title="from ontology-catalog.generated.json (verified Lean FullActionA doc-comments)">
        <strong>${esc(ex.ctor || s.kind)}</strong>: ${esc(ex.semantics)}
      </div>
      <div class="twb-staged__fields">${inputs || '<span class="twb-dim">(no fields)</span>'}</div>
    </li>`;
  }).join('') : '<li class="twb-empty">nothing staged — pick a verb above and stage an effect.</li>';

  const agentList = agents.length
    ? `<div class="twb-agents">local agents: ${agents.map((a) =>
        `<code class="twb-agent" data-cell="${esc(a.cell_id)}" title="click to copy into the focused 'to' field">${esc(a.name)}=${esc(String(a.cell_id).slice(0, 10))}…</code>`).join(' ')}</div>`
    : '';

  const runBlock = lastRun ? `
    <div class="twb-result ${lastRun.status === 'committed' ? 'is-ok' : 'is-fail'}">
      <div><strong>${esc(String(lastRun.status || '').toUpperCase())}</strong> <span class="twb-dim">(in-browser wasm executor — the real dregg-turn TurnExecutor)</span></div>
      ${lastRun.turn_hash ? `<div>turn <code>${esc(lastRun.turn_hash)}</code></div>` : ''}
      ${lastRun.pre_state_hash ? `<div>pre-state <code>${esc(String(lastRun.pre_state_hash).slice(0, 20))}…</code> → post-state <code>${esc(String(lastRun.post_state_hash).slice(0, 20))}…</code> <span class="twb-dim">(the receipt binds the whole post-state)</span></div>` : ''}
      ${lastRun.computrons_used != null ? `<div>${esc(String(lastRun.computrons_used))} computrons</div>` : ''}
      ${lastRun.error ? `<div class="twb-err">${esc(lastRun.error)}</div>` : ''}
      ${lastRun.status === 'committed' ? `<button class="pg-btn pg-btn--accent pg-btn--sm" id="twb-prove">prove this turn (real EffectVM STARK)</button>` : ''}
      ${lastProof ? (lastProof.error
        ? `<div class="twb-err">prove_turn: ${esc(lastProof.error)}</div>`
        : `<div class="twb-proof">proof: <strong>${esc(lastProof.kind)}</strong> · ${esc(String(lastProof.proof_size_bytes))} bytes · ${esc(String(lastProof.trace_rows))} trace rows · net Δ ${esc(String(lastProof.net_delta))} <span class="twb-dim">(proved + self-verified in wasm before being reported)</span></div>`) : ''}
    </div>` : '';

  const submitBlock = lastSubmit ? (lastSubmit.pending
    ? `<div class="twb-result">submitting…</div>`
    : `<div class="twb-result ${lastSubmit.ok && lastSubmit.payload?.accepted ? 'is-ok' : 'is-fail'}">
        <div><strong>${lastSubmit.http === 0 ? 'NODE UNREACHABLE' : (lastSubmit.payload?.accepted ? 'ACCEPTED' : 'REJECTED')}</strong>
          <span class="twb-dim">HTTP ${esc(String(lastSubmit.http))} · ${esc(lastSubmit.url || '')}</span></div>
        ${lastSubmit.payload?.turn_hash ? `<div>turn <code>${esc(lastSubmit.payload.turn_hash)}</code> — <a href="/explorer/?at=dregg://receipt/${esc(lastSubmit.payload.turn_hash)}" target="_blank" rel="noreferrer">open in the explorer</a></div>` : ''}
        ${lastSubmit.payload?.proof_status ? `<div>proof status: <code>${esc(lastSubmit.payload.proof_status)}</code></div>` : ''}
        ${lastSubmit.payload?.error ? `<div class="twb-err">${esc(lastSubmit.payload.error)}</div>` : ''}
        ${lastSubmit.error ? `<div class="twb-err">${esc(lastSubmit.error)} — check the node URL (settings shared with the Studio composer) and CORS.</div>` : ''}
        ${lastSubmit.skipped?.length ? `<div class="twb-warn">not submitted (no thin-HTTP projection, labeled local-only): ${esc(lastSubmit.skipped.join(', '))}</div>` : ''}
      </div>`) : '';

  const logRows = log.map((l) =>
    `<div class="twb-log__row twb-log__row--${l.kind}"><span class="twb-dim">${esc(l.at)}</span> ${esc(l.text)}</div>`).join('');

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Turn Workbench</h2>
      <p>
        Speak the kernel's <strong>eight verbs</strong> (docs/DREGG3.md §2.3) instead of 50 effect
        names: stage a turn, read what each effect <em>means</em> (from the verified-Lean catalog)
        <strong>before</strong> running it, execute it on the real in-browser executor, prove it,
        or submit the thin-HTTP fragment to a devnet node. ${wasmOk ? '' : '<strong>wasm failed to load — local runs are unavailable; node submit still works.</strong>'}
      </p>
    </div>

    <div class="twb-verbs">${verbCards}</div>
    <div class="twb-verbnote"><strong>${esc(active.verb)}</strong> — ${esc(active.note)}
      <a class="twb-verblink" data-dregg-uri="dregg://verb/${esc(active.verb === 'shield' || active.verb === 'unshield' ? 'shieldUnshield' : active.verb)}"
         href="/learn/concepts/substances.html#verb-${esc(active.verb === 'shield' || active.verb === 'unshield' ? 'shieldUnshield' : active.verb)}"
         title="open this verb's row in the substances rung (generated from VerbRegistry.lean)">what is ${esc(active.verb)}? →</a></div>
    <div class="twb-verbactions">${effButtons}${actBtn ? ' ' + actBtn : ''}</div>

    ${agentList}

    <div class="twb-cols">
      <div class="twb-col">
        <h3 class="twb-h">Staged turn <span class="twb-dim">(${staged.length} effect${staged.length === 1 ? '' : 's'})</span></h3>
        <ul class="twb-stagedlist">${stagedRows}</ul>
        <div class="twb-runrow">
          <button class="pg-btn pg-btn--primary" id="twb-run"${staged.length && wasmOk ? '' : ' disabled'}>Run locally (wasm executor)</button>
          <button class="pg-btn pg-btn--ghost" id="twb-submit"${staged.some((s) => EFFECT_FORMS[s.kind].toSubmit) ? '' : ' disabled'}>Submit thin-HTTP fragment to node</button>
          <button class="pg-btn pg-btn--ghost pg-btn--sm" id="twb-clear"${staged.length ? '' : ' disabled'}>clear</button>
        </div>
        ${runBlock}
        ${submitBlock}
      </div>

      <div class="twb-col">
        <h3 class="twb-h">Activity <span class="twb-dim">(real call results)</span></h3>
        <div class="twb-log">${logRows || '<div class="twb-dim">no calls yet</div>'}</div>

        <details class="twb-gaps">
          <summary>WASM API surface — what exists, what's missing (honest inventory)</summary>
          <ul>
            <li><strong>exists:</strong> <code>execute_turn</code> (real TurnExecutor: set_field / transfer / emit_event / increment_nonce / grant), <code>prove_turn</code> (real EffectVM STARK), <code>create_agent</code>/<code>create_cell</code>, <code>create_note</code>/<code>spend_note</code>, <code>revoke_capability</code>/<code>trip_revocation_channel</code>, <code>advance_height</code>, <code>deploy_factory_descriptor</code>, <code>sign_turn_v3</code>/<code>build_committed_turn</code> (canonical v3 signing for node submit-signed).</li>
            <li><strong>missing:</strong> <code>sdk/src/explain.rs</code> (<code>explain_turn</code> / <code>explain_action</code> / <code>explain_effect</code>) has no wasm-bindgen export — the explain text here comes from the generated Lean catalog instead (labeled per effect).</li>
            <li><strong>missing:</strong> browser blocklace sync (<code>wasm/src/bindings.rs</code> STARBRIDGE FOLLOWUP-09 note) — devnet consensus state is read over the node HTTP API, not synced into the browser.</li>
            <li><strong>missing:</strong> <code>get_factory_descriptor(vk)</code> registry lookup — factory inspectors render deploy results / supplied JSON only.</li>
          </ul>
        </details>
      </div>
    </div>
  `;

  wire(section);
}

function wire(section) {
  section.querySelectorAll('[data-verb]').forEach((b) =>
    b.addEventListener('click', () => { activeVerb = b.getAttribute('data-verb'); render(section); }));

  section.querySelectorAll('[data-stage]').forEach((b) =>
    b.addEventListener('click', () => {
      const kind = b.getAttribute('data-stage');
      const form = EFFECT_FORMS[kind];
      const fields = {};
      for (const [name, spec] of Object.entries(form.fields)) fields[name] = spec.def;
      // default transfer target: the other local agent, if present
      if (kind === 'transfer' && agents[1]) fields.to = agents[1].cell_id;
      if (kind === 'grant' && agents[1]) fields.to = agents[1].cell_id;
      staged.push({ kind, fields });
      render(section);
    }));

  section.querySelectorAll('[data-unstage]').forEach((b) =>
    b.addEventListener('click', () => { staged.splice(+b.getAttribute('data-unstage'), 1); render(section); }));

  section.querySelectorAll('[data-si]').forEach((inp) =>
    inp.addEventListener('input', () => {
      const s = staged[+inp.getAttribute('data-si')];
      if (s) s.fields[inp.getAttribute('data-sf')] = inp.value;
    }));

  section.querySelectorAll('[data-verbact]').forEach((b) =>
    b.addEventListener('click', () => runVerbAction(section, b.getAttribute('data-verbact'))));

  section.querySelectorAll('.twb-agent').forEach((c) =>
    c.addEventListener('click', () => {
      navigator.clipboard?.writeText(c.getAttribute('data-cell') || '').catch(() => {});
    }));

  section.querySelector('#twb-run')?.addEventListener('click', () => runLocal(section));
  section.querySelector('#twb-prove')?.addEventListener('click', () => proveLast(section));
  section.querySelector('#twb-submit')?.addEventListener('click', () => submitToNode(section));
  section.querySelector('#twb-clear')?.addEventListener('click', () => { staged = []; lastRun = null; lastProof = null; render(section); });
}

// --- styles ------------------------------------------------------------------
(function injectStyles() {
  if (document.getElementById('twb-styles')) return;
  const s = document.createElement('style');
  s.id = 'twb-styles';
  s.textContent = `
.twb-verbs { display:grid; grid-template-columns:repeat(auto-fill,minmax(150px,1fr)); gap:8px; margin:10px 0; }
.twb-verb { display:flex; flex-direction:column; gap:3px; text-align:left; cursor:pointer; font:inherit; padding:9px 11px; border:1px solid var(--line,#2a3530); border-radius:7px; background:var(--bg-raised,#141a17); color:var(--text,#e8f0e8); }
.twb-verb:hover { border-color:var(--accent,#5b8a5a); }
.twb-verb.is-on { border-color:var(--accent,#5b8a5a); outline:1px solid var(--accent,#5b8a5a); }
.twb-verb.is-passive { opacity:0.75; }
.twb-verb__name { font-weight:700; font-size:0.92rem; }
.twb-verb__sub { font-size:0.64rem; color:var(--text-dim,#8a958f); line-height:1.35; }
.twb-verb__status { font-size:0.6rem; text-transform:uppercase; letter-spacing:0.04em; color:var(--accent-bright,#7db87b); }
.twb-verb.is-passive .twb-verb__status { color:var(--text-dim,#8a958f); }
.twb-verbnote { font-size:0.78rem; color:var(--text-dim,#8a958f); margin:4px 0 8px; line-height:1.5; }
.twb-verblink { margin-left:8px; color:var(--accent-bright,#8fddff); text-decoration:none; border-bottom:1px dotted currentColor; font-size:0.74rem; white-space:nowrap; }
.twb-verbactions { display:flex; gap:8px; flex-wrap:wrap; margin-bottom:10px; }
.twb-agents { font-size:0.74rem; color:var(--text-dim,#8a958f); margin:6px 0 10px; }
.twb-agent { cursor:copy; border:1px solid var(--line,#2a3530); border-radius:4px; padding:1px 6px; margin-right:4px; }
.twb-cols { display:grid; grid-template-columns:minmax(0,3fr) minmax(0,2fr); gap:14px; align-items:start; }
@media (max-width: 900px) { .twb-cols { grid-template-columns:1fr; } }
.twb-h { font-size:0.84rem; margin:0 0 8px; }
.twb-stagedlist { list-style:none; padding:0; margin:0 0 10px; display:flex; flex-direction:column; gap:7px; }
.twb-staged { border:1px solid var(--line,#2a3530); border-left:3px solid var(--accent,#5b8a5a); border-radius:6px; background:var(--bg-raised,#141a17); padding:8px 10px; }
.twb-staged__head { display:flex; align-items:center; gap:7px; flex-wrap:wrap; }
.twb-staged__head > code { font-weight:700; }
.twb-pill { font-size:0.62rem; border:1px solid var(--line,#2a3530); border-radius:9px; padding:1px 7px; color:var(--text-dim,#8a958f); cursor:help; }
.twb-pill--facet { border-color:#64a8c8; color:#8fcde6; }
.twb-pill--warn { border-color:#c9a84c; color:#f2d06b; }
.twb-del { margin-left:auto; background:none; border:0; color:var(--text-dim,#8a958f); cursor:pointer; }
.twb-del:hover { color:#e08878; }
.twb-staged__explain { font-size:0.72rem; color:var(--text-dim,#8a958f); margin-top:5px; line-height:1.45; cursor:help; }
.twb-staged__explain strong { color:var(--text,#e8f0e8); }
.twb-staged__fields { display:flex; gap:10px; flex-wrap:wrap; margin-top:6px; }
.twb-f { display:flex; flex-direction:column; gap:2px; font-size:0.68rem; color:var(--text-dim,#8a958f); }
.twb-f input { padding:5px 7px; font:inherit; font-size:0.74rem; background:var(--bg,#0a0f0d); color:var(--text,#e8f0e8); border:1px solid var(--line,#2a3530); border-radius:4px; min-width:200px; }
.twb-empty { color:var(--text-dim,#8a958f); font-style:italic; padding:8px 10px; border:1px dashed var(--line,#2a3530); border-radius:5px; }
.twb-runrow { display:flex; gap:8px; flex-wrap:wrap; margin:8px 0; }
.twb-result { border:1px solid var(--line,#2a3530); border-left:3px solid #c9a84c; border-radius:6px; background:var(--bg-raised,#141a17); padding:9px 11px; font-size:0.78rem; margin-top:8px; display:flex; flex-direction:column; gap:4px; }
.twb-result.is-ok { border-left-color:#62c47a; }
.twb-result.is-fail { border-left-color:#d4685c; }
.twb-result code { word-break:break-all; }
.twb-err { color:#f18b7d; }
.twb-warn { color:#f2d06b; font-size:0.72rem; }
.twb-proof { color:#8ee6a2; }
.twb-dim { color:var(--text-dim,#8a958f); font-size:0.92em; }
.twb-log { border:1px solid var(--line,#2a3530); border-radius:6px; background:var(--bg,#0a0f0d); padding:8px 10px; font-size:0.7rem; max-height:260px; overflow-y:auto; display:flex; flex-direction:column; gap:4px; }
.twb-log__row--err { color:#f18b7d; }
.twb-log__row--ok { color:var(--text,#e8f0e8); }
.twb-gaps { margin-top:12px; font-size:0.74rem; color:var(--text-dim,#8a958f); }
.twb-gaps summary { cursor:pointer; }
.twb-gaps ul { padding-left:18px; display:grid; gap:6px; line-height:1.5; margin:8px 0 0; }
.twb-gaps code { color:var(--text,#e8f0e8); }
`;
  document.head.appendChild(s);
})();
