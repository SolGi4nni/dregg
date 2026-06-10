/**
 * Polis inspectors — governance cells made legible in the image.
 *
 *   <dregg-council uri="dregg://council/<cell-id>">             M-of-N proposal cell
 *   <dregg-constitution uri="dregg://constitution/<cell-id>">   per-version parameter cell
 *   <dregg-mandate uri="dregg://mandate/<cell-id>">             budgeted worker mandate
 *   <dregg-amendment-ceremony uri="dregg://amendment-ceremony/<cell-id>[/old/<id>/new/<id>]">
 *
 * Decode logic is the PURE module `../polis-decode.js` — the browser port of
 * `starbridge_polis::council::inspect_council` (the same decoder behind the
 * CLI `dregg polis council` and Discord `/council-status`) plus the slot
 * schemas of `starbridge-apps/polis/src/lib.rs`. Charter terms (threshold M,
 * member count N, pinned literals, the cooling gate) are READ from the cell's
 * served program view or a descriptor's constraints — never hand-set.
 *
 * Every element also supports `mode="descriptor"` with `data-descriptor`
 * (a FactoryDescriptor JSON): the FACTORY view — the machine + the terms a
 * cell born from it lives under, current state = the birth state, honestly
 * labeled as not-a-live-cell. The Studio's worked examples open this view.
 *
 * HONESTY notes baked in:
 *   * A live node program view has NO projection for `AffineLe`/`MemberOf`
 *     (StateConstraintView gap) — so the threshold M is shown from data only
 *     when a descriptor carries it; otherwise the gap is stated, not papered.
 *   * Slot values come from the cell's CURRENT fields; the machine's monotone
 *     design is what makes the ceremony ladder a sound readback (each rung's
 *     "done" is witnessed by a monotone slot, not inferred from history).
 */

import { parseRef } from '../uri.js';
import { findRuntime } from '../context.js';
import {
  InspectorBase, renderParseError, shortHex, dreggCodeLink, emptyState,
} from './_base.js';
import {
  COUNCIL, CONSTITUTION, MANDATE,
  classifyConstraints, constraintsOf, inspectCouncil, inspectConstitution,
  inspectMandate, ceremonyLadder, fieldHex, fieldIsZero,
} from '../polis-decode.js';
import { surfaceHref, rungRef } from '../resolver.js';

// --- base: tolerate descriptor-mode mounts outside <dregg-app> ---------------

function uiReady() {
  return new Promise((resolve) => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', (e) => resolve(e.detail), { once: true });
  });
}

class PolisBase extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode', 'data-descriptor']; }
  async connectedCallback() {
    const token = ++this._connectToken;
    const api = await uiReady();
    let runtime = null;
    try { runtime = await Promise.race([
      findRuntime(this).catch(() => null),
      // A descriptor-mode mount has no <dregg-app>; don't wait forever for one.
      new Promise((r) => setTimeout(() => r(null), this.getAttribute('mode') === 'descriptor' ? 0 : 4000)),
    ]); } catch { runtime = null; }
    if (!this.isConnected || token !== this._connectToken) return;
    this._api = api;
    this._runtime = runtime;
    this.addEventListener('click', this._onNavigateClick);
    ensurePolisStyles();
    this._render();
  }

  _descriptor() {
    const raw = this.getAttribute('data-descriptor');
    if (!raw) return null;
    try { return JSON.parse(raw); } catch { return null; }
  }
}

// --- shared render helpers ----------------------------------------------------

/** The little state diagram: main rail + optional branch, current state lit. */
function machineDiagram(html, family, states, edges, terminal, currentCode, opts = {}) {
  // Fixed layouts per family (the three machines are small and known).
  const rail = family === 'council' || family === 'amendment'
    ? [0, 1, 3, 4] : [0, 1, 2];
  const branch = family === 'council' || family === 'amendment'
    ? { from: 1, to: 2 } : null;
  const node = (code) => {
    const lit = Number(currentCode) === code;
    const term = terminal.includes(code);
    return html`<span class=${`dregg-polis__state${lit ? ' is-lit' : ''}${term ? ' is-terminal' : ''}`}
      title=${`state code ${code}${term ? ' · terminal (no outgoing transition row — inert)' : ''}${lit ? ' · CURRENT' : ''}`}>
      ${states[code]}</span>`;
  };
  return html`
    <div class="dregg-polis__machine" role="img"
      aria-label=${`state machine, current state ${states[currentCode] ?? currentCode}`}>
      <div class="dregg-polis__rail">
        ${rail.map((code, i) => html`${i > 0 ? html`<span class="dregg-polis__arrow">→</span>` : null}${node(code)}`)}
        ${opts.coolingGate != null ? html`<span class="dregg-polis__gate" title="TemporalGate: the EXECUTED step is rejected before this block height — the program enforces the cooling-off, not the operator">⏲ enact ≥ h${String(opts.coolingGate)}</span>` : null}
      </div>
      ${branch ? html`
        <div class="dregg-polis__branchrow">
          <span class="dregg-polis__branch">${states[branch.from]} ↘</span>
          ${node(branch.to)}
        </div>` : null}
    </div>`;
}

/** "About this object" — the image explains its own construction. */
function aboutPanel(html, kind, rows) {
  const rung = rungRef(kind);
  const rungHref = rung ? surfaceHref(rung) : null;
  return html`
    <details class="dregg-inspector__section">
      <summary>About this object</summary>
      <div class="dregg-inspector__section-body">
        <dl class="dregg-inspector__kv">
          ${rows.map(([k, v]) => html`<dt>${k}</dt><dd>${v}</dd>`)}
        </dl>
        ${rungHref ? html`<div class="dregg-inspector__note">
          What is this? <a class="dregg-inspector__link" href=${rungHref}>read the concept rung</a>.
        </div>` : null}
      </div>
    </details>`;
}

function whatIsThis(html, kind) {
  const rung = rungRef(kind);
  const href = rung ? surfaceHref(rung) : null;
  if (!href) return null;
  return html`<a class="dregg-inspector__link dregg-polis__what" href=${href} title="open the docs rung that explains this object kind">what is this?</a>`;
}

function decodeSourceLabel(mode, viewOk) {
  if (mode === 'descriptor') return 'factory descriptor (published constraints — no live cell)';
  return viewOk
    ? 'live cell: slots from the node, charter terms from the served program view'
    : 'live cell slots (program view not polis-shaped — slot decode labeled best-effort)';
}

const DECODER_PROVENANCE = [
  ['decoder', 'polis-decode.js — browser port of starbridge_polis::council::inspect_council (sdk/src/polis.rs re-export); same decoder as the CLI `dregg polis council` and Discord /council-status'],
  ['slot schema', 'starbridge-apps/polis/src/lib.rs (council / constitution / mandate module docs)'],
];

// Look up a runtime cell as a signal (or null).
function cellSignal(runtime, id) {
  try { return runtime && typeof runtime.getCell === 'function' ? runtime.getCell(id) : null; } catch { return null; }
}

// --- <dregg-council> ------------------------------------------------------------

class DreggCouncil extends PolisBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    const mode = this.getAttribute('mode') || 'default';
    const descriptor = this._descriptor();

    let parsed = null;
    if (mode !== 'descriptor') {
      try { parsed = parseRef(this.getAttribute('uri')); } catch {}
      if (renderParseError(this, this.getAttribute('uri'), parsed, 'council')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);
    const sig = parsed ? cellSignal(this._runtime, parsed.id) : null;

    const Component = () => {
      const cell = sig ? sig.value : null;
      if (mode !== 'descriptor' && !this._runtime) {
        return emptyState(html, 'No runtime', 'This council inspector needs a <dregg-app> runtime (or mode="descriptor" with a descriptor).');
      }
      if (mode !== 'descriptor' && !cell) {
        return emptyState(html, 'Cell not in this runtime',
          html`No cell <code>${shortHex(parsed.id, 16)}</code> on this runtime — nothing is fabricated.`);
      }

      const constraints = mode === 'descriptor' ? constraintsOf(descriptor) : constraintsOf(cell?.program);
      const cls = classifyConstraints(constraints);
      const isCouncilShaped = cls && (cls.family === 'council' || cls.family === 'amendment');
      const fields = mode === 'descriptor' ? [] : (cell?.fields || []);
      const status = inspectCouncil(
        {
          threshold: isCouncilShaped ? cls.threshold : null,
          members: isCouncilShaped ? cls.members : COUNCIL.MAX_MEMBERS,
          membersCommit: isCouncilShaped ? cls.membersCommit : null,
        },
        fields,
      );
      const ladder = ceremonyLadder(status);
      const family = cls?.family === 'amendment' ? 'amendment' : 'council';

      const approvalsChips = status.approvals.map((a, i) => html`
        <span class=${`dregg-polis__bit${a ? ' is-on' : ''}`}
          title=${`member ${i} (charter order, slot ${COUNCIL.FIRST_APPROVAL_SLOT + i}) — ${a ? 'approved (monotone: cannot be retracted)' : 'not approved'}`}>
          ${a ? '●' : '○'} m${i}</span>`);

      const thresholdCell = status.threshold != null
        ? html`<strong>${status.approvalCount} / ${status.threshold}</strong>`
        : html`<strong>${status.approvalCount}</strong> <span class="dregg-inspector__meta" title="the AffineLe threshold gate has no StateConstraintView projection yet, so a live program view cannot carry M; the executor still enforces it — read M from the published descriptor">/ M (not in node view)</span>`;

      return html`
        <div class="dregg-inspector dregg-polis">
          <header class="dregg-polis__head">
            <span class="dregg-inspector__kind">${family === 'amendment' ? 'amendment proposal' : 'council proposal'}</span>
            ${parsed ? dreggCodeLink(html, `dregg://cell/${parsed.id}`, shortHex(parsed.id, 16), 'open the raw cell') : html`<span class="dregg-polis__pill">factory view — no live cell</span>`}
            ${whatIsThis(html, 'council')}
          </header>

          ${mode === 'descriptor' ? html`
            <div class="dregg-inspector__notice">
              FACTORY VIEW: the machine and charter terms below are the published descriptor's
              constraints. Every cell born from this factory starts at <strong>DRAFT</strong>
              (the all-zero birth state) and lives under exactly these teeth.
            </div>` : null}
          ${mode !== 'descriptor' && !isCouncilShaped ? html`
            <div class="dregg-inspector__notice dregg-inspector__notice--warn">
              The program view this runtime serves is not council-shaped — decoding the 8 slots
              against the council schema anyway, labeled best-effort.
            </div>` : null}

          ${machineDiagram(html, family, COUNCIL.STATES, COUNCIL.EDGES, COUNCIL.TERMINAL,
            mode === 'descriptor' ? 0 : status.stateCode,
            { coolingGate: cls?.enactNotBefore })}

          <div class="dregg-inspector__summary">
            <div><span>state</span><strong>${mode === 'descriptor' ? 'DRAFT (birth)' : status.state}</strong></div>
            <div><span>approvals</span>${thresholdCell}</div>
            <div><span>certified</span><strong>${status.certified ? 'armed' : 'not armed'}</strong></div>
          </div>

          <dl class="dregg-inspector__kv">
            ${isCouncilShaped ? html`<dt>charter</dt><dd>${cls.threshold != null ? `${cls.threshold}-of-${cls.members}` : `${cls.members} member slot${cls.members === 1 ? '' : 's'} (M not in view)`}</dd>` : null}
            <dt>member approvals</dt><dd>${approvalsChips.length ? approvalsChips : html`<em>none decodable</em>`}</dd>
            <dt>staged ${family === 'amendment' ? 'successor hash' : 'proposal hash'}</dt>
            <dd>${status.proposalStaged ? html`<code title=${status.proposalHash}>${shortHex(status.proposalHash, 20)}</code>` : html`<em>nothing staged${mode === 'descriptor' ? ' at birth' : ''}</em>`}
              ${family === 'amendment' && cls?.pinnedProposalHash != null ? html` <span class="dregg-polis__pill" title="the amendment descriptor pins exactly which successor constitution it stages — the staged hash is a descriptor literal">pinned: <code>${shortHex(fieldHex(cls.pinnedProposalHash), 14)}</code></span>` : null}</dd>
            <dt>membership commitment</dt>
            <dd>${fieldIsZero(status.membersCommit) ? html`<em>not yet published (written at propose)</em>` : html`<code title=${status.membersCommit}>${shortHex(status.membersCommit, 20)}</code>`}
              ${status.membersCommitMatches === true ? html` <span class="dregg-polis__pill is-ok" title="slot 6 equals the charter commitment pinned in the descriptor">matches charter pin</span>` : null}
              ${status.membersCommitMatches === false && status.proposalStaged ? html` <span class="dregg-polis__pill is-bad">≠ charter pin</span>` : null}</dd>
            ${cls?.enactNotBefore != null ? html`<dt>cooling gate</dt><dd>enact admitted only at block height ≥ <strong>${String(cls.enactNotBefore)}</strong> (TemporalGate, program-enforced)</dd>` : null}
          </dl>

          <div class="dregg-polis__ladder">
            ${ladder.map((rung) => html`
              <div class=${`dregg-polis__rung${rung.done ? ' is-done' : ''}${rung.terminalBranch ? ' is-rejected' : ''}`}>
                <span class="dregg-polis__rungmark">${rung.done ? (rung.terminalBranch ? '✕' : '✓') : '·'}</span>
                <span class="dregg-polis__rungname">${rung.step}</span>
                <span class="dregg-polis__rungdetail">${rung.detail}</span>
              </div>`)}
          </div>

          ${parsed && family === 'amendment' ? html`
            <div class="dregg-inspector__actions">
              ${dreggCodeLink(html, `dregg://amendment-ceremony/${parsed.id}`, 'walk the amendment ceremony →', 'receipt-chain view of the propose → approve → enact → supersede ceremony')}
            </div>` : null}
          ${parsed ? html`
            <div class="dregg-inspector__actions">
              ${dreggCodeLink(html, `dregg://cell-history/${parsed.id}`, 'receipt time-travel', 'walk this cell\'s receipt chain')}
            </div>` : null}

          ${aboutPanel(html, 'council', [
            ['rendered from', decodeSourceLabel(mode, isCouncilShaped)],
            ...DECODER_PROVENANCE,
            ['machine source', 'AllowedTransitions / AffineLe / Monotonic constraints as served — the figure is decoded, not drawn from prose'],
          ])}
        </div>`;
    };

    this._dispose = effect(() => { if (sig) sig.value; render(h(Component, {}), root); });
  }
}

// --- <dregg-constitution> ---------------------------------------------------------

class DreggConstitution extends PolisBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    const mode = this.getAttribute('mode') || 'default';
    const descriptor = this._descriptor();

    let parsed = null;
    if (mode !== 'descriptor') {
      try { parsed = parseRef(this.getAttribute('uri')); } catch {}
      if (renderParseError(this, this.getAttribute('uri'), parsed, 'constitution')) return;
    }
    const root = document.createElement('div');
    this.appendChild(root);
    const sig = parsed ? cellSignal(this._runtime, parsed.id) : null;

    const Component = () => {
      const cell = sig ? sig.value : null;
      if (mode !== 'descriptor' && !cell) {
        return emptyState(html, 'Cell not in this runtime',
          html`No cell <code>${shortHex(parsed?.id, 16)}</code> on this runtime.`);
      }
      const constraints = mode === 'descriptor' ? constraintsOf(descriptor) : constraintsOf(cell?.program);
      const cls = classifyConstraints(constraints);
      const shaped = cls?.family === 'constitution';
      const st = inspectConstitution(mode === 'descriptor' ? [] : (cell?.fields || []));
      const stateCode = mode === 'descriptor' ? 0 : st.stateCode;

      // Pinned literals from the program (the constitution's whole point):
      // shown beside the live slots so pin == slot is visible.
      const pinRow = (label, pinned, live, fmt = String) => html`
        <dt>${label}</dt>
        <dd>${mode === 'descriptor'
          ? html`<strong>${pinned != null ? fmt(pinned) : '—'}</strong> <span class="dregg-polis__pill" title="pinned literal: once the cell leaves UNINIT this slot can never differ from the descriptor's published value">pinned for life</span>`
          : html`<strong>${fmt(live)}</strong>${shaped && pinned != null ? html` <span class=${`dregg-polis__pill ${Number(pinned) === Number(live) || stateCode === 0 ? 'is-ok' : 'is-bad'}`} title="the descriptor pin for this slot">pin: ${fmt(pinned)}</span>` : null}`}</dd>`;

      return html`
        <div class="dregg-inspector dregg-polis">
          <header class="dregg-polis__head">
            <span class="dregg-inspector__kind">constitution</span>
            ${parsed ? dreggCodeLink(html, `dregg://cell/${parsed.id}`, shortHex(parsed.id, 16), 'open the raw cell') : html`<span class="dregg-polis__pill">factory view — no live cell</span>`}
            ${whatIsThis(html, 'constitution')}
          </header>

          ${mode === 'descriptor' ? html`
            <div class="dregg-inspector__notice">
              FACTORY VIEW: this per-version factory births exactly ONE cell (creation budget 1);
              its descriptor hash is the identity an amendment stages and a superseded predecessor records.
            </div>` : null}
          ${mode !== 'descriptor' && !shaped ? html`
            <div class="dregg-inspector__notice dregg-inspector__notice--warn">
              The served program view is not constitution-shaped — slot decode labeled best-effort.
            </div>` : null}

          ${machineDiagram(html, 'constitution', CONSTITUTION.STATES, CONSTITUTION.EDGES, CONSTITUTION.TERMINAL, stateCode)}

          <div class="dregg-inspector__summary">
            <div><span>state</span><strong>${mode === 'descriptor' ? 'UNINIT (birth)' : st.state}</strong></div>
            <div><span>version</span><strong>${mode === 'descriptor' ? (cls?.version ?? '—') : (st.version || '—')}</strong></div>
            <div><span>amendment</span><strong>${st.superseded ? 'superseded' : 'reissue-only'}</strong></div>
          </div>

          <dl class="dregg-inspector__kv">
            ${pinRow('version', shaped ? cls.version : null, st.version)}
            ${pinRow('council threshold', shaped ? cls.councilThreshold : null, st.councilThreshold)}
            ${pinRow('amendment delay (blocks)', shaped ? cls.amendmentDelay : null, st.amendmentDelay)}
            ${pinRow('treasury cap', shaped ? cls.treasuryCap : null, st.treasuryCap)}
            <dt>successor hash</dt>
            <dd>${st.superseded
              ? html`<code title=${st.successorHash}>${shortHex(st.successorHash, 20)}</code> <span class="dregg-polis__pill" title="written exactly once (WriteOnce), only at the supersede step; this cell is now terminally inert">recorded at supersede</span>`
              : html`<em>none — ${mode === 'descriptor' ? 'written only at the supersede step' : 'this version is not superseded'}</em>`}</dd>
          </dl>

          <div class="dregg-inspector__note">
            Parameter mutation on this cell is <strong>impossible</strong> (every parameter slot is a
            pinned literal once ACTIVE); amendment is REISSUE — a successor cell is born and this one
            steps to SUPERSEDED exactly once, recording the successor's descriptor hash.
          </div>

          ${parsed ? html`<div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://cell-history/${parsed.id}`, 'receipt time-travel', 'walk this cell\'s receipt chain')}
          </div>` : null}

          ${aboutPanel(html, 'constitution', [
            ['rendered from', decodeSourceLabel(mode, shaped)],
            ...DECODER_PROVENANCE,
            ['pin readback', 'pin_term shape: AnyOf[state==UNINIT, slot==literal] — the literals shown are decoded from the constraints, not typed in'],
          ])}
        </div>`;
    };

    this._dispose = effect(() => { if (sig) sig.value; render(h(Component, {}), root); });
  }
}

// --- <dregg-mandate> ----------------------------------------------------------------

class DreggMandate extends PolisBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    const mode = this.getAttribute('mode') || 'default';
    const descriptor = this._descriptor();

    let parsed = null;
    if (mode !== 'descriptor') {
      try { parsed = parseRef(this.getAttribute('uri')); } catch {}
      if (renderParseError(this, this.getAttribute('uri'), parsed, 'mandate')) return;
    }
    const root = document.createElement('div');
    this.appendChild(root);
    const sig = parsed ? cellSignal(this._runtime, parsed.id) : null;

    const Component = () => {
      const cell = sig ? sig.value : null;
      if (mode !== 'descriptor' && !cell) {
        return emptyState(html, 'Cell not in this runtime',
          html`No cell <code>${shortHex(parsed?.id, 16)}</code> on this runtime.`);
      }
      const constraints = mode === 'descriptor' ? constraintsOf(descriptor) : constraintsOf(cell?.program);
      const cls = classifyConstraints(constraints);
      const shaped = cls?.family === 'mandate';
      const st = inspectMandate(mode === 'descriptor' ? [] : (cell?.fields || []), cell?.balance);
      const stateCode = mode === 'descriptor' ? 0 : st.stateCode;
      const slice = mode === 'descriptor' ? (shaped ? cls.slice : null) : st.slice;
      const remaining = st.remaining;

      return html`
        <div class=${`dregg-inspector dregg-polis${st.revoked ? ' dregg-polis--inert' : ''}`}>
          <header class="dregg-polis__head">
            <span class="dregg-inspector__kind">worker mandate</span>
            ${parsed ? dreggCodeLink(html, `dregg://cell/${parsed.id}`, shortHex(parsed.id, 16), 'open the raw cell') : html`<span class="dregg-polis__pill">factory view — no live cell</span>`}
            ${st.revoked ? html`<span class="dregg-polis__pill is-bad" title="REVOKED is terminal with no outgoing transition row: the executor rejects EVERY further touch of this cell — spends, re-activation, even transfers in">REVOKED · inert</span>` : null}
            ${whatIsThis(html, 'mandate')}
          </header>

          ${mode !== 'descriptor' && !shaped ? html`
            <div class="dregg-inspector__notice dregg-inspector__notice--warn">
              The served program view is not mandate-shaped — slot decode labeled best-effort.
            </div>` : null}

          ${machineDiagram(html, 'mandate', MANDATE.STATES, MANDATE.EDGES, MANDATE.TERMINAL, stateCode)}

          <div class="dregg-inspector__summary">
            <div><span>state</span><strong>${mode === 'descriptor' ? 'UNINIT (birth)' : st.state}</strong></div>
            <div><span>slice</span><strong>${slice ?? '—'}</strong></div>
            <div><span>remaining</span><strong>${remaining != null ? remaining : '—'}</strong></div>
          </div>

          ${slice != null && remaining != null && Number(slice) > 0 ? html`
            <div class="dregg-polis__budget" title="the slice IS the cell's funded balance: a spend beyond the remaining balance cannot commit (kernel conservation — the enforcement is the move law, not a predicate)">
              <span class="dregg-inspector__progress"><span class="dregg-inspector__progress-fill" style=${`width:${Math.max(0, Math.min(100, (remaining / Number(slice)) * 100))}%`}></span></span>
              <span class="dregg-inspector__meta">${remaining} of ${slice} unspent — conservation-enforced, not program-checked</span>
            </div>` : null}

          <dl class="dregg-inspector__kv">
            <dt>worker tag</dt><dd><code title=${mode === 'descriptor' ? fieldHex(cls?.workerTag) : st.workerTag}>${shortHex(mode === 'descriptor' ? fieldHex(cls?.workerTag) : st.workerTag, 18)}</code> <span class="dregg-polis__pill" title="per-worker identity tag: makes this mandate content-addressed to ONE worker even when slices and scopes coincide">pinned</span></dd>
            <dt>tool scope</dt><dd><code title=${mode === 'descriptor' ? fieldHex(cls?.toolScope) : st.toolScope}>${shortHex(mode === 'descriptor' ? fieldHex(cls?.toolScope) : st.toolScope, 18)}</code> <span class="dregg-inspector__meta" title="blake3('dregg-polis:tool-scope v1', tool list) — the published audit anchor; per-tool gating lives at the MCP capability layer (lib docs gap 6)">commitment</span></dd>
            <dt>orchestrator</dt><dd>${(() => {
              const orch = mode === 'descriptor' ? fieldHex(cls?.orchestrator) : st.orchestrator;
              return fieldIsZero(orch) ? html`<em>—</em>` : dreggCodeLink(html, `dregg://cell/${orch}`, shortHex(orch, 16), 'the delegating cell');
            })()}</dd>
          </dl>

          ${st.revoked ? html`
            <div class="dregg-inspector__notice dregg-inspector__notice--warn">
              Revoked: terminal and inert. Any residual balance is unrecoverable (the recover transfer
              must ride IN the revoke turn itself — after it, every touch is rejected).
            </div>` : null}

          ${parsed ? html`<div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://cell-history/${parsed.id}`, 'receipt time-travel', 'every spend is a receipt resolving to this content-addressed mandate')}
          </div>` : null}

          ${aboutPanel(html, 'mandate', [
            ['rendered from', decodeSourceLabel(mode, shaped)],
            ...DECODER_PROVENANCE,
            ['budget enforcement', 'kernel conservation (the slice IS the balance) — published in slot 1 for audit, enforced by the move law'],
          ])}
        </div>`;
    };

    this._dispose = effect(() => { if (sig) sig.value; render(h(Component, {}), root); });
  }
}

// --- <dregg-amendment-ceremony> --------------------------------------------------------

function cellMatches(r, id) {
  const want = String(id || '').toLowerCase();
  const fields = [r.agent, r.cell, r.cell_id, r.target];
  if (fields.some((f) => String(f || '').toLowerCase() === want)) return true;
  const touched = r.touched_cells || r.cells || [];
  return Array.isArray(touched) && touched.some((c) => String(c || '').toLowerCase() === want);
}

class DreggAmendmentCeremony extends PolisBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(this.getAttribute('uri')); } catch {}
    if (renderParseError(this, this.getAttribute('uri'), parsed, 'amendment-ceremony')) return;
    const cellId = parsed.id;
    // Optional cross-cell legs: dregg://amendment-ceremony/<id>/old/<id>/new/<id>
    const sub = parsed.sub || [];
    const oldConstitution = sub[0] === 'old' ? sub[1] : null;
    const newConstitution = (sub[0] === 'new' ? sub[1] : null) || (sub[2] === 'new' ? sub[3] : null);

    const runtime = this._runtime;
    const chainSig = runtime && typeof runtime.listCellReceipts === 'function' ? runtime.listCellReceipts(cellId) : null;
    const allSig = runtime && typeof runtime.listReceipts === 'function' ? runtime.listReceipts() : null;
    const sig = cellSignal(runtime, cellId);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cell = sig ? sig.value : null;
      if (!runtime) return emptyState(html, 'No runtime', 'The ceremony view walks a live receipt chain.');
      if (!cell) {
        return emptyState(html, 'Cell not in this runtime',
          html`No amendment cell <code>${shortHex(cellId, 16)}</code> on this runtime.`);
      }
      const cls = classifyConstraints(constraintsOf(cell.program));
      const status = inspectCouncil(
        { threshold: cls?.threshold ?? null, members: cls?.members ?? COUNCIL.MAX_MEMBERS, membersCommit: cls?.membersCommit ?? null },
        cell.fields || [],
      );
      const ladder = ceremonyLadder(status);

      // The receipt chain (oldest first — a ceremony reads forward).
      let receipts = chainSig ? chainSig.value : null;
      if (!Array.isArray(receipts) || !receipts.length) {
        receipts = ((allSig && allSig.value) || []).filter((r) => cellMatches(r, cellId));
      }
      const chain = [...(receipts || [])].sort((a, b) => Number(a.chain_index ?? 0) - Number(b.chain_index ?? 0)
        || Number(a.timestamp ?? 0) - Number(b.timestamp ?? 0));

      const crossCellRungs = [
        {
          step: 'successor birth',
          detail: 'the staged constitution cell is created from its per-version factory (descriptor hash = the pinned literal above)',
          cross: newConstitution,
        },
        {
          step: 'supersede predecessor',
          detail: 'the old constitution records the successor hash and steps ACTIVE → SUPERSEDED (terminal)',
          cross: oldConstitution,
        },
      ];

      return html`
        <div class="dregg-inspector dregg-polis">
          <header class="dregg-polis__head">
            <span class="dregg-inspector__kind">amendment ceremony</span>
            ${dreggCodeLink(html, `dregg://council/${cellId}`, shortHex(cellId, 16), 'open the amendment proposal inspector')}
            ${whatIsThis(html, 'amendment-ceremony')}
          </header>

          <div class="dregg-inspector__note" style="margin-bottom:8px;">
            The receipt chain IS the forward certification: each rung below is witnessed by the
            machine's monotone slots; the receipts are the canonical per-step record.
            ${cls?.enactNotBefore != null ? html` Cooling gate: enact admitted only at height ≥ <strong>${String(cls.enactNotBefore)}</strong>.` : null}
          </div>

          <div class="dregg-polis__ladder">
            ${ladder.map((rung) => html`
              <div class=${`dregg-polis__rung${rung.done ? ' is-done' : ''}${rung.terminalBranch ? ' is-rejected' : ''}`}>
                <span class="dregg-polis__rungmark">${rung.done ? (rung.terminalBranch ? '✕' : '✓') : '·'}</span>
                <span class="dregg-polis__rungname">${rung.step}</span>
                <span class="dregg-polis__rungdetail">${rung.detail}</span>
              </div>`)}
            ${crossCellRungs.map((rung) => html`
              <div class="dregg-polis__rung dregg-polis__rung--cross">
                <span class="dregg-polis__rungmark">↗</span>
                <span class="dregg-polis__rungname">${rung.step}</span>
                <span class="dregg-polis__rungdetail">${rung.detail}
                  ${rung.cross
                    ? html` — ${dreggCodeLink(html, `dregg://cell-history/${rung.cross}`, shortHex(rung.cross, 14), 'walk that cell\'s receipt chain')}`
                    : html` <em>(cross-cell: its receipts live on the constitution cell — open its history to verify the ordering)</em>`}</span>
              </div>`)}
          </div>

          <details class="dregg-inspector__section" open>
            <summary>this cell's receipt chain (${chain.length}, oldest first)</summary>
            <div class="dregg-inspector__section-body">
              ${chain.length ? html`
                <table class="dregg-inspector__table">
                  <thead><tr><th>#</th><th>turn</th><th>effects</th><th>post-state</th></tr></thead>
                  <tbody>
                    ${chain.map((r, i) => html`
                      <tr>
                        <td>${String(r.chain_index ?? i)}</td>
                        <td>${dreggCodeLink(html, `dregg://receipt/${r.turn_hash || r.receipt_hash}`, shortHex(r.turn_hash || r.receipt_hash, 14), 'open the witnessed receipt')}</td>
                        <td>${Array.isArray(r.effect_kinds) && r.effect_kinds.length ? r.effect_kinds.join(' · ') : html`<em>${String(r.action_count ?? 0)} action${(r.action_count ?? 0) === 1 ? '' : 's'}</em>`}</td>
                        <td><code title=${r.post_state_hash}>${shortHex(r.post_state_hash, 14)}</code></td>
                      </tr>`)}
                  </tbody>
                </table>` : html`<div class="dregg-inspector__note">No receipts served for this cell yet — a cell with no turns has no ceremony.</div>`}
            </div>
          </details>

          ${aboutPanel(html, 'amendment-ceremony', [
            ['rendered from', 'live receipt chain + the amendment cell\'s slots and served program view'],
            ...DECODER_PROVENANCE,
            ['ladder soundness', 'each rung\'s done-mark is witnessed by a monotone slot (WriteOnce hash, monotone approval bits, monotone flag, terminal state) — readback, not inference'],
          ])}
        </div>`;
    };

    this._dispose = effect(() => {
      if (chainSig) chainSig.value;
      if (allSig) allSig.value;
      if (sig) sig.value;
      render(h(Component, {}), root);
    });
  }
}

// --- registration + styles ---------------------------------------------------------

if (!customElements.get('dregg-council')) customElements.define('dregg-council', DreggCouncil);
if (!customElements.get('dregg-constitution')) customElements.define('dregg-constitution', DreggConstitution);
if (!customElements.get('dregg-mandate')) customElements.define('dregg-mandate', DreggMandate);
if (!customElements.get('dregg-amendment-ceremony')) customElements.define('dregg-amendment-ceremony', DreggAmendmentCeremony);

function ensurePolisStyles() {
  if (document.getElementById('dregg-polis-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-polis-styles';
  s.textContent = `
.dregg-polis__head { display:flex; align-items:center; gap:10px; flex-wrap:wrap; border-bottom:1px solid var(--line,#30363d); padding-bottom:6px; margin-bottom:8px; }
.dregg-polis__what { margin-left:auto; font-size:0.72rem; }
.dregg-polis__machine { border:1px solid var(--line,#30363d); border-radius:6px; background:var(--bg,#0d1117); padding:10px 12px; margin:8px 0; }
.dregg-polis__rail { display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
.dregg-polis__branchrow { display:flex; align-items:center; gap:8px; margin-top:6px; padding-left:18px; }
.dregg-polis__branch { color:var(--fg-dim,#9aa0a6); font-size:0.7rem; }
.dregg-polis__state { display:inline-block; border:1px solid var(--line,#30363d); border-radius:5px; padding:3px 9px; font-size:0.74rem; letter-spacing:0.04em; color:var(--fg-dim,#9aa0a6); background:var(--bg-raised,#161b22); }
.dregg-polis__state.is-terminal { border-style:double; border-width:3px; }
.dregg-polis__state.is-lit { color:var(--bg,#0d1117); background:var(--accent,#5b8a5a); border-color:var(--accent,#5b8a5a); font-weight:650; }
.dregg-polis__arrow { color:var(--fg-dim,#9aa0a6); }
.dregg-polis__gate { margin-left:6px; border:1px dashed var(--line,#30363d); border-radius:999px; padding:2px 8px; font-size:0.68rem; color:#f2d06b; cursor:help; }
.dregg-polis__pill { display:inline-block; border:1px solid var(--line,#30363d); border-radius:999px; padding:1px 8px; font-size:0.66rem; color:var(--fg-dim,#9aa0a6); }
.dregg-polis__pill.is-ok { border-color:#62c47a; color:#8ee6a2; }
.dregg-polis__pill.is-bad { border-color:#d4685c; color:#f18b7d; }
.dregg-polis__bit { display:inline-block; border:1px solid var(--line,#30363d); border-radius:999px; padding:1px 8px; margin-right:4px; font-size:0.7rem; color:var(--fg-dim,#9aa0a6); cursor:help; }
.dregg-polis__bit.is-on { border-color:#62c47a; color:#8ee6a2; }
.dregg-polis__ladder { display:grid; gap:4px; margin:10px 0; }
.dregg-polis__rung { display:grid; grid-template-columns:18px max-content minmax(0,1fr); gap:8px; align-items:baseline; border:1px solid var(--line,#30363d); border-radius:5px; background:var(--bg-raised,#161b22); padding:6px 9px; }
.dregg-polis__rung.is-done { border-color:#62c47a; }
.dregg-polis__rung.is-rejected { border-color:#d4685c; }
.dregg-polis__rung--cross { border-style:dashed; }
.dregg-polis__rungmark { color:#8ee6a2; }
.dregg-polis__rung.is-rejected .dregg-polis__rungmark { color:#f18b7d; }
.dregg-polis__rungname { font-size:0.78rem; color:var(--fg,#e8f0e8); font-weight:600; }
.dregg-polis__rungdetail { font-size:0.74rem; color:var(--fg-dim,#9aa0a6); line-height:1.4; }
.dregg-polis__budget { display:flex; align-items:center; gap:10px; margin:6px 0 10px; cursor:help; }
.dregg-polis--inert { opacity:0.82; }
.dregg-polis--inert .dregg-polis__machine { filter:saturate(0.4); }
`;
  document.head.appendChild(s);
}
