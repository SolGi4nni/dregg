// starbridge-apps/nameservice/pages/inspectors.js
//
// Web components for the nameservice starbridge-app's three UI surfaces.
// Pure custom-element shells: query window.pyana for cell data, render
// the per-name state machine, and dispatch turn requests via the
// turn-builder bridge in ./turn-builders.js (which wraps
// window.pyana.signTurn).
//
// All policy lives in Rust (starbridge-apps/nameservice/src/lib.rs); the
// JS is the thinnest possible UX layer. The three components are:
//
//   <pyana-name uri="pyana://cell/..."/>
//     Read-only view of a single name cell — owner, expiry, target,
//     revocation status.
//
//   <pyana-name-registry uri="pyana://cell/..." child-inspector="name"/>
//     Browseable list of registered names with filter + paginate.
//
//   <pyana-name-register-form registry-uri="pyana://cell/..."/>
//     Mutation surface — register / renew / transfer / revoke /
//     set-target — wired to the turn-builder bridge.
//
// Each component dispatches CustomEvents so host pages can wire their
// own analytics or persistence without forking these.

// Slot indices — mirror constants in src/lib.rs.
const NAME_HASH_SLOT       = 2;
const OWNER_HASH_SLOT      = 3;
const EXPIRY_SLOT          = 4;
const REVOKED_SLOT         = 5;
const RESOLVE_TARGET_SLOT  = 6;

const TAGS = [
  'pyana-name',
  'pyana-name-registry',
  'pyana-name-register-form',
];

// ─── helpers ─────────────────────────────────────────────────────────────

function hex32(bytes) {
  if (!bytes) return '—';
  if (typeof bytes === 'string') return bytes.length > 16 ? `${bytes.slice(0, 8)}…${bytes.slice(-8)}` : bytes;
  if (Array.isArray(bytes) || bytes instanceof Uint8Array) {
    const arr = Array.from(bytes);
    const h = arr.map((b) => b.toString(16).padStart(2, '0')).join('');
    return h.length > 16 ? `${h.slice(0, 8)}…${h.slice(-8)}` : h;
  }
  return String(bytes);
}

function u64FromBE32(bytes) {
  if (!bytes) return 0n;
  const arr = Array.isArray(bytes) || bytes instanceof Uint8Array ? Array.from(bytes) : null;
  if (!arr) return 0n;
  let v = 0n;
  for (let i = 24; i < 32; i += 1) {
    v = (v << 8n) | BigInt(arr[i] ?? 0);
  }
  return v;
}

function isZero32(bytes) {
  if (!bytes) return true;
  const arr = Array.isArray(bytes) || bytes instanceof Uint8Array ? Array.from(bytes) : null;
  if (!arr) return true;
  return arr.every((b) => b === 0);
}

// ─── <pyana-name> ────────────────────────────────────────────────────────

class PyanaNameElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'name']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  async render() {
    const uri = this.getAttribute('uri') || '';
    const nameAttr = this.getAttribute('name') || '';
    const data = await this.#load(uri);
    const revoked = !isZero32(data.revoked);
    const expiry = u64FromBE32(data.expiry);
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .card { border: 1px solid #ddd; border-radius: 6px; padding: 1rem; max-width: 480px; }
        .row { display: flex; justify-content: space-between; gap: 0.5rem; padding: 0.25rem 0; }
        .label { color: #555; }
        code { font-family: ui-monospace, monospace; }
        .status-ok  { color: #2a8a3e; font-weight: 600; }
        .status-bad { color: #c43030; font-weight: 600; }
        .row.actions { margin-top: 0.5rem; gap: 0.5rem; }
        button { padding: 0.4rem 0.7rem; }
      </style>
      <div class="card">
        <h3>${nameAttr || '(name)'}</h3>
        <div class="row"><span class="label">cell</span><code>${hex32(uri)}</code></div>
        <div class="row"><span class="label">name-hash</span><code>${hex32(data.name_hash)}</code></div>
        <div class="row"><span class="label">owner-hash</span><code>${hex32(data.owner_hash)}</code></div>
        <div class="row"><span class="label">expiry (block)</span><code>${expiry.toString()}</code></div>
        <div class="row"><span class="label">target</span><code>${isZero32(data.target) ? '—' : hex32(data.target)}</code></div>
        <div class="row">
          <span class="label">status</span>
          <span class="${revoked ? 'status-bad' : 'status-ok'}">${revoked ? 'REVOKED' : 'ACTIVE'}</span>
        </div>
        <div class="row actions">
          <button data-action="renew"     ${revoked ? 'disabled' : ''}>Renew</button>
          <button data-action="transfer"  ${revoked ? 'disabled' : ''}>Transfer</button>
          <button data-action="set-target" ${revoked ? 'disabled' : ''}>Set target</button>
          <button data-action="revoke"    ${revoked ? 'disabled' : ''}>Revoke</button>
        </div>
      </div>
    `;
    this.shadowRoot.querySelectorAll('button[data-action]').forEach((btn) => {
      btn.addEventListener('click', () => {
        this.dispatchEvent(new CustomEvent('name-action', {
          bubbles: true, composed: true,
          detail: { action: btn.dataset.action, uri, name: nameAttr },
        }));
      });
    });
  }

  async #load(uri) {
    const empty = () => ({
      name_hash: null, owner_hash: null, expiry: null,
      revoked: null, target: null,
    });
    if (typeof window === 'undefined' || !window.pyana?.cell?.readField) {
      return empty();
    }
    try {
      const [name_hash, owner_hash, expiry, revoked, target] = await Promise.all([
        window.pyana.cell.readField(uri, NAME_HASH_SLOT),
        window.pyana.cell.readField(uri, OWNER_HASH_SLOT),
        window.pyana.cell.readField(uri, EXPIRY_SLOT),
        window.pyana.cell.readField(uri, REVOKED_SLOT),
        window.pyana.cell.readField(uri, RESOLVE_TARGET_SLOT),
      ]);
      return { name_hash, owner_hash, expiry, revoked, target };
    } catch (_) {
      return empty();
    }
  }
}

// ─── <pyana-name-registry> ──────────────────────────────────────────────

class PyanaNameRegistryElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'page-size']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._filter = '';
    this._page = 0;
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  async render() {
    const uri = this.getAttribute('uri') || '';
    const pageSize = Math.max(1, Number(this.getAttribute('page-size') || 25));
    const entries = await this.#load(uri);
    const filter = this._filter.trim().toLowerCase();
    const filtered = filter
      ? entries.filter((e) => (e.name || '').toLowerCase().includes(filter))
      : entries;
    const pages = Math.max(1, Math.ceil(filtered.length / pageSize));
    if (this._page >= pages) this._page = pages - 1;
    const start = this._page * pageSize;
    const slice = filtered.slice(start, start + pageSize);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .toolbar { display: flex; gap: 0.5rem; align-items: center; margin-bottom: 0.5rem; }
        input[type=search] { padding: 0.4rem; min-width: 240px; }
        table { border-collapse: collapse; width: 100%; max-width: 760px; }
        th, td { border-bottom: 1px solid #eee; padding: 0.35rem 0.5rem; text-align: left; }
        th { background: #fafafa; }
        tr.revoked td { color: #888; text-decoration: line-through; }
        .pager { margin-top: 0.5rem; display: flex; gap: 0.4rem; align-items: center; }
        button { padding: 0.3rem 0.6rem; }
        .empty { color: #888; padding: 0.5rem; }
      </style>
      <div class="toolbar">
        <input type="search" placeholder="Filter by name…" value="${filter}" />
        <span>${filtered.length} / ${entries.length}</span>
        <button data-action="register-new">Register new…</button>
      </div>
      ${slice.length === 0
        ? `<div class="empty">No names registered${filter ? ' match the filter.' : '.'}</div>`
        : `
        <table>
          <thead>
            <tr><th>Name</th><th>Owner</th><th>Expiry</th><th>Status</th></tr>
          </thead>
          <tbody>
            ${slice.map((e) => `
              <tr class="${e.revoked ? 'revoked' : ''}">
                <td><a href="#" data-uri="${e.uri || ''}" data-name="${e.name || ''}">${e.name || '(unnamed)'}</a></td>
                <td><code>${hex32(e.owner_hash)}</code></td>
                <td><code>${e.expiry?.toString() ?? '—'}</code></td>
                <td>${e.revoked ? 'REVOKED' : 'ACTIVE'}</td>
              </tr>
            `).join('')}
          </tbody>
        </table>
        <div class="pager">
          <button data-action="prev" ${this._page === 0 ? 'disabled' : ''}>‹ Prev</button>
          <span>Page ${this._page + 1} / ${pages}</span>
          <button data-action="next" ${this._page >= pages - 1 ? 'disabled' : ''}>Next ›</button>
        </div>
      `}
    `;
    const inp = this.shadowRoot.querySelector('input[type=search]');
    inp?.addEventListener('input', (e) => { this._filter = e.target.value; this._page = 0; this.render(); });
    this.shadowRoot.querySelector('button[data-action=prev]')?.addEventListener('click', () => { this._page -= 1; this.render(); });
    this.shadowRoot.querySelector('button[data-action=next]')?.addEventListener('click', () => { this._page += 1; this.render(); });
    this.shadowRoot.querySelector('button[data-action=register-new]')?.addEventListener('click', () => {
      this.dispatchEvent(new CustomEvent('register-requested', {
        bubbles: true, composed: true, detail: { registryUri: uri },
      }));
    });
    this.shadowRoot.querySelectorAll('a[data-uri]').forEach((a) => {
      a.addEventListener('click', (e) => {
        e.preventDefault();
        this.dispatchEvent(new CustomEvent('name-selected', {
          bubbles: true, composed: true,
          detail: { uri: a.dataset.uri, name: a.dataset.name },
        }));
      });
    });
  }

  async #load(uri) {
    if (typeof window === 'undefined' || !window.pyana?.nameservice?.listEntries) {
      return [];
    }
    try {
      const entries = await window.pyana.nameservice.listEntries(uri);
      return Array.isArray(entries) ? entries : [];
    } catch (_) {
      return [];
    }
  }
}

// ─── <pyana-name-register-form> ─────────────────────────────────────────

class PyanaNameRegisterFormElement extends HTMLElement {
  static get observedAttributes() { return ['registry-uri', 'mode']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const registryUri = this.getAttribute('registry-uri') || '';
    const mode = this.getAttribute('mode') || 'register';
    const showFields = {
      register:   ['name', 'owner', 'expiry'],
      renew:      ['name', 'expiry'],
      transfer:   ['name', 'old_owner', 'new_owner'],
      revoke:     ['name'],
      set_target: ['name', 'target'],
    }[mode] ?? ['name'];

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        form { display: grid; gap: 0.75rem; max-width: 420px; }
        label { display: grid; gap: 0.25rem; }
        input, select { padding: 0.4rem; font-size: 1rem; font-family: inherit; }
        button { padding: 0.5rem; font-weight: 600; }
        .target { font-size: 0.85rem; color: #666; }
        nav { display: flex; gap: 0.4rem; margin-bottom: 0.5rem; }
        nav button { padding: 0.3rem 0.6rem; font-weight: 400; }
        nav button[aria-current=true] { background: #eef; font-weight: 600; }
      </style>
      <nav>
        ${['register', 'renew', 'transfer', 'revoke', 'set_target'].map((m) => `
          <button type="button" data-mode="${m}" aria-current="${m === mode}">${m}</button>
        `).join('')}
      </nav>
      <form>
        <div class="target">Registry: <code>${registryUri || '(none)'}</code></div>
        ${showFields.includes('name') ? `
          <label>Name<input name="name" required placeholder="alice.pyana" /></label>
        ` : ''}
        ${showFields.includes('owner') ? `
          <label>Owner pubkey (hex)<input name="owner" required placeholder="0x…" /></label>
        ` : ''}
        ${showFields.includes('old_owner') ? `
          <label>Old owner pubkey (hex)<input name="old_owner" required placeholder="0x…" /></label>
        ` : ''}
        ${showFields.includes('new_owner') ? `
          <label>New owner pubkey (hex)<input name="new_owner" required placeholder="0x…" /></label>
        ` : ''}
        ${showFields.includes('expiry') ? `
          <label>Expiry (block height)<input name="expiry" type="number" required min="1" /></label>
        ` : ''}
        ${showFields.includes('target') ? `
          <label>Target URI<input name="target" placeholder="pyana://cell/…" /></label>
        ` : ''}
        <button type="submit">${mode}</button>
      </form>
    `;
    this.shadowRoot.querySelectorAll('nav button[data-mode]').forEach((b) => {
      b.addEventListener('click', () => this.setAttribute('mode', b.dataset.mode));
    });
    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      const data = Object.fromEntries(fd.entries());
      this.#dispatch(mode, registryUri, data);
    });
  }

  async #dispatch(mode, registryUri, data) {
    const builders = (typeof window !== 'undefined') ? window.pyana?.builders?.nameservice : null;
    const builder = builders?.[`${mode}_name`] ?? builders?.[mode];
    if (!builder) {
      this.dispatchEvent(new CustomEvent(`${mode}-requested`, {
        bubbles: true, composed: true,
        detail: { registryUri, ...data },
      }));
      return;
    }
    try {
      const receipt = await builder(registryUri, data);
      this.dispatchEvent(new CustomEvent(`${mode}-submitted`, {
        bubbles: true, composed: true, detail: { receipt },
      }));
    } catch (err) {
      this.dispatchEvent(new CustomEvent(`${mode}-failed`, {
        bubbles: true, composed: true, detail: { error: String(err) },
      }));
    }
  }
}

// ─── Registration ────────────────────────────────────────────────────────

const COMPONENTS = {
  'pyana-name':                   PyanaNameElement,
  'pyana-name-registry':          PyanaNameRegistryElement,
  'pyana-name-register-form':     PyanaNameRegisterFormElement,
};

for (const [tag, ctor] of Object.entries(COMPONENTS)) {
  if (typeof customElements !== 'undefined' && !customElements.get(tag)) {
    customElements.define(tag, ctor);
  }
  if (typeof window !== 'undefined' && window.pyana?.register) {
    window.pyana.register(tag, ctor);
  }
}

export {
  PyanaNameElement,
  PyanaNameRegistryElement,
  PyanaNameRegisterFormElement,
  TAGS,
  NAME_HASH_SLOT,
  OWNER_HASH_SLOT,
  EXPIRY_SLOT,
  REVOKED_SLOT,
  RESOLVE_TARGET_SLOT,
};
