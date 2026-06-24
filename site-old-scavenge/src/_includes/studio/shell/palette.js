/**
 * palette.js — the shell's command affordance (Cmd/Ctrl-K).
 *
 * One input over everything reachable: places, tools, shell actions, your
 * cells, recent receipts — plus free-text jumps: a dregg:// ref or a bare
 * 64-hex id inspects directly. Items come from a provider function so the
 * list always reflects the live frame state.
 */

export function createPalette({ root, getItems, onRun }) {
  const el = document.createElement('div');
  el.className = 'shl-palette';
  el.hidden = true;
  el.setAttribute('role', 'dialog');
  el.setAttribute('aria-modal', 'true');
  el.setAttribute('aria-label', 'Command palette');
  el.innerHTML = `
    <div class="shl-palette__panel">
      <input class="shl-palette__input" type="text" autocomplete="off" spellcheck="false"
             placeholder="places, cells, receipts, dregg://… " aria-label="Command">
      <div class="shl-palette__list" role="listbox"></div>
      <div class="shl-palette__hint">enter to run · esc to close · ⌘K / ctrl-K</div>
    </div>`;
  root.appendChild(el);

  const input = el.querySelector('.shl-palette__input');
  const list = el.querySelector('.shl-palette__list');
  let filtered = [];
  let selected = 0;

  function score(item, query) {
    if (!query) return 1;
    const hay = `${item.label} ${item.hint || ''} ${item.keywords || ''}`.toLowerCase();
    const q = query.toLowerCase();
    if (hay.includes(q)) return 100 - hay.indexOf(q);
    // subsequence match
    let i = 0;
    for (const ch of hay) { if (ch === q[i]) i += 1; if (i === q.length) return 10; }
    return 0;
  }

  function freeTextItems(query) {
    const q = query.trim();
    const items = [];
    if (/^dregg:\/\/[a-z-]+\/.+$/i.test(q)) {
      items.push({ label: `inspect ${q}`, hint: 'open in the shell inspector', run: () => onRun({ kind: 'inspect', uri: q }) });
    } else if (/^[0-9a-f]{64}$/i.test(q)) {
      items.push({ label: `inspect cell ${q.slice(0, 12)}…`, hint: 'treat as a cell id', run: () => onRun({ kind: 'inspect', uri: `dregg://cell/${q.toLowerCase()}` }) });
      items.push({ label: `inspect receipt ${q.slice(0, 12)}…`, hint: 'treat as a turn hash', run: () => onRun({ kind: 'inspect', uri: `dregg://receipt/${q.toLowerCase()}` }) });
    }
    return items;
  }

  function render() {
    const query = input.value.trim();
    const ranked = getItems()
      .map((item) => ({ item, s: score(item, query) }))
      .filter(({ s }) => s > 0)
      .sort((a, b) => b.s - a.s)
      .map(({ item }) => item);
    filtered = [...freeTextItems(query), ...ranked].slice(0, 12);
    selected = Math.min(selected, Math.max(0, filtered.length - 1));
    list.replaceChildren();
    if (!filtered.length) {
      const empty = document.createElement('div');
      empty.className = 'shl-palette__empty';
      empty.textContent = 'nothing matches';
      list.appendChild(empty);
      return;
    }
    filtered.forEach((item, idx) => {
      const row = document.createElement('button');
      row.type = 'button';
      row.className = 'shl-palette__item';
      row.setAttribute('role', 'option');
      row.setAttribute('aria-selected', idx === selected ? 'true' : 'false');
      row.innerHTML = `<strong></strong><span></span>`;
      row.querySelector('strong').textContent = item.label;
      row.querySelector('span').textContent = item.hint || '';
      row.addEventListener('click', () => { close(); item.run(); });
      list.appendChild(row);
    });
  }

  function open(seed = '') {
    el.hidden = false;
    input.value = seed;
    selected = 0;
    render();
    queueMicrotask(() => input.focus());
  }
  function close() {
    el.hidden = true;
  }

  input.addEventListener('input', () => { selected = 0; render(); });
  input.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowDown') { e.preventDefault(); selected = Math.min(selected + 1, filtered.length - 1); render(); }
    else if (e.key === 'ArrowUp') { e.preventDefault(); selected = Math.max(selected - 1, 0); render(); }
    else if (e.key === 'Enter') {
      e.preventDefault();
      const item = filtered[selected];
      if (item) { close(); item.run(); }
    } else if (e.key === 'Escape') { close(); }
  });
  el.addEventListener('click', (e) => { if (e.target === el) close(); });

  document.addEventListener('keydown', (e) => {
    if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k') {
      e.preventDefault();
      if (el.hidden) open(); else close();
    }
  });

  return { open, close };
}
