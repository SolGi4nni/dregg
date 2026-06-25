#!/usr/bin/env node
// Drive the SERVED live TALLY-BOARD page in headless Chrome over the DevTools Protocol (CDP).
// PROVES the FULL ViewNode vocabulary (Row + Table + a multi-affordance row) renders AND fires
// real cap-gated verified turns in a browser TAB, through the SAME `ViewNode` IR the native
// cockpit renders:
//
//   1. launch headless Chrome with --remote-debugging-port, navigate to the tally page;
//   2. wait for the in-tab `TallyWorld` to boot (window.__deosCard bound);
//   3. read the three bound tally rows (slots 0/1/2) + the receipt count off the LIVE ledger;
//   4. assert the rendered DOM carries a `.deos-table` of three `.deos-row`s, each with a
//      `+1` and a `−1` button — the layout vocabulary the counter/inspector never exercised;
//   5. CLICK `+1` on oranges (slot 1) → a REAL verified turn; assert that row re-painted (1→2)
//      and ONLY that slot moved, receipts +1;
//   6. CLICK `−1` on pears (slot 2) → the opposite direction, independent slot (4→3), receipts +1;
//   7. capture a screenshot of the painted board to the given path (default: scratch/deos-tally.png).
//
// No npm deps: node's built-in fetch + WebSocket (node >= 22). Chrome via $CHROME or the macOS
// default. The page must already be SERVED (file:// is CORS-blocked).
//
//   node scripts/drive-deos-tally.mjs [http://localhost:8000/tally.html] [screenshot.png]

import { spawn } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const URL = process.argv[2] || 'http://localhost:8000/tally.html';
const SHOT = process.argv[3] || join(process.cwd(), 'deos-tally.png');
const CHROME =
  process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const DEBUG_PORT = 9334;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function cdpTargets() {
  const res = await fetch(`http://127.0.0.1:${DEBUG_PORT}/json`);
  return res.json();
}

class CDP {
  constructor(ws) {
    this.ws = ws;
    this.id = 0;
    this.pending = new Map();
    ws.addEventListener('message', (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.id && this.pending.has(msg.id)) {
        const { resolve, reject } = this.pending.get(msg.id);
        this.pending.delete(msg.id);
        if (msg.error) reject(new Error(JSON.stringify(msg.error)));
        else resolve(msg.result);
      }
    });
  }
  send(method, params = {}) {
    const id = ++this.id;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.ws.send(JSON.stringify({ id, method, params }));
    });
  }
  async eval(expr) {
    const r = await this.send('Runtime.evaluate', {
      expression: expr,
      awaitPromise: true,
      returnByValue: true,
    });
    if (r.exceptionDetails) {
      throw new Error('page eval threw: ' + JSON.stringify(r.exceptionDetails));
    }
    return r.result.value;
  }
}

function assert(cond, msg) {
  if (!cond) {
    console.error('FAIL:', msg);
    process.exit(1);
  }
  console.log('  ok:', msg);
}

async function main() {
  const userDir = mkdtempSync(join(tmpdir(), 'deos-chrome-'));
  const chrome = spawn(
    CHROME,
    [
      '--headless=new',
      `--remote-debugging-port=${DEBUG_PORT}`,
      `--user-data-dir=${userDir}`,
      '--no-first-run',
      '--no-default-browser-check',
      '--force-device-scale-factor=2',
      '--window-size=520,420',
      URL,
    ],
    { stdio: 'ignore' },
  );

  let cleanup = () => {
    try {
      chrome.kill('SIGKILL');
    } catch {}
  };
  process.on('exit', cleanup);

  try {
    let target = null;
    for (let i = 0; i < 50; i++) {
      try {
        const targets = await cdpTargets();
        target = targets.find((t) => t.type === 'page' && t.webSocketDebuggerUrl);
        if (target) break;
      } catch {}
      await sleep(200);
    }
    assert(target, `Chrome devtools page target reachable (navigated to ${URL})`);

    const ws = new WebSocket(target.webSocketDebuggerUrl);
    await new Promise((res, rej) => {
      ws.addEventListener('open', res);
      ws.addEventListener('error', rej);
    });
    const cdp = new CDP(ws);
    await cdp.send('Runtime.enable');
    await cdp.send('Page.enable');

    // 1. Wait for the in-tab TallyWorld to boot.
    let booted = false;
    for (let i = 0; i < 80; i++) {
      const ready = await cdp.eval(
        `(() => { const c = window.__deosCard; return !!(c && typeof c.read === 'function' && typeof c.fire === 'function'); })()`,
      );
      if (ready) {
        booted = true;
        break;
      }
      await sleep(250);
    }
    assert(booted, 'the in-tab TallyWorld booted (window.__deosCard bound, real verified executor)');

    // 2. The rendered DOM carries the LAYOUT vocabulary the counter/inspector never exercised.
    const layout = await cdp.eval(
      `(() => ({
        tables: document.querySelectorAll('.deos-table').length,
        rows: document.querySelectorAll('.deos-table .deos-row').length,
        incs: document.querySelectorAll('.deos-button[data-turn="inc"]').length,
        decs: document.querySelectorAll('.deos-button[data-turn="dec"]').length,
      }))()`,
    );
    console.log('  rendered layout:', JSON.stringify(layout));
    assert(layout.tables === 1, 'the board rendered a Table');
    assert(layout.rows === 3, 'the Table holds three Rows (the three tallies)');
    assert(layout.incs === 3 && layout.decs === 3, 'each Row carries BOTH affordances (+1 / −1)');

    // 3. Read the bound rows + receipts off the LIVE in-tab ledger.
    const before = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s0: Number(c.read(0)), s1: Number(c.read(1)), s2: Number(c.read(2)), receipts: c.receiptCount(), cell: c.cellId() }; })()`,
    );
    console.log('  in-tab ledger (before):', JSON.stringify(before));
    assert(before.s0 === 3 && before.s1 === 1 && before.s2 === 4, 'the three tallies read their seeds (3, 1, 4)');
    assert(before.receipts === 3, 'three seed turns committed (receipts = 3)');
    assert(before.cell && before.cell.length > 0, 'the tally cell has a real id');

    const oRow = await cdp.eval(`document.querySelector('.deos-bind[data-slot="1"]').textContent`);
    assert(/^1$/.test(oRow.trim()), `the oranges Bind row paints 1 before the click (got "${oRow}")`);

    // 4. CLICK +1 on oranges (slot 1) → a REAL verified turn.
    await cdp.eval(
      `(() => { const btns = document.querySelectorAll('.deos-row')[1].querySelectorAll('.deos-button'); btns[0].click(); })()`,
    );
    await sleep(300);
    const afterInc = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s0: Number(c.read(0)), s1: Number(c.read(1)), s2: Number(c.read(2)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab ledger (after +1 oranges):', JSON.stringify(afterInc));
    assert(afterInc.s1 === 2, 'the +1 click fired a real verified turn: oranges 1 → 2');
    assert(afterInc.s0 === 3 && afterInc.s2 === 4, 'the untouched tallies are unchanged');
    assert(afterInc.receipts === 4, 'exactly one more verified turn committed (3 → 4)');
    const oRow2 = await cdp.eval(`document.querySelector('.deos-bind[data-slot="1"]').textContent`);
    assert(/^2$/.test(oRow2.trim()), `the oranges Bind row RE-PAINTED to 2 (got "${oRow2}")`);

    // 5. CLICK −1 on pears (slot 2) → the opposite direction, an independent slot.
    await cdp.eval(
      `(() => { const btns = document.querySelectorAll('.deos-row')[2].querySelectorAll('.deos-button'); btns[1].click(); })()`,
    );
    await sleep(300);
    const afterDec = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s1: Number(c.read(1)), s2: Number(c.read(2)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab ledger (after −1 pears):', JSON.stringify(afterDec));
    assert(afterDec.s2 === 3, 'the −1 click fired a real verified turn: pears 4 → 3');
    assert(afterDec.s1 === 2, 'oranges held its committed 2 (independent slot)');
    assert(afterDec.receipts === 5, 'five verified turns on the in-tab audit tape');

    // 6. Capture a screenshot of the painted board.
    const shot = await cdp.send('Page.captureScreenshot', { format: 'png' });
    writeFileSync(SHOT, Buffer.from(shot.data, 'base64'));
    console.log('  screenshot:', SHOT);

    console.log('\nPASS: the tally board (Row + Table + multi-affordance) renders + fires real verified turns in a browser TAB.');
  } finally {
    cleanup();
  }
}

main().catch((e) => {
  console.error('driver error:', e);
  process.exit(1);
});
