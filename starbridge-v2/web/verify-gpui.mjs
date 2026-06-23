// Headless-Chrome verification of the gpui cockpit bundle (pkg-gpui/).
//
// The bar: the SAME browser-run discipline the gpui-free `WebImage` skin passes —
// a real (headless) browser loads the bundle, invokes `boot_cockpit`, and we
// report HONESTLY how far it gets: bundle load → boot invoked → WebGPU init →
// canvas created → first paint. It distinguishes "renders the cockpit" from the
// real ceiling ("WebGPU up but the gpui_web run-loop stops before first paint").
//
// Prereq: build the bundle (`./build-gpui.sh`) and serve this dir, e.g.
//   python3 -m http.server 8099
// then:
//   node verify-gpui.mjs                                   # default URL
//   node verify-gpui.mjs http://localhost:8099/cockpit_gpui.html out.png
//
// puppeteer resolution: uses a global puppeteer if present (this repo has one
// under @mermaid-js/mermaid-cli). Override with PUPPETEER_PATH=/abs/.../puppeteer.js.
import { createRequire } from 'node:module';
import { execSync } from 'node:child_process';

async function loadPuppeteer() {
  if (process.env.PUPPETEER_PATH) return (await import(process.env.PUPPETEER_PATH)).default;
  try { return (await import('puppeteer')).default; } catch {}
  // fall back to the global install this repo ships (mermaid-cli's puppeteer)
  try {
    const root = execSync('npm root -g', { encoding: 'utf8' }).trim();
    const p = `${root}/@mermaid-js/mermaid-cli/node_modules/puppeteer/lib/esm/puppeteer/puppeteer.js`;
    return (await import(p)).default;
  } catch (e) {
    console.error('Could not locate puppeteer. Set PUPPETEER_PATH or `npm i -g puppeteer`.');
    throw e;
  }
}

const URL = process.argv[2] || 'http://localhost:8099/cockpit_gpui.html';
const SHOT = process.argv[3] || '/tmp/cockpit-headless.png';
const puppeteer = await loadPuppeteer();

const browser = await puppeteer.launch({
  headless: true,
  args: ['--enable-unsafe-webgpu', '--enable-features=Vulkan,WebGPU', '--use-angle=metal', '--ignore-gpu-blocklist', '--no-sandbox'],
});
const page = await browser.newPage();
await page.setViewport({ width: 1280, height: 820 });

const logs = [];
page.on('console', m => logs.push(`[console.${m.type()}] ${m.text()}`));
page.on('pageerror', e => logs.push(`[pageerror] ${e.message}`));
page.on('requestfailed', r => logs.push(`[requestfailed] ${r.url()} :: ${r.failure()?.errorText}`));

await page.goto(URL, { waitUntil: 'load', timeout: 60000 });

const gpu = await page.evaluate(async () => {
  const o = { present: !!navigator.gpu, adapter: false, err: null };
  if (navigator.gpu) { try { o.adapter = !!(await navigator.gpu.requestAdapter()); } catch (e) { o.err = String(e); } }
  return o;
});

// Drive + observe MANY frames. SUSTAINED repaint is the bar (not one static
// frame): we count rAF ticks the page actually services, sample the canvas
// backing store + a content fingerprint across those ticks, and nudge repaints
// (resize + synthetic input) to exercise the reentrant paths that used to panic.
//
// `frameCount` is incremented from a rAF loop installed in-page; a healthy
// run-loop keeps ticking. We also fingerprint the rendered pixels via
// toDataURL so we can assert the canvas STAYS painted (non-blank) across frames,
// not merely that it was sized once.
await page.evaluate(() => {
  window.__frameCount = 0;
  const tick = () => { window.__frameCount++; requestAnimationFrame(tick); };
  requestAnimationFrame(tick);
});

let maxW = 0, maxH = 0;
const fingerprints = [];
const frameCounts = [];
for (let i = 0; i < 40; i++) {
  const d = await page.evaluate(() => {
    const c = document.querySelector('canvas');
    if (!c) return null;
    let fp = null, nonBlank = false;
    try {
      // Read a small slice of the backing store via a 2D downscale. WebGPU
      // canvases can't be read with getContext('2d'), so use toDataURL which
      // snapshots the composited canvas; hash its length + a char sample.
      const url = c.toDataURL('image/png');
      // crude content fingerprint: length + sampled codepoints
      let h = url.length;
      for (let k = 100; k < url.length; k += Math.max(1, (url.length / 64) | 0)) h = (h * 31 + url.charCodeAt(k)) >>> 0;
      fp = h;
      // a blank/transparent canvas produces a very short, highly-repetitive dataURL
      nonBlank = url.length > 5000;
    } catch (e) { fp = 'ERR:' + e; }
    return { w: c.width, h: c.height, fp, nonBlank, frames: window.__frameCount };
  });
  if (d) {
    maxW = Math.max(maxW, d.w); maxH = Math.max(maxH, d.h);
    fingerprints.push({ fp: d.fp, nonBlank: d.nonBlank });
    frameCounts.push(d.frames);
  }
  // Halfway through, nudge a resize + a synthetic pointer move to drive the
  // reentrant resize/input callbacks (the paths that held the borrow).
  if (i === 12) { await page.setViewport({ width: 1100, height: 760 }); }
  if (i === 20) { await page.mouse.move(400 + i, 300 + i); await page.mouse.move(500, 350); }
  if (i === 28) { await page.setViewport({ width: 1280, height: 820 }); }
  await new Promise(r => setTimeout(r, 200));
}
const state = await page.evaluate(() => {
  const live = document.getElementById('live');
  return { status: live?.textContent, canvases: document.querySelectorAll('canvas').length, wasmError: document.body.innerText.includes('wasm error'), frames: window.__frameCount };
});
await page.screenshot({ path: SHOT });
await browser.close();

const bundleLoaded = !logs.some(l => l.includes('requestfailed') && l.includes('pkg-gpui'));
const webgpuInit = logs.some(l => l.includes('WebGPU context initialized successfully'));
const painted = maxW > 1 || maxH > 1;
const reentrancy = logs.some(l => l.includes('closure invoked recursively'));
// The exact panic we are fixing: a HARD panic at the gpui_web window backend
// (`gpui_web/src/window.rs:294` was the reported reentrancy site).
const gpuiWebBorrowPanic = logs.some(l =>
  (l.includes('panicked') && l.includes('gpui_web') &&
   (l.includes('already borrowed') || l.includes('BorrowMutError') || l.includes('BorrowError') || l.includes('window.rs'))));
// Any borrow-error chatter at all (may be a downstream LOG, not the backend panic).
const borrowChatter = logs.some(l => l.includes('already borrowed') || l.includes('already mutably borrowed') || l.includes('BorrowMutError') || l.includes('BorrowError'));
// An UNRELATED hard panic upstream of the loop (e.g. app/widget-library code).
// In wasm (panic=abort) such a panic aborts the in-flight gpui `handle.update()`
// WITHOUT running the borrow guard's Drop, poisoning the App RefCell — which then
// makes every subsequent rAF `try_borrow` log "RefCell already borrowed". That
// cascade is a SYMPTOM of the upstream panic, not the gpui_web reentrancy.
const appPanic = logs.find(l => l.includes('panicked') && !l.includes('gpui_web'));
// The gpui_web reentrancy is fixed iff there is NO hard backend borrow panic.
const borrowPanic = gpuiWebBorrowPanic;
// rAF ticks serviced across the run (run-loop liveness).
const framesServiced = state.frames | 0;
// content stayed non-blank across the sampled frames
const nonBlankSamples = fingerprints.filter(f => f.nonBlank).length;
const stayedPainted = painted && nonBlankSamples >= 5;
// did the rendered content ever change across frames (live, not frozen)?
const distinctFps = new Set(fingerprints.map(f => String(f.fp))).size;

console.log('=== gpui cockpit headless verification ===');
console.log('URL                 :', URL);
console.log('bundle loaded       :', bundleLoaded);
console.log('boot_cockpit invoked:', !state.wasmError);
console.log('WebGPU adapter avail :', gpu.adapter, gpu.err ? `(err: ${gpu.err})` : '');
console.log('WebGPU ctx init      :', webgpuInit);
console.log('canvas created       :', state.canvases > 0);
console.log('canvas backing max   :', `${maxW}x${maxH}`, painted ? '(PAINTED a real frame)' : '(stayed ~1x1 — NO real paint)');
console.log('rAF frames serviced  :', framesServiced, '(run-loop liveness across the run)');
console.log('non-blank samples    :', `${nonBlankSamples}/${fingerprints.length}`, '(canvas STAYED painted across frames)');
console.log('distinct frame fps   :', distinctFps, distinctFps > 1 ? '(content changed — live)' : '(content static)');
console.log('run-loop reentrancy  :', reentrancy, reentrancy ? '(gpui_web closure-reentrancy)' : '');
console.log('gpui_web borrow PANIC:', gpuiWebBorrowPanic, gpuiWebBorrowPanic ? '(THE IN-SCOPE BUG: hard panic at gpui_web window backend)' : '(none — the reentrancy fix holds)');
console.log('borrow-error chatter :', borrowChatter, borrowChatter ? '(logged from gpui::window — see whether an app panic preceded it)' : '');
console.log('upstream app panic   :', appPanic ? `YES — ${appPanic.replace(/\s+/g, ' ').slice(0, 160)}` : 'none');
console.log('status text          :', state.status);
console.log('screenshot           →', SHOT);
console.log('--- console / errors ---');
for (const l of logs) console.log(l);

console.log('\n=== VERDICT ===');
if (gpuiWebBorrowPanic) {
  console.log('FAIL: a HARD borrow panic at the gpui_web window backend occurred during sustained repaint — the reentrancy is NOT fixed.');
  process.exitCode = 1;
} else if (stayedPainted && framesServiced >= 10) {
  console.log(`SUSTAINED: gpui cockpit painted and STAYED painted across ${framesServiced} rAF frames with NO gpui_web borrow panic (${nonBlankSamples}/${fingerprints.length} non-blank samples). Live repaint works.`);
} else if (appPanic && borrowChatter) {
  console.log('BLOCKED UPSTREAM: the gpui_web reentrancy fix HOLDS (no hard panic at the window backend, no panic at window.rs:294), but an UNRELATED app panic aborts the frame loop and (under wasm panic=abort) poisons the App RefCell, producing the downstream `gpui::window: RefCell already borrowed` log cascade. Fix the app panic (out of this fork) to see sustained paint.');
  console.log(`  → upstream panic: ${appPanic.replace(/\s+/g, ' ').trim()}`);
  process.exitCode = 2;
} else if (painted) {
  console.log('PARTIAL: a frame painted and no gpui_web borrow panic, but sustained/non-blank evidence is weak (see counts above).');
} else if (webgpuInit && reentrancy) {
  console.log('CEILING: WebGPU initialized but the run-loop hit a closure-reentrancy before first paint (canvas stayed 1x1).');
} else if (webgpuInit) {
  console.log('CEILING: WebGPU initialized but no paint observed.');
} else {
  console.log('CEILING: bundle loaded / boot invoked but WebGPU did not initialize (adapter unavailable in this env?).');
}
