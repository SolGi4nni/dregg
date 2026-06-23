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

// Sample the canvas backing store over time: a real paint resizes it past 1x1.
let maxW = 0, maxH = 0;
for (let i = 0; i < 40; i++) {
  const d = await page.evaluate(() => { const c = document.querySelector('canvas'); return c ? { w: c.width, h: c.height } : null; });
  if (d) { maxW = Math.max(maxW, d.w); maxH = Math.max(maxH, d.h); }
  await new Promise(r => setTimeout(r, 200));
}
const state = await page.evaluate(() => {
  const live = document.getElementById('live');
  return { status: live?.textContent, canvases: document.querySelectorAll('canvas').length, wasmError: document.body.innerText.includes('wasm error') };
});
await page.screenshot({ path: SHOT });
await browser.close();

const bundleLoaded = !logs.some(l => l.includes('requestfailed') && l.includes('pkg-gpui'));
const webgpuInit = logs.some(l => l.includes('WebGPU context initialized successfully'));
const painted = maxW > 1 || maxH > 1;
const reentrancy = logs.some(l => l.includes('closure invoked recursively'));

console.log('=== gpui cockpit headless verification ===');
console.log('URL                 :', URL);
console.log('bundle loaded       :', bundleLoaded);
console.log('boot_cockpit invoked:', !state.wasmError);
console.log('WebGPU adapter avail :', gpu.adapter, gpu.err ? `(err: ${gpu.err})` : '');
console.log('WebGPU ctx init      :', webgpuInit);
console.log('canvas created       :', state.canvases > 0);
console.log('canvas backing max   :', `${maxW}x${maxH}`, painted ? '(PAINTED a real frame)' : '(stayed ~1x1 — NO real paint)');
console.log('run-loop reentrancy  :', reentrancy, reentrancy ? '(gpui_web closure-reentrancy before paint — the current ceiling)' : '');
console.log('status text          :', state.status);
console.log('screenshot           →', SHOT);
console.log('--- console / errors ---');
for (const l of logs) console.log(l);

console.log('\n=== VERDICT ===');
if (painted) console.log('RENDERS: the gpui cockpit painted a frame in-browser.');
else if (webgpuInit && reentrancy) console.log('CEILING: bundled + boot_cockpit invoked + WebGPU initialized, but the gpui_web run-loop hit a closure-reentrancy before first paint (canvas stayed 1x1).');
else if (webgpuInit) console.log('CEILING: WebGPU initialized but no paint observed (no reentrancy error captured).');
else console.log('CEILING: bundle loaded / boot invoked but WebGPU did not initialize (adapter unavailable in this env?).');
