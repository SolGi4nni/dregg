// verify.mjs — headless proof the 8-bit shader actually transforms an input.
// No browser, no deps: it exercises the PURE CPU core (processRGBA), which is
// the same algorithm the GPU path runs and the canvas-2D fallback uses.
//
// It runs the shader on TWO synthetic inputs — mirroring the shader's two real
// sources — and ASSERTS the transform is genuine, not a passthrough:
//   INPUT A = an "uploaded / AI-gen image": a smooth 24-bit RGB gradient.
//   INPUT B = a "live game canvas": a procedural checkerboard + diagonal ramp.
// For each it checks: (1) PIXELATION — every pixelSize×pixelSize block is one
// flat color; (2) QUANTIZATION — every output color is a member of the target
// palette; (3) TRANSFORM — output differs from input. It also writes .ppm files
// so a human can eyeball the before/after.
//
// Run: node web-studio/eightbit/verify.mjs

import { writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { processRGBA } from './shader.js';
import { PALETTES } from './palettes.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const OUT = path.join(HERE, 'verify-out');
import { mkdirSync } from 'node:fs';
mkdirSync(OUT, { recursive: true });

// ── synthetic inputs (RGBA byte arrays) ──
function gradient(w, h) {
  const a = new Uint8ClampedArray(w * h * 4);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = (y * w + x) * 4;
    a[i] = (x / w) * 255; a[i + 1] = (y / h) * 255; a[i + 2] = 200 - (x / w) * 160; a[i + 3] = 255;
  }
  return a;
}
function gameCanvas(w, h) {
  // A stand-in for a live game render: checkerboard tiles + a diagonal ramp,
  // as the CoordGrid board might rasterize.
  const a = new Uint8ClampedArray(w * h * 4);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = (y * w + x) * 4;
    const check = ((x >> 3) + (y >> 3)) & 1;
    const ramp = ((x + y) / (w + h)) * 255;
    a[i] = check ? ramp : 20;
    a[i + 1] = check ? 200 - ramp * 0.5 : 40;
    a[i + 2] = check ? 255 - ramp : 80;
    a[i + 3] = 255;
  }
  return a;
}

// ── write a P6 PPM (RGB), dep-free + viewable ──
function writePPM(name, rgba, w, h) {
  const rgb = Buffer.alloc(w * h * 3);
  for (let p = 0; p < w * h; p++) { rgb[p * 3] = rgba[p * 4]; rgb[p * 3 + 1] = rgba[p * 4 + 1]; rgb[p * 3 + 2] = rgba[p * 4 + 2]; }
  const header = Buffer.from(`P6\n${w} ${h}\n255\n`, 'ascii');
  writeFileSync(path.join(OUT, name), Buffer.concat([header, rgb]));
}

// ── assertions ──
let failures = 0;
function check(cond, msg) {
  if (cond) { console.log('  PASS  ' + msg); }
  else { console.log('  FAIL  ' + msg); failures++; }
}

function paletteSet(pal) { return new Set(pal.map(c => `${c[0]},${c[1]},${c[2]}`)); }

function assertPixelated(out, w, h, pixelSize, label) {
  // Every full block must be internally constant (ignoring scanline rows: we run
  // these cases with scanline=0, so blocks are strictly flat).
  for (let by = 0; by + pixelSize <= h; by += pixelSize) {
    for (let bx = 0; bx + pixelSize <= w; bx += pixelSize) {
      const i0 = (by * w + bx) * 4;
      const r = out[i0], g = out[i0 + 1], b = out[i0 + 2];
      for (let y = by; y < by + pixelSize; y++) for (let x = bx; x < bx + pixelSize; x++) {
        const i = (y * w + x) * 4;
        if (out[i] !== r || out[i + 1] !== g || out[i + 2] !== b) {
          check(false, `${label}: block (${bx},${by}) not flat`); return;
        }
      }
    }
  }
  check(true, `${label}: every ${pixelSize}×${pixelSize} block is one flat color (pixelation real)`);
}

function assertQuantized(out, w, h, pal, label) {
  const set = paletteSet(pal);
  const seen = new Set();
  for (let p = 0; p < w * h; p++) {
    const key = `${out[p * 4]},${out[p * 4 + 1]},${out[p * 4 + 2]}`;
    seen.add(key);
    if (!set.has(key)) { check(false, `${label}: color ${key} NOT in palette`); return; }
  }
  check(true, `${label}: all ${seen.size} distinct output colors ∈ palette of ${pal.length} (quantization real)`);
}

function assertTransformed(src, out, label) {
  let diff = 0;
  for (let i = 0; i < src.length; i += 4) if (src[i] !== out[i] || src[i + 1] !== out[i + 1] || src[i + 2] !== out[i + 2]) diff++;
  const pct = (100 * diff / (src.length / 4)).toFixed(1);
  check(diff > 0, `${label}: output differs from input at ${pct}% of pixels (not a passthrough)`);
}

// ── run the cases ──
function run(label, src, w, h, opts, file) {
  console.log(`\n[${label}]  ${w}×${h}  pixelSize=${opts.pixelSize}  palette=${opts.paletteName}  dither=${opts.dither ?? 0}`);
  const out = processRGBA(src, w, h, opts);
  assertPixelated(out, w, h, opts.pixelSize, label);
  assertQuantized(out, w, h, opts.palette, label);
  assertTransformed(src, out, label);
  writePPM(file + '.in.ppm', src, w, h);
  writePPM(file + '.out.ppm', out, w, h);
  console.log(`  wrote verify-out/${file}.in.ppm and .out.ppm`);
}

const W = 128, H = 128;

// INPUT A — uploaded/AI-gen image → Game Boy 4-color, no dither.
run('uploaded-image', gradient(W, H), W, H,
  { pixelSize: 8, palette: PALETTES.gameboy.colors, paletteName: 'gameboy', dither: 0, scanline: 0 },
  'A-uploaded');

// INPUT A' — same image, dregg-navy 12-color + dither (asset-studio default).
run('uploaded-dither', gradient(W, H), W, H,
  { pixelSize: 6, palette: PALETTES['dregg-navy'].colors, paletteName: 'dregg-navy', dither: 1, scanline: 0 },
  'A2-uploaded-dither');

// INPUT B — live game canvas → dregg-dark theme, chunky.
run('game-canvas', gameCanvas(W, H), W, H,
  { pixelSize: 8, palette: PALETTES['dregg-dark'].colors, paletteName: 'dregg-dark', dither: 0, scanline: 0 },
  'B-game-canvas');

console.log(`\n${failures === 0 ? 'ALL CHECKS PASSED ✓' : failures + ' CHECK(S) FAILED ✗'}`);
process.exit(failures === 0 ? 0 : 1);
