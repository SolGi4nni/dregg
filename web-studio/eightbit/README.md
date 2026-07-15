# 8-bit shader — dregg web studio

A self-contained pixel-art shader for the dregg web surfaces. It takes any image —
an **uploaded / AI-generated picture** or a **live game canvas** — and:

1. **downsamples** it to a chunky pixel grid (configurable `pixelSize`),
2. **quantizes** it to a limited retro palette (configurable — see `palettes.js`),
3. optionally applies **ordered dither** (Bayer 4×4) and **scanline/CRT** darkening.

No build step, no dependencies, no CDN — one ES module you import directly. This is
the seed tool of the web content-creation/demoing suite designed in
[`docs/deos/WEB-CONTENT-TOOLING.md`](../../docs/deos/WEB-CONTENT-TOOLING.md).

## Files

| file | what |
|------|------|
| `shader.js`   | the shader. `processRGBA` (pure CPU core), `EightBitShader` (WebGL class, CPU fallback), `eightBitImage` (one-shot). |
| `palettes.js` | the palette registry (Game Boy, CGA, PICO-8, 1-bit, **dregg-navy**, **dregg-dark**). |
| `index.html`  | a live demo: drop an image → see it 8-bit-ified; pixel-size + palette + dither + scanline controls; a live game-canvas demo; PNG export. |
| `verify.mjs`  | a **headless** proof the transform is real (no browser). |

## Two paths, one algorithm

- **`processRGBA(src, w, h, opts)`** is a pure function over an RGBA byte array. It is
  the canvas-2D fallback for browsers without WebGL *and* the thing the verifier
  exercises. It runs in node.
- **`EightBitShader`** runs the same downsample → dither → quantize → scanline as a
  WebGL/WebGL2 fragment shader (GLSL ES 1.00, so it works on both), for per-frame use
  over a live game render. It falls back to `processRGBA` automatically when WebGL is
  absent — callers never branch.

The GLSL samples the block center; the CPU core averages the block (nicer stills).
Both produce flat, palette-quantized blocks — the verifier asserts those invariants.

## Use it

```js
import { eightBitImage } from './shader.js';
import { PALETTES } from './palettes.js';

// still image / AI-gen asset → a new 8-bit canvas
const out = eightBitImage(myImageOrCanvas, {
  pixelSize: 6,
  palette: PALETTES['dregg-navy'].colors,
  dither: 1.0,
});
document.body.appendChild(out);
```

```js
import { EightBitShader } from './shader.js';
// live over a game canvas — call render() each frame
const shader = new EightBitShader(outCanvas, { pixelSize: 8 });
function frame() { shader.render(gameCanvas); requestAnimationFrame(frame); }
```

Open `index.html` over any static server to play with it (it fetches nothing).

## Verify (headless)

```
node web-studio/eightbit/verify.mjs
```

Runs the shader on two synthetic inputs (a gradient "uploaded image" and a
procedural "game canvas") and asserts, for each: **pixelation** (every block is one
flat color), **quantization** (every output color ∈ the palette), and **transform**
(output ≠ input). It writes before/after `.ppm` files to `verify-out/` (gitignored).

## Composition

- **Asset pathway** (`docs/CONTRIBUTING-ASSETS.md`): the AI-art prep steps
  (generate → remove background → crop → export 128) become an in-browser step — the
  shader is the *normalize* stage that makes arbitrary art land on the board's palette
  and pixel grid. Export is 128×128 (the engine's native `CANVAS = 128`).
- **Sprite layer** (`dreggnet-sprite`): procedural sprites are already deterministic
  SVG; this shader gives the *hand/AI-art* slot (`art:<pack>/<name>`, designed in
  CONTRIBUTING-ASSETS) a normalizer so uploaded art matches the generated substrate.
- **Launchpad** (`docs/deos/DREGG-LAUNCHPAD-DESIGN.md`): the same shader is the token
  logo / microsite imagery normalizer — a verified-provenance answer to AI-logo-gen.
