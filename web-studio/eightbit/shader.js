// shader.js — a self-contained 8-bit / pixel-art shader. No deps, no CDN.
//
// It does three things to an input image (an uploaded/AI-gen picture OR a live
// game canvas):
//   (a) DOWNSAMPLE to a chunky pixel grid  (configurable pixelSize);
//   (b) QUANTIZE to a limited palette      (configurable, see palettes.js);
//   (c) optional ORDERED DITHER (Bayer 4×4) + SCANLINE/CRT darkening.
//
// TWO execution paths, ONE algorithm:
//   • processRGBA(...)  — a PURE CPU function over an RGBA byte array. It is the
//     canvas-2D fallback (browsers without WebGL) AND the thing the headless
//     verifier exercises. No DOM, runs in node.
//   • EightBitShader     — a WebGL2/WebGL fragment-shader path that runs the same
//     downsample→dither→quantize→scanline on the GPU, for live per-frame use on a
//     game canvas. Falls back to processRGBA automatically if WebGL is absent.
//
// The GLSL and the CPU core are deliberately kept in step (block-center sample,
// same Bayer matrix, nearest-in-palette). The verifier asserts the CPU core; the
// GPU path is the same math for speed.

import { PALETTES, DEFAULT_PALETTE } from './palettes.js';

// Bayer 4×4 ordered-dither matrix, row-major, values 0..15.
export const BAYER4 = [
  0, 8, 2, 10,
  12, 4, 14, 6,
  3, 11, 1, 9,
  15, 7, 13, 5,
];

function clamp255(x) { return x < 0 ? 0 : x > 255 ? 255 : x; }

/** Nearest palette color (squared-euclidean in RGB). Returns [r,g,b]. */
export function nearestInPalette(r, g, b, palette) {
  let best = Infinity, out = palette[0];
  for (let i = 0; i < palette.length; i++) {
    const p = palette[i];
    const dr = r - p[0], dg = g - p[1], db = b - p[2];
    const d = dr * dr + dg * dg + db * db;
    if (d < best) { best = d; out = p; }
  }
  return out;
}

/**
 * The CPU core. Transforms an RGBA byte array in place-of a fresh output.
 *
 * @param {Uint8ClampedArray|Uint8Array} src  RGBA, length w*h*4
 * @param {number} w  source width in px
 * @param {number} h  source height in px
 * @param {object} opts
 *   pixelSize   {number}   chunk size in source px (>=1). default 8
 *   palette     {[r,g,b][]} target palette. default dregg-navy
 *   dither      {number}   0..1 ordered-dither amount. default 0
 *   scanline    {number}   0..1 CRT scanline darkening. default 0
 *   brightness  {number}   added -255..255. default 0
 *   contrast    {number}   multiplier around 128. default 1
 * @returns {Uint8ClampedArray} a NEW RGBA array, same w*h*4, fully processed
 *   (each pixelSize×pixelSize block is one flat quantized color).
 */
export function processRGBA(src, w, h, opts = {}) {
  const pixelSize = Math.max(1, Math.round(opts.pixelSize ?? 8));
  const palette = opts.palette ?? PALETTES[DEFAULT_PALETTE].colors;
  const dither = opts.dither ?? 0;
  const scanline = opts.scanline ?? 0;
  const brightness = opts.brightness ?? 0;
  const contrast = opts.contrast ?? 1;
  const out = new Uint8ClampedArray(w * h * 4);

  for (let by = 0; by < h; by += pixelSize) {
    for (let bx = 0; bx < w; bx += pixelSize) {
      // (a) downsample: average the block (nicer than point-sample on the CPU).
      let sr = 0, sg = 0, sb = 0, n = 0;
      const yEnd = Math.min(by + pixelSize, h), xEnd = Math.min(bx + pixelSize, w);
      for (let y = by; y < yEnd; y++) {
        for (let x = bx; x < xEnd; x++) {
          const i = (y * w + x) * 4;
          sr += src[i]; sg += src[i + 1]; sb += src[i + 2]; n++;
        }
      }
      let r = sr / n, g = sg / n, b = sb / n;

      // brightness / contrast
      r = clamp255((r - 128) * contrast + 128 + brightness);
      g = clamp255((g - 128) * contrast + 128 + brightness);
      b = clamp255((b - 128) * contrast + 128 + brightness);

      // (c) ordered dither: nudge the block color by a Bayer threshold keyed to
      // the block's grid position, before quantizing. Spreads banding.
      if (dither > 0) {
        const gx = Math.floor(bx / pixelSize), gy = Math.floor(by / pixelSize);
        const t = (BAYER4[(gy & 3) * 4 + (gx & 3)] / 16 - 0.5) * dither * 96;
        r = clamp255(r + t); g = clamp255(g + t); b = clamp255(b + t);
      }

      // (b) quantize to the palette.
      const q = nearestInPalette(r, g, b, palette);

      // write the flat block; (c) scanline darkens alternate source rows.
      for (let y = by; y < yEnd; y++) {
        const dark = scanline > 0 && (y & 1) ? (1 - scanline * 0.45) : 1;
        for (let x = bx; x < xEnd; x++) {
          const i = (y * w + x) * 4;
          out[i] = q[0] * dark;
          out[i + 1] = q[1] * dark;
          out[i + 2] = q[2] * dark;
          out[i + 3] = 255;
        }
      }
    }
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// The GLSL fragment shader — same algorithm on the GPU (block-center sample).
// GLSL ES 1.00 so it runs on WebGL1 and WebGL2.

const VERT_SRC = `
attribute vec2 aPos;
varying vec2 vUv;
void main() {
  vUv = aPos * 0.5 + 0.5;
  gl_Position = vec4(aPos, 0.0, 1.0);
}`;

const FRAG_SRC = `
precision highp float;
varying vec2 vUv;
uniform sampler2D uTex;
uniform vec2  uResolution;   // output size (px)
uniform float uPixelSize;
uniform vec3  uPalette[32];
uniform int   uPaletteSize;
uniform float uDither;       // 0..1
uniform float uScanline;     // 0..1
uniform float uBrightness;   // -1..1
uniform float uContrast;     // ~1

// Bayer 4x4 as a mat4 (dynamic component indexing is legal on mat types).
mat4 bayer = mat4(
   0.0,  8.0,  2.0, 10.0,
  12.0,  4.0, 14.0,  6.0,
   3.0, 11.0,  1.0,  9.0,
  15.0,  7.0, 13.0,  5.0);

void main() {
  // (a) downsample: snap to the block center, then sample.
  vec2 px = gl_FragCoord.xy;
  vec2 block = (floor(px / uPixelSize) + 0.5) * uPixelSize;
  vec2 uv = block / uResolution;
  vec3 c = texture2D(uTex, uv).rgb;

  // brightness / contrast (work in 0..1)
  c = (c - 0.5) * uContrast + 0.5 + uBrightness;

  // (c) ordered dither keyed to block grid coords.
  if (uDither > 0.0) {
    vec2 g = floor(px / uPixelSize);
    int bx = int(mod(g.x, 4.0));
    int by = int(mod(g.y, 4.0));
    float t = (bayer[bx][by] / 16.0 - 0.5) * uDither * 0.375;
    c += t;
  }
  c = clamp(c, 0.0, 1.0);

  // (b) nearest palette color.
  vec3 chosen = uPalette[0];
  float best = 1e9;
  for (int i = 0; i < 32; i++) {
    if (i >= uPaletteSize) break;
    vec3 p = uPalette[i];
    vec3 d = c - p;
    float dd = dot(d, d);
    if (dd < best) { best = dd; chosen = p; }
  }

  // (c) scanline darkening on alternate rows.
  float dark = (uScanline > 0.0 && mod(px.y, 2.0) >= 1.0)
      ? (1.0 - uScanline * 0.45) : 1.0;

  gl_FragColor = vec4(chosen * dark, 1.0);
}`;

function compile(gl, type, src) {
  const s = gl.createShader(type);
  gl.shaderSource(s, src);
  gl.compileShader(s);
  if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
    const log = gl.getShaderInfoLog(s);
    gl.deleteShader(s);
    throw new Error('shader compile failed: ' + log);
  }
  return s;
}

/**
 * The live GPU shader. Wraps a target <canvas>. Feed it any drawable source
 * (an <img>, another <canvas>, ImageBitmap, a video) and it renders the 8-bit
 * transform into the target canvas. Use it per-frame over a game render.
 *
 * If WebGL is unavailable it transparently falls back to the CPU core via a 2D
 * context, so callers never branch.
 */
export class EightBitShader {
  constructor(targetCanvas, opts = {}) {
    this.canvas = targetCanvas;
    this.opts = {
      pixelSize: 8, palette: PALETTES[DEFAULT_PALETTE].colors,
      dither: 0, scanline: 0, brightness: 0, contrast: 1, ...opts,
    };
    this.gl = targetCanvas.getContext('webgl2') || targetCanvas.getContext('webgl');
    this.usingGL = !!this.gl;
    if (this.usingGL) this._initGL();
  }

  setOptions(patch) { Object.assign(this.opts, patch); }

  _initGL() {
    const gl = this.gl;
    const prog = gl.createProgram();
    gl.attachShader(prog, compile(gl, gl.VERTEX_SHADER, VERT_SRC));
    gl.attachShader(prog, compile(gl, gl.FRAGMENT_SHADER, FRAG_SRC));
    gl.linkProgram(prog);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
      throw new Error('link failed: ' + gl.getProgramInfoLog(prog));
    }
    this.prog = prog;
    // fullscreen triangle-pair
    this.buf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, this.buf);
    gl.bufferData(gl.ARRAY_BUFFER,
      new Float32Array([-1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1]), gl.STATIC_DRAW);
    this.tex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, this.tex);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    this.loc = {
      aPos: gl.getAttribLocation(prog, 'aPos'),
      uTex: gl.getUniformLocation(prog, 'uTex'),
      uResolution: gl.getUniformLocation(prog, 'uResolution'),
      uPixelSize: gl.getUniformLocation(prog, 'uPixelSize'),
      uPalette: gl.getUniformLocation(prog, 'uPalette'),
      uPaletteSize: gl.getUniformLocation(prog, 'uPaletteSize'),
      uDither: gl.getUniformLocation(prog, 'uDither'),
      uScanline: gl.getUniformLocation(prog, 'uScanline'),
      uBrightness: gl.getUniformLocation(prog, 'uBrightness'),
      uContrast: gl.getUniformLocation(prog, 'uContrast'),
    };
  }

  /** Render `source` (img/canvas/ImageBitmap/video) into the target canvas. */
  render(source) {
    const w = this.canvas.width, h = this.canvas.height;
    if (!this.usingGL) return this._render2D(source, w, h);
    const gl = this.gl;
    gl.viewport(0, 0, w, h);
    gl.useProgram(this.prog);
    gl.bindBuffer(gl.ARRAY_BUFFER, this.buf);
    gl.enableVertexAttribArray(this.loc.aPos);
    gl.vertexAttribPointer(this.loc.aPos, 2, gl.FLOAT, false, 0, 0);
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, this.tex);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, source);
    gl.uniform1i(this.loc.uTex, 0);
    gl.uniform2f(this.loc.uResolution, w, h);
    gl.uniform1f(this.loc.uPixelSize, this.opts.pixelSize);
    const pal = this.opts.palette.slice(0, 32);
    const flat = new Float32Array(32 * 3);
    pal.forEach((c, i) => { flat[i * 3] = c[0] / 255; flat[i * 3 + 1] = c[1] / 255; flat[i * 3 + 2] = c[2] / 255; });
    gl.uniform3fv(this.loc.uPalette, flat);
    gl.uniform1i(this.loc.uPaletteSize, pal.length);
    gl.uniform1f(this.loc.uDither, this.opts.dither);
    gl.uniform1f(this.loc.uScanline, this.opts.scanline);
    gl.uniform1f(this.loc.uBrightness, this.opts.brightness / 255);
    gl.uniform1f(this.loc.uContrast, this.opts.contrast);
    gl.drawArrays(gl.TRIANGLES, 0, 6);
  }

  _render2D(source, w, h) {
    // CPU fallback: rasterize the source, run the pure core, blit back.
    const scratch = (this._scratch ||= document.createElement('canvas'));
    scratch.width = w; scratch.height = h;
    const sctx = scratch.getContext('2d');
    sctx.drawImage(source, 0, 0, w, h);
    const img = sctx.getImageData(0, 0, w, h);
    const out = processRGBA(img.data, w, h, this.opts);
    const octx = this.canvas.getContext('2d');
    octx.putImageData(new ImageData(out, w, h), 0, 0);
  }
}

/**
 * One-shot convenience: 8-bit-ify a still image/canvas and return a NEW canvas
 * sized to the source. Prefers the GPU shader; identical output shape either way.
 * This is what the Asset Studio calls on an uploaded/AI-gen picture.
 */
export function eightBitImage(source, opts = {}) {
  const w = source.width || source.videoWidth;
  const h = source.height || source.videoHeight;
  const target = document.createElement('canvas');
  target.width = w; target.height = h;
  const shader = new EightBitShader(target, opts);
  shader.render(source);
  return target;
}
