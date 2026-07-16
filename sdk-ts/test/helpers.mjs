// Shared test helpers: load the repo's own dregg-wasm build as the
// differential ORACLE (the exact Rust dregg-turn/dregg-sdk code compiled to
// wasm), so the TS wire implementation drift-fails against the source of
// truth without running cargo.
//
// ⚠ ORACLE INTEGRITY (M30): the oracle MUST be the REAL, FRESHLY-BUILT wasm
// artifact — never a stale, hand-frozen snapshot. `wasm/pkg` is gitignored
// (`.gitignore` = `*`), so on a fresh clone it does NOT exist. The npm
// `pretest` hook rebuilds it (`npm run build:oracle` → `wasm-pack build`)
// before every `npm test`, so the compared bytes are always current source.
// A differential whose oracle is untracked and never rebuilt proves nothing:
// it silently blesses whatever the frozen binary happened to encode. This
// loader therefore FAILS LOUD when the oracle is absent rather than skipping.

import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

const ORACLE_MISSING =
  "dregg-wasm ORACLE MISSING — the wire differential cannot run without the " +
  "REAL, freshly-built wasm artifact. `wasm/pkg` is gitignored, so it must be " +
  "built: run `npm run build:oracle` (or `npm test`, whose `pretest` hook " +
  "builds it). Refusing to pass silently against an absent oracle (M30).";

let cached = null;

/** Load + initialize dregg-wasm (file-linked from ../wasm/pkg). */
export async function loadWasmOracle() {
  if (cached) return cached;
  let pkgDir;
  try {
    pkgDir = dirname(require.resolve("dregg-wasm/package.json"));
  } catch {
    throw new Error(ORACLE_MISSING);
  }
  const glue = join(pkgDir, "dregg_wasm.js");
  const bin = join(pkgDir, "dregg_wasm_bg.wasm");
  if (!existsSync(glue) || !existsSync(bin)) throw new Error(ORACLE_MISSING);
  const mod = await import(glue);
  mod.initSync({ module: readFileSync(bin) });
  cached = mod;
  return mod;
}

export const hex = (bytes) => Buffer.from(bytes).toString("hex");

export const fromHex = (s) => Uint8Array.from(Buffer.from(s, "hex"));

export const distDir = join(here, "..", "dist");

export const sdk = () => import(join(distDir, "index.mjs"));
export const raw = () => import(join(distDir, "raw.mjs"));
export const pg = () => import(join(distDir, "pg.mjs"));
