import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { test } from "node:test";

/**
 * The defect this exists to catch, because it dammed the whole client:
 *
 *   app.js imported `createSignalRun` and `submitSignalGuess` from
 *   signal-runtime.js. The Signal client had been rewritten for the
 *   hidden-instance split and neither name existed any more. Nothing in the
 *   suite imported app.js, `node --check` parses a module without resolving its
 *   imports, and the browser was the first thing to find out — by failing to
 *   link the entry point, so the terminal rendered nothing at all.
 *
 * A named import of a missing export is a LINK-time error, not a runtime one, so
 * no amount of coverage of the leaves catches it.
 */

const src = new URL("../src/", import.meta.url);
const IMPORT = /import\s+(?:([\w$]+)\s*,\s*)?(?:\{([^}]*)\}|\*\s+as\s+[\w$]+|([\w$]+))\s+from\s+["']([^"']+)["']/g;

function importedNames(source) {
  const found = [];
  for (const match of source.matchAll(IMPORT)) {
    const [, defaultWithBrace, braced, bareDefault, specifier] = match;
    if (!specifier.startsWith(".")) continue;
    if (defaultWithBrace || bareDefault) found.push({ specifier, name: "default" });
    for (const entry of (braced ?? "").split(",")) {
      const name = entry.trim().split(/\s+as\s+/)[0].trim();
      if (name) found.push({ specifier, name });
    }
  }
  return found;
}

/** Every name a module imports that its target does not export. */
async function missingImports(file, source) {
  const missing = [];
  for (const { specifier, name } of importedNames(source)) {
    const target = new URL(specifier, new URL(file, src)).href;
    const available = new Set(Object.keys(await import(target)));
    if (!available.has(name)) missing.push(`${file} imports { ${name} } from "${specifier}", which does not export it`);
  }
  return missing;
}

test("every relative named import in src/ resolves to a real export", async () => {
  const files = (await readdir(src)).filter((file) => file.endsWith(".js"));
  assert.ok(files.length > 10, "the source tree should not be empty");
  const missing = (await Promise.all(files.map(async (file) => missingImports(file, await readFile(new URL(file, src), "utf8"))))).flat();
  assert.deepEqual(missing, []);
});

test("the import checker actually fails when an import goes missing", async () => {
  // ⚠ A falsifier that stops falsifying is worse than none, so this runs the
  // REAL checker over the REAL defect rather than asserting its parts: app.js
  // source with the pre-split name put back, checked against the live module.
  const source = await readFile(new URL("app.js", src), "utf8");
  const broken = source.replace("createPracticeRun,", "createSignalRun,");
  assert.notEqual(broken, source, "the mutation must actually change app.js source; if the import moved, update this, do not delete it");

  const missing = await missingImports("app.js", broken);
  assert.deepEqual(missing, [
    'app.js imports { createSignalRun } from "./signal-runtime.js", which does not export it',
  ]);
  // …and the unmutated source is clean, so the checker is not simply always red.
  assert.deepEqual(await missingImports("app.js", source), []);
});
